import Lean

open Lean

namespace CEnter

inductive Path where
  | node : Path
  | arg (arg : Nat) (all : Bool) (next : Path) : Path
  | proj (next : Path) : Path
  | fun (depth : Nat) (next : Path) : Path
  | type (next : Path) : Path
  | body (next : Path) : Path
  | value (next : Path) : Path
deriving Inhabited, DecidableEq

def Path.toSubExprPos (expr : Expr) (path : Path) : MetaM SubExpr.Pos := do
  go expr path .root
where
  go (expr : Expr) (path : Path) (acc : SubExpr.Pos) : MetaM SubExpr.Pos :=
    match path with
    | .node => pure acc
    | .type next =>
      match expr.consumeMData with
      | .letE _ t _ _ _ => go t next acc.pushLetVarType
      | .lam _ t _ _
      | .forallE _ t _ _ => go t next acc.pushBindingDomain
      | _ => throwError m!"invalid binding domain access on{indentExpr expr}"
    -- we don't need to add instances here, since there is no instance synthesis happening
    | .body next =>
      match expr.consumeMData with
      | .letE n t v b nonDep => do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLetDecl fvarId n t v nonDep
        withReader (fun ctx => {ctx with lctx})
          (go (b.instantiate1 (.fvar fvarId)) next acc.pushLetBody)
      | .lam n t b bi
      | .forallE n t b bi => do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t bi
        withReader (fun ctx => {ctx with lctx})
          (go (b.instantiate1 (.fvar fvarId)) next acc.pushBindingBody)
      | _ => throwError m!"invalid binding body access on{indentExpr expr}"
    | .value next =>
      match expr.consumeMData with
      | .letE _ _ v _  _ => go v next acc.pushLetValue
      | _ => throwError m!"invalid let value access on{indentExpr expr}"
    | .proj next =>
      match expr.consumeMData with
      | .proj _ _ e => go e next acc.pushProj
      | _ => throwError m!"invalid proj access on{indentExpr expr}"
    | .fun n next =>
      if expr.consumeMData.getAppNumArgs < n then
        throwError m!"invalid fun access on{indentExpr expr}"
      else go (expr.consumeMData.getBoundedAppFn n) next (acc.pushNaryFn n)
    | arg 0 _ next =>
      go expr.consumeMData.getAppFn next (acc.pushNaryFn expr.consumeMData.getAppNumArgs)
    | arg (n + 1) true next => do
      if expr.consumeMData.getAppNumArgs < n + 1 then
        throwError m!"invalid arg @{n + 1} access on{indentExpr expr}"
      let c ← getIdxAll expr.consumeMData (n + 1) (expr.consumeMData.getAppNumArgs - (n + 1))
      go c next (acc.pushNaryArg expr.consumeMData.getAppNumArgs n)
    | arg (n + 1) false next =>
      expr.consumeMData.withApp fun f args => do
        let err :=
          throwError m!"invalid arg {n + 1} access on{indentExpr expr}"
        let kinds ← PrettyPrinter.Delaborator.getParamKinds f args
        if let Except.error i := kinds.foldlM
          (fun (v, i) k =>
            if let .default := k.bInfo then
              if v = n then throw i else pure (v + 1, i + 1)
            else pure (v, i + 1)) (0, 0) then
          if let some c := args[i]? then
            go c next (acc.pushNaryArg expr.consumeMData.getAppNumArgs i)
          else err
        else err
  getIdxAll (e : Expr) (n k : Nat) : MetaM Expr :=
    match e, k with
    | .app _ a, 0 => pure a
    | .app f _, k + 1 => getIdxAll f n k
    | _, _ => throwError m!"invalid arg @{n} access on{indentExpr expr}"

partial def Path.ofSubExprPos (expr : Expr) (pos : SubExpr.Pos) : MetaM Path :=
  go expr pos.toArray 0
where
  go (expr : Expr) (pos : Array Nat) (i : Fin (pos.size + 1)) : MetaM Path :=
    if h : i = Fin.last pos.size then pure .node else
    let i := i.castLT (Fin.val_lt_last h)
    if pos[i] = SubExpr.Pos.typeCoord then
      throwError m!"cannot enter type of expression{indentExpr expr}" else
    let err :=
      throwError m!"cannot access position {pos[i]} of{indentExpr expr}"
    match expr with
    | .bvar i => throwError m!"unexpected bound variable #{i}"
    | .fvar _
    | .mvar _
    | .lit _
    | .const _ _
    | .sort _ => err
    | .proj _ _ e =>
      if pos[i] = 0 then Path.proj <$> go e pos i.succ else err
    | .mdata _ e => go e pos i.castSucc
    | .letE n t v b nonDep =>
      if pos[i] = 0 then Path.type <$> go t pos i.succ else
      if pos[i] = 1 then Path.value <$> go v pos i.succ else
      if pos[i] = 2 then do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLetDecl fvarId n t v nonDep
        withReader (fun ctx => {ctx with lctx})
          (Path.body <$> go (b.instantiate1 (.fvar fvarId)) pos i.succ) else
      err
    | .forallE n t b bi
    | .lam n t b bi =>
      if pos[i] = 0 then Path.type <$> go t pos i.succ else
      if pos[i] = 1 then do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t bi
        withReader (fun ctx => {ctx with lctx})
          (Path.body <$> go (b.instantiate1 (.fvar fvarId)) pos i.succ) else
      err
    | .app .. => appT expr pos i.castSucc [] none
  appT (e : Expr) (p : Array Nat) (i : Fin (p.size + 1))
      (acc : List Expr) (n : Option (Fin acc.length)) : MetaM Path :=
    match e with
    | .app f a =>
      if let some u := n then appT f p i (a :: acc) (some u.succ)
      else if h : i = Fin.last p.size then pure (Path.fun acc.length .node)
      else let i := i.castLT (Fin.val_lt_last h)
      if p[i] = 0 then appT f p i.succ (a :: acc) none
      else if p[i] = 1 then appT f p i.succ (a :: acc) (some ⟨0, acc.length.zero_lt_succ⟩)
      else throwError m!"cannot access position {p[i]} of{indentExpr e}"
    | _ =>
      if let some u := n then do
        let c ← PrettyPrinter.Delaborator.getParamKinds e acc.toArray
        if let some {bInfo := .default, ..} := c[u]? then
          arg (((c.map (·.bInfo)).take u).count .default + 1)
            false <$> go acc[u] p i
        else arg (u + 1) true <$> go acc[u] p i
      else arg 0 false <$> go e p i

declare_syntax_cat cLoc

syntax (name := cNode) "." : cLoc
syntax (name := cProj) "-" cLoc : cLoc
syntax (name := cFun) num "," cLoc : cLoc
syntax (name := cType) "<" cLoc : cLoc
syntax (name := cBody) ">" cLoc : cLoc
syntax (name := cValue) "/" cLoc : cLoc
syntax (name := cArg) "@"? num ";" cLoc : cLoc

partial def parseCLoc (stx : TSyntax `cLoc) : Option Path :=
  match stx with
  | `(cLoc| .) => some Path.node
  | `(cLoc| -$loc) => (parseCLoc loc).map Path.proj
  | `(cLoc| $n:num,$loc) => (parseCLoc loc).map (Path.fun n.getNat)
  | `(cLoc| <$loc) => (parseCLoc loc).map Path.type
  | `(cLoc| >$loc) => (parseCLoc loc).map Path.body
  | `(cLoc| /$loc) => (parseCLoc loc).map Path.value
  | `(cLoc| @$n;$loc) => (parseCLoc loc).map (Path.arg n.getNat true)
  | `(cLoc| $n:num;$loc) => (parseCLoc loc).map (Path.arg n.getNat false)
  | _ => none

def reprPath (path : Path) : TSyntax `cLoc := Unhygienic.run do
  match path with
  | .node => `(cLoc| .)
  | .proj next => `(cLoc| -$(reprPath next))
  | .fun n next => `(cLoc| $(Syntax.mkNatLit n):num,$(reprPath next))
  | .type next => `(cLoc| <$(reprPath next))
  | .body next => `(cLoc| >$(reprPath next))
  | .value next => `(cLoc| /$(reprPath next))
  | .arg n true next => `(cLoc| @$(Syntax.mkNatLit n);$(reprPath next))
  | .arg n false next => `(cLoc| $(Syntax.mkNatLit n):num;$(reprPath next))

instance : Quote Path `cLoc where
  quote := reprPath

def formatPath (path : Path) : String :=
  match path with
  | .node => s!"."
  | .proj next => s!"-{formatPath next}"
  | .fun n next => s!"{n},{formatPath next}"
  | .type next => s!"<{formatPath next}"
  | .body next => s!">{formatPath next}"
  | .value next => s!"/{formatPath next}"
  | .arg n true next => s!"@{n};{formatPath next}"
  | .arg n false next => s!"{n};{formatPath next}"

instance : ToString Path where
  toString := formatPath

instance : Repr Path where
  reprPrec path _ := .text (formatPath path)

end CEnter

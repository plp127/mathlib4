import Lean

open Lean

namespace Mathlib.Tactic.Widget.Rewrite

inductive Path where
  | node : Path
  | app (arg : Nat) (all : Bool) (next : Path) : Path
  | proj (next : Path) : Path
  | fun (next : Path) : Path
  | type (next : Path) : Path
  | body (next : Path) : Path
  | value (next : Path) : Path

def Path.toSubExprPos (expr : Expr) (path : Path) : MetaM SubExpr.Pos := do
  go expr path .root
where
  go (expr : Expr) (path : Path) (acc : SubExpr.Pos) : MetaM SubExpr.Pos :=
    match path with
    | .node => return acc
    | .type next =>
      match expr.consumeMData with
      | .letE _ t _ _ _ => go t next acc.pushLetVarType
      | .lam _ t _ _
      | .forallE _ t _ _ => go t next acc.pushBindingDomain
      | _ => throwError m!"invalid binding domain access on{indentExpr expr}"
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
    | .fun next =>
      match expr.consumeMData with
      | .app f _ => go f next acc.pushAppFn
      | _ => throwError m!"invalid fun access on{indentExpr expr}"
    | .app 0 _ next => go expr.getAppFn next (acc.pushNaryFn expr.getAppNumArgs)
    | .app (n + 1) true next => do
      let c ← getIdxAll expr.consumeMData (n + 1) (expr.getAppNumArgs - n - 1)
      go c next (acc.pushNaryArg expr.getAppNumArgs n)
    | .app (n + 1) false next =>
      expr.consumeMData.withApp fun f args => do
        let err :=
          throwError m!"invalid arg {n} access on{indentExpr expr}"
        let kinds ← PrettyPrinter.Delaborator.getParamKinds f args
        if let Except.error i := kinds.foldlM
          (fun (v, i) k =>
            if let .default := k.bInfo then
              if v = n then throw i else pure (v + 1, i + 1)
            else pure (v, i + 1)) (0, 0) then
          if let some c := args[i]? then
            go c next (acc.pushNaryArg expr.getAppNumArgs i)
          else err
        else err
  getIdxAll (e : Expr) (n k : Nat) : MetaM Expr :=
    match e, k with
    | .app _ a, 0 => pure a
    | .app f _, k + 1 => getIdxAll f n k
    | _, _ => throwError m!"invalid arg @{n} access on{indentExpr expr}"

partial def Path.ofSubExprPos (expr : Expr) (pos : SubExpr.Pos) : MetaM Path :=
  let err :=
    throwError m!"cannot access position {pos.head} of{indentExpr expr}"
  if pos.isRoot then pure .node else
  match expr with
  | .bvar i => throwError m!"unexpected bound variable #{i}"
  | .fvar _
  | .mvar _
  | .lit _
  | .const _ _
  | .sort _ => err
  | .proj _ _ e =>
    if pos.head = 0 then Path.proj <$> Path.ofSubExprPos e pos.tail else err
  | .mdata _ e => Path.ofSubExprPos e pos
  | .letE n t v b nonDep =>
    if pos.head = 0 then Path.type <$> Path.ofSubExprPos t pos.tail else
    if pos.head = 1 then Path.value <$> Path.ofSubExprPos v pos.tail else
    if pos.head = 2 then Path.body <$> do
      let lctx ← getLCtx
      let fvarId ← mkFreshFVarId
      let lctx := lctx.mkLetDecl fvarId n t v nonDep
      withReader (fun ctx => {ctx with lctx})
        (Path.ofSubExprPos (b.instantiate1 (.fvar fvarId)) pos.tail) else
    err
  | .forallE n t b bi
  | .lam n t b bi =>
    if pos.head = 0 then Path.type <$> Path.ofSubExprPos t pos.tail else
    if pos.head = 1 then Path.body <$> do
      let lctx ← getLCtx
      let fvarId ← mkFreshFVarId
      let lctx := lctx.mkLocalDecl fvarId n t bi
      withReader (fun ctx => {ctx with lctx})
        (Path.ofSubExprPos (b.instantiate1 (.fvar fvarId)) pos.tail) else
    err
  | .app .. => appT expr pos [] none
where
  appT (e : Expr) (p : SubExpr.Pos) (acc : List Expr) (n : Option (Fin acc.length)) : MetaM Path :=
    match e with
    | .app f a =>
      if let some u := n then appT f p (a :: acc) (some u.succ)
      else if p.isRoot then pure (Nat.repeat Path.fun acc.length .node)
      else if p.head = 0 then appT f p.tail (a :: acc) none
      else if p.head = 1 then appT f p.tail (a :: acc) (some ⟨0, acc.length.zero_lt_succ⟩)
      else throwError m!"cannot access position {p.head} of{indentExpr e}"
    | _ =>
      if let some u := n then do
        let c ← PrettyPrinter.Delaborator.getParamKinds e acc.toArray
        if let some {bInfo := .default, ..} := c[u]? then
          Path.app (((c.map (·.bInfo)).take u).count .default + 1)
            false <$> Path.ofSubExprPos acc[u] p
        else Path.app (u + 1) true <$> Path.ofSubExprPos acc[u] p
      else Path.app 0 false <$> Path.ofSubExprPos e p

end Mathlib.Tactic.Widget.Rewrite

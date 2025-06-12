import Lean

open Lean

namespace Mathlib.Tactic.Widget.Rewrite

inductive Path where
  | node : Path
  | app (arg : Nat) (explicit : Bool) (next : Path) : Path
  | proj (next : Path) : Path
  | fun (next : Path) : Path
  | type (next : Path) : Path
  | body (next : Path) : Path
  | value (next : Path) : Path

def pathToSubExpr (expr : Expr) (path : Path) : MetaM SubExpr.Pos := do
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
          (go b next acc.pushLetBody)
      | .lam n t b bi
      | .forallE n t b bi => do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t bi
        withReader (fun ctx => {ctx with lctx})
          (go b next acc.pushBindingBody)
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
      let c ← getIdxExplicit expr.consumeMData (n + 1) (expr.getAppNumArgs - n - 1)
      go c next (acc.pushNaryArg expr.getAppNumArgs n)
    | .app (n + 1) false next =>
      expr.consumeMData.withApp fun f args => do
        let throw :=
          throwError m!"invalid explicit arg {n} access on{indentExpr expr}"
        let kinds ← PrettyPrinter.Delaborator.getParamKinds f args
        if let .error i := kinds.foldl
          (fun l k => l.bind fun (v, i) =>
            if let .default := k.bInfo then
              if v = n then .error i else .ok (v + 1, i + 1)
            else .ok (v, i + 1)) (Except.ok (0, 0)) then
          if let some c := args[i]? then
            go c next (acc.pushNaryArg expr.getAppNumArgs i)
          else throw
        else throw
  getIdxExplicit (e : Expr) (n k : Nat) : MetaM Expr :=
    match e, k with
    | .app _ a, 0 => pure a
    | .app f _, k + 1 => getIdxExplicit f n k
    | _, _ => throwError m!"invalid implicit arg {n} access on{indentExpr expr}"

end Mathlib.Tactic.Widget.Rewrite

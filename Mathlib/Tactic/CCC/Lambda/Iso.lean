/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.CCC.Lambda.Basic

universe u v w

namespace Mathlib.Tactic.CCC

inductive Object₀ (ι : Type u) : Type u where
  | of (i : ι) : Object₀ ι
  | prod (left right : Object₀ ι) : Object₀ ι
  | hom (source target : Object₀ ι) : Object₀ ι

inductive Objectq (ι : Type u) : Type u where
  | of (i : ι) : Objectq ι
  | prod (left right : Objectq ι) : Objectq ι
  | hom (source : Objectq ι) (target : ι) : Objectq ι

inductive Objectu (ι : Type u) where
  | of (i : ι) : Objectu ι
  | hom (source target : Objectu ι) : Objectu ι

def Object₀.toObject {ι : Type u} (o : Object₀ ι) : Object ι :=
  match o with
  | .of i => .of i
  | .prod left right => .prod left.toObject right.toObject
  | .hom source target => .hom source.toObject target.toObject

def Objectq.toObject₀ {ι : Type u} (o : Objectq ι) : Object₀ ι :=
  match o with
  | .of i => .of i
  | .prod left right => .prod left.toObject₀ right.toObject₀
  | .hom source target => .hom source.toObject₀ (.of target)

def Objectu.toObject₀ {ι : Type u} (o : Objectu ι) : Object₀ ι :=
  match o with
  | .of i => .of i
  | .hom source target => .hom source.toObject₀ target.toObject₀

def Object.elimUnit {ι : Type u} (o : Object ι) : Option (Object₀ ι) :=
  match o with
  | .of i => some (.of i)
  | .unit => none
  | .prod left right =>
    left.elimUnit.elim right.elimUnit fun l => some (right.elimUnit.elim l (.prod l))
  | .hom source target =>
    target.elimUnit.map fun i => source.elimUnit.elim i fun k => .hom k i

def Object₀.elimHom {ι : Type u} (o : Object₀ ι) : Objectq ι :=
  match o with
  | .of i => .of i
  | .prod left right => .prod left.elimHom right.elimHom
  | .hom source target => coHom source.elimHom target
where
  coHom {ι : Type u} (source : Objectq ι) (target : Object₀ ι) : Objectq ι :=
    match target with
    | .of i => .hom source i
    | .prod left right => .prod (coHom source left) (coHom source right)
    | .hom source' target => coHom (.prod source source'.elimHom) target

def Objectq.elimProd {ι : Type u} (o : Objectq ι) : List (Objectu ι) :=
  match o with
  | .of i => [.of i]
  | .prod left right => left.elimProd ++ right.elimProd
  | .hom source target => [source.elimProd.foldr .hom (.of target)]

structure Iso {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (source target : Object ι) where
  hom : LambdaTerm ι κ
  inv : LambdaTerm ι κ
  sath : Typing ζ (source :: ctx) hom target
  sati : Typing ζ (target :: ctx) inv source
  left_inv : Convertible
    ((sati.incrementBVars [target] source 1 (Eq.refl 1)).instantiate [] sath 0 (Eq.refl 0))
    (.bvar 0 source (Option.mem_some_self source))
  right_inv : Convertible
    ((sath.incrementBVars [source] target 1 (Eq.refl 1)).instantiate [] sati 0 (Eq.refl 0))
    (.bvar 0 target (Option.mem_some_self target))

def Iso.refl {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (type : Object ι) : Iso ζ ctx type type where
  hom := .bvar 0
  inv := .bvar 0
  sath := .bvar 0 type (Option.mem_some_self type)
  sati := .bvar 0 type (Option.mem_some_self type)
  left_inv := .refl _
  right_inv := .refl _

def Iso.symm {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {source target : Object ι} (iso : Iso ζ ctx source target) : Iso ζ ctx target source where
  hom := iso.inv
  inv := iso.hom
  sath := iso.sati
  sati := iso.sath
  left_inv := iso.right_inv
  right_inv := iso.left_inv

def Iso.trans {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {t₁ t₂ t₃ : Object ι} (iso₁₂ : Iso ζ ctx t₁ t₂) (iso₂₃ : Iso ζ ctx t₂ t₃) :
    Iso ζ ctx t₁ t₃ where
  hom := (iso₂₃.hom.incrementBVars 1).instantiate 0 iso₁₂.hom
  inv := (iso₁₂.inv.incrementBVars 1).instantiate 0 iso₂₃.inv
  sath := (iso₂₃.sath.incrementBVars [t₂] t₁ 1 (Eq.refl 1)).instantiate [] iso₁₂.sath 0 (Eq.refl 0)
  sati := (iso₁₂.sati.incrementBVars [t₂] t₃ 1 (Eq.refl 1)).instantiate [] iso₂₃.sati 0 (Eq.refl 0)
  left_inv := by
    refine .trans ?_ iso₁₂.left_inv
    refine .trans ?_ (.congr_instantiate_right [] _ (.congr_instantiate_left [] iso₁₂.sath
        (.congr_incrementBVars [t₂] iso₂₃.left_inv 1 (Eq.refl 1)) 0 (Eq.refl 0)) 0 (Eq.refl 0))
    refine .of_eq ?_ _ _
    simp only [instantiate_incrementBVars_assoc]
  right_inv := by
    refine .trans ?_ iso₂₃.right_inv
    refine .trans ?_ (.congr_instantiate_right [] _ (.congr_instantiate_left [] iso₂₃.sati
        (.congr_incrementBVars [t₂] iso₁₂.right_inv 1 (Eq.refl 1)) 0 (Eq.refl 0)) 0 (Eq.refl 0))
    refine .of_eq ?_ _ _
    simp only [instantiate_incrementBVars_assoc]

def Iso.unitProd {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (t : Object ι) : Iso ζ ctx (.prod .unit t) t where
  hom := .right (.bvar 0)
  inv := .prod .unit (.bvar 0)
  sath := .right (.bvar 0 (.prod .unit t) (Option.mem_some_self _))
  sati := .prod (.unit (t :: ctx)) (.bvar 0 t (Option.mem_some_self t))
  left_inv := .symm (.trans (.prod_eta _) (.congr_prod (.unit_eta _) (.refl _)))
  right_inv := .prod_right _ _

def Iso.prodUnit {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (t : Object ι) : Iso ζ ctx (.prod t .unit) t where
  hom := .left (.bvar 0)
  inv := .prod (.bvar 0) .unit
  sath := .left (.bvar 0 (.prod t .unit) (Option.mem_some_self _))
  sati := .prod (.bvar 0 t (Option.mem_some_self t)) (.unit (t :: ctx))
  left_inv := .symm (.trans (.prod_eta _) (.congr_prod (.refl _) (.unit_eta _)))
  right_inv := .prod_left _ _

def Iso.homUnit {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (t : Object ι) : Iso ζ ctx (.hom t .unit) .unit where
  hom := .unit
  inv := .lam t .unit
  sath := .unit (.hom t .unit :: ctx)
  sati := .lam (.unit (t :: .unit :: ctx))
  left_inv := .trans (.trans (.lam_eta _) (.congr_lam (.unit_eta _)))
    (.trans (.congr_lam (.symm (.unit_eta _))) (.symm (.lam_eta _)))
  right_inv := .trans (.unit_eta _) (.symm (.unit_eta _))

def Iso.unitHom {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (t : Object ι) : Iso ζ ctx (.hom .unit t) t where
  hom := .app (.bvar 0) .unit
  inv := .lam .unit (.bvar 1)
  sath := .app (.bvar 0 (.hom .unit t) (Option.mem_some_self _)) (.unit (.hom .unit t :: ctx))
  sati := .lam (.bvar 1 t (Option.mem_some_self t))
  left_inv := .symm (.trans (.lam_eta _) (.congr_lam (.congr_app (.refl _) (.unit_eta _))))
  right_inv := .beta _ _

def Iso.prodCongr {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {left₁ right₁ left₂ right₂ : Object ι}
    (left : Iso ζ ctx left₁ left₂) (right : Iso ζ ctx right₁ right₂) :
    Iso ζ ctx (.prod left₁ right₁) (.prod left₂ right₂) where
  hom := .prod
    ((left.hom.incrementBVars 1).instantiate 0 (.left (.bvar 0)))
    ((right.hom.incrementBVars 1).instantiate 0 (.right (.bvar 0)))
  inv := .prod
    ((left.inv.incrementBVars 1).instantiate 0 (.left (.bvar 0)))
    ((right.inv.incrementBVars 1).instantiate 0 (.right (.bvar 0)))
  sath := .prod
    ((left.sath.incrementBVars [left₁] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
      (.left (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))
    ((right.sath.incrementBVars [right₁] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
      (.right (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))
  sati := .prod
    ((left.sati.incrementBVars [left₂] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
      (.left (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))
    ((right.sati.incrementBVars [right₂] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
      (.right (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))
  left_inv := by
    refine .trans (.congr_prod ?_ ?_) (.symm (.prod_eta _))
    · refine .trans ?_ (.congr_instantiate_left [] _
        (.congr_incrementBVars [left₁] left.left_inv 1 (Eq.refl 1)) 0 (Eq.refl 0))
      refine .trans ?_ (.congr_instantiate_left [] _ (.refl _) 0 (Eq.refl 0))
      refine .trans (.of_eq (instantiate_incrementBVars_assoc _ _ _ 0) _
        ((left.sati.incrementBVars [left₂] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
          (.left (.prod
            ((left.sath.incrementBVars [left₁] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sath.incrementBVars [right₁] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
              (.right (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))))
          0 (Eq.refl 0))) ?_
      refine .trans (.congr_instantiate_right [] _ (.prod_left _ _) 0 (Eq.refl 0)) (.of_eq ?_ _ _)
      simp only [instantiate_incrementBVars_assoc]
    · refine .trans ?_ (.congr_instantiate_left [] _
        (.congr_incrementBVars [right₁] right.left_inv 1 (Eq.refl 1)) 0 (Eq.refl 0))
      refine .trans ?_ (.congr_instantiate_left [] _ (.refl _) 0 (Eq.refl 0))
      refine .trans (.of_eq (instantiate_incrementBVars_assoc _ _ _ 0) _
        ((right.sati.incrementBVars [right₂] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
          (.right (.prod
            ((left.sath.incrementBVars [left₁] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sath.incrementBVars [right₁] (.prod left₁ right₁) 1 (Eq.refl 1)).instantiate []
              (.right (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))))
          0 (Eq.refl 0))) ?_
      refine .trans (.congr_instantiate_right [] _ (.prod_right _ _) 0 (Eq.refl 0)) (.of_eq ?_ _ _)
      simp only [instantiate_incrementBVars_assoc]
  right_inv := by
    refine .trans (.congr_prod ?_ ?_) (.symm (.prod_eta _))
    · refine .trans ?_ (.congr_instantiate_left [] _
        (.congr_incrementBVars [left₂] left.right_inv 1 (Eq.refl 1)) 0 (Eq.refl 0))
      refine .trans ?_ (.congr_instantiate_left [] _ (.refl _) 0 (Eq.refl 0))
      refine .trans (.of_eq (instantiate_incrementBVars_assoc _ _ _ 0) _
        ((left.sath.incrementBVars [left₁] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
          (.left (.prod
            ((left.sati.incrementBVars [left₂] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sati.incrementBVars [right₂] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
              (.right (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))))
          0 (Eq.refl 0))) ?_
      refine .trans (.congr_instantiate_right [] _ (.prod_left _ _) 0 (Eq.refl 0)) (.of_eq ?_ _ _)
      simp only [instantiate_incrementBVars_assoc]
    · refine .trans ?_ (.congr_instantiate_left [] _
        (.congr_incrementBVars [right₂] right.right_inv 1 (Eq.refl 1)) 0 (Eq.refl 0))
      refine .trans ?_ (.congr_instantiate_left [] _ (.refl _) 0 (Eq.refl 0))
      refine .trans (.of_eq (instantiate_incrementBVars_assoc _ _ _ 0) _
        ((right.sath.incrementBVars [right₁] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
          (.right (.prod
            ((left.sati.incrementBVars [left₂] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sati.incrementBVars [right₂] (.prod left₂ right₂) 1 (Eq.refl 1)).instantiate []
              (.right (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))))
          0 (Eq.refl 0))) ?_
      refine .trans (.congr_instantiate_right [] _ (.prod_right _ _) 0 (Eq.refl 0)) (.of_eq ?_ _ _)
      simp only [instantiate_incrementBVars_assoc]

def Iso.homCongr {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {source₁ target₁ source₂ target₂ : Object ι}
    (source : Iso ζ ctx source₁ source₂) (target : Iso ζ ctx target₁ target₂) :
    Iso ζ ctx (.hom source₁ target₁) (.hom source₂ target₂) where
  hom := .lam source₂ ((((target.hom.incrementBVars 1).incrementBVars 1).instantiate 0
    (.app (.bvar 1) (source.inv.incrementBVars 1))))
  inv := .lam source₁ ((((target.inv.incrementBVars 1).incrementBVars 1).instantiate 0
    (.app (.bvar 1) (source.hom.incrementBVars 1))))
  sath := .lam (((target.sath.incrementBVars [target₁] (.hom source₁ target₁)
    1 (Eq.refl 1)).incrementBVars [target₁] source₂ 1 (Eq.refl 1)).instantiate []
      (.app (.bvar 1 (.hom source₁ target₁) (Option.mem_some_self _))
        (source.sati.incrementBVars [source₂] (.hom source₁ target₁) 1 (Eq.refl 1))) 0 (Eq.refl 0))
  sati := .lam (((target.sati.incrementBVars [target₂] (.hom source₂ target₂)
    1 (Eq.refl 1)).incrementBVars [target₂] source₁ 1 (Eq.refl 1)).instantiate []
      (.app (.bvar 1 (.hom source₂ target₂) (Option.mem_some_self _))
        (source.sath.incrementBVars [source₁] (.hom source₂ target₂) 1 (Eq.refl 1))) 0 (Eq.refl 0))
  left_inv := by
    refine .trans (.congr_lam ?_) (.symm (.lam_eta _))
    refine .trans (.of_eq (?eq : _ = ?_) _ ?_) ?_
    case eq =>
      rw [incrementBVars_instantiate_of_le _ _ (Nat.zero_le 2),
        instantiate_instantiate_of_le _ _ _ (Nat.zero_le 1),
        ← incrementBVars_incrementBVars_of_ge _ (Nat.one_le_of_lt Nat.two_pos),
        ← incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1),
        incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1), instantiate_incrementBVars]
      exact rfl
    · exact ((target.sati.incrementBVars [target₂] (.hom source₁ target₁)
          1 (Eq.refl 1)).incrementBVars [target₂] source₁ 1 (Eq.refl 1)).instantiate []
        (.instantiate [source₁]
          (.incrementBVars [source₁, (.hom source₂ target₂)] (.hom source₁ target₁)
            (.app (.bvar 1 (.hom source₂ target₂) (Option.mem_some_self _))
              (source.sath.incrementBVars [source₁] (.hom source₂ target₂) 1 (Eq.refl 1)))
            2 (Eq.refl 2))
          (.incrementBVars [] source₁ (.lam
            (((target.sath.incrementBVars [target₁] (.hom source₁ target₁)
                1 (Eq.refl 1)).incrementBVars [target₁] source₂ 1 (Eq.refl 1)).instantiate []
              (.app (.bvar 1 (.hom source₁ target₁) (Option.mem_some_self _))
                (source.sati.incrementBVars [source₂] (.hom source₁ target₁) 1 (Eq.refl 1)))
              0 (Eq.refl 0))) 0 (Eq.refl 0)) 1 (Eq.refl 1)) 0 (Eq.refl 0)
    refine .trans (.congr_instantiate_right [] _ (.beta _ _) 0 (Eq.refl 0)) ?_
    refine .trans (.of_eq (?eq : _ = ?_) _ ?_) ?_
    case eq =>
      rw [instantiate_incrementBVars_assoc, ← incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1),
        instantiate_incrementBVars, LambdaTerm.incrementBVars, LambdaTerm.incrementBVars,
        if_pos (Nat.le_refl 1), LambdaTerm.instantiate, LambdaTerm.instantiate,
        if_neg (Nat.add_one_ne_zero 1), if_pos (Nat.lt_add_one_of_le (Nat.zero_le 1)),
        incrementBVars_incrementBVars_of_ge source.inv (Nat.le_refl 1),
        ← incrementBVars_instantiate_of_le _ _ (Nat.zero_le 1)]
      exact rfl
    · exact ((target.sati.incrementBVars [target₂] (.hom source₁ target₁)
        1 (Eq.refl 1)).incrementBVars [target₂] source₁ 1 (Eq.refl 1)).instantiate []
          (((target.sath.incrementBVars [target₁] (.hom source₁ target₁)
            1 (Eq.refl 1)).incrementBVars [target₁] source₁ 1 (Eq.refl 1)).instantiate []
              (.app (.bvar 1 (.hom source₁ target₁) (Option.mem_some_self _))
                (((source.sati.incrementBVars [source₂] source₁ 1 (Eq.refl 1)).instantiate []
                  source.sath 0 (Eq.refl 0)).incrementBVars [source₁] (.hom source₁ target₁)
                    1 (Eq.refl 1))) 0 (Eq.refl 0)) 0 (Eq.refl 0)
    refine .trans (.congr_instantiate_right [] _ (.congr_instantiate_right [] _
      (.congr_app (.refl _) (.congr_incrementBVars [source₁] source.left_inv
        1 (Eq.refl 1))) 0 (Eq.refl 0)) 0 (Eq.refl 0)) ?_
    refine .trans (.of_eq (?eq : _ = ?_) _ ?_) ?_
    case eq =>
      rw [← instantiate_incrementBVars_assoc, incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1),
        ← incrementBVars_instantiate_of_le _ _ (Nat.zero_le 1)]
      exact rfl
    · exact ((((target.sati.incrementBVars [target₂] target₁ 1 (Eq.refl 1)).instantiate []
        target.sath 0 (Eq.refl 0)).incrementBVars [target₁] (.hom source₁ target₁)
          1 (Eq.refl 1)).incrementBVars [target₁] source₁ 1 (Eq.refl 1)).instantiate []
            (.app (.bvar 1 (.hom source₁ target₁) (Option.mem_some_self _))
              (.bvar 0 source₁ (Option.mem_some_self source₁))) 0 (Eq.refl 0)
    exact (.congr_instantiate_left [] _ (.congr_incrementBVars [target₁]
      (.congr_incrementBVars [target₁] target.left_inv 1 (Eq.refl 1))
        1 (Eq.refl 1)) 0 (Eq.refl 0))
  right_inv := by
    refine .trans (.congr_lam ?_) (.symm (.lam_eta _))
    refine .trans (.of_eq (?eq : _ = ?_) _ ?_) ?_
    case eq =>
      rw [incrementBVars_instantiate_of_le _ _ (Nat.zero_le 2),
        instantiate_instantiate_of_le _ _ _ (Nat.zero_le 1),
        ← incrementBVars_incrementBVars_of_ge _ (Nat.one_le_of_lt Nat.two_pos),
        ← incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1),
        incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1), instantiate_incrementBVars]
      exact rfl
    · exact ((target.sath.incrementBVars [target₁] (.hom source₂ target₂)
          1 (Eq.refl 1)).incrementBVars [target₁] source₂ 1 (Eq.refl 1)).instantiate []
        (.instantiate [source₂]
          (.incrementBVars [source₂, (.hom source₁ target₁)] (.hom source₂ target₂)
            (.app (.bvar 1 (.hom source₁ target₁) (Option.mem_some_self _))
              (source.sati.incrementBVars [source₂] (.hom source₁ target₁) 1 (Eq.refl 1)))
            2 (Eq.refl 2))
          (.incrementBVars [] source₂ (.lam
            (((target.sati.incrementBVars [target₂] (.hom source₂ target₂)
                1 (Eq.refl 1)).incrementBVars [target₂] source₁ 1 (Eq.refl 1)).instantiate []
              (.app (.bvar 1 (.hom source₂ target₂) (Option.mem_some_self _))
                (source.sath.incrementBVars [source₁] (.hom source₂ target₂) 1 (Eq.refl 1)))
              0 (Eq.refl 0))) 0 (Eq.refl 0)) 1 (Eq.refl 1)) 0 (Eq.refl 0)
    refine .trans (.congr_instantiate_right [] _ (.beta _ _) 0 (Eq.refl 0)) ?_
    refine .trans (.of_eq (?eq : _ = ?_) _ ?_) ?_
    case eq =>
      rw [instantiate_incrementBVars_assoc, ← incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1),
        instantiate_incrementBVars, LambdaTerm.incrementBVars, LambdaTerm.incrementBVars,
        if_pos (Nat.le_refl 1), LambdaTerm.instantiate, LambdaTerm.instantiate,
        if_neg (Nat.add_one_ne_zero 1), if_pos (Nat.lt_add_one_of_le (Nat.zero_le 1)),
        incrementBVars_incrementBVars_of_ge source.hom (Nat.le_refl 1),
        ← incrementBVars_instantiate_of_le _ _ (Nat.zero_le 1)]
      exact rfl
    · exact ((target.sath.incrementBVars [target₁] (.hom source₂ target₂)
        1 (Eq.refl 1)).incrementBVars [target₁] source₂ 1 (Eq.refl 1)).instantiate []
          (((target.sati.incrementBVars [target₂] (.hom source₂ target₂)
            1 (Eq.refl 1)).incrementBVars [target₂] source₂ 1 (Eq.refl 1)).instantiate []
              (.app (.bvar 1 (.hom source₂ target₂) (Option.mem_some_self _))
                (((source.sath.incrementBVars [source₁] source₂ 1 (Eq.refl 1)).instantiate []
                  source.sati 0 (Eq.refl 0)).incrementBVars [source₂] (.hom source₂ target₂)
                    1 (Eq.refl 1))) 0 (Eq.refl 0)) 0 (Eq.refl 0)
    refine .trans (.congr_instantiate_right [] _ (.congr_instantiate_right [] _
      (.congr_app (.refl _) (.congr_incrementBVars [source₂] source.right_inv
        1 (Eq.refl 1))) 0 (Eq.refl 0)) 0 (Eq.refl 0)) ?_
    refine .trans (.of_eq (?eq : _ = ?_) _ ?_) ?_
    case eq =>
      rw [← instantiate_incrementBVars_assoc, incrementBVars_incrementBVars_of_ge _ (Nat.le_refl 1),
        ← incrementBVars_instantiate_of_le _ _ (Nat.zero_le 1)]
      exact rfl
    · exact ((((target.sath.incrementBVars [target₁] target₂ 1 (Eq.refl 1)).instantiate []
        target.sati 0 (Eq.refl 0)).incrementBVars [target₂] (.hom source₂ target₂)
          1 (Eq.refl 1)).incrementBVars [target₂] source₂ 1 (Eq.refl 1)).instantiate []
            (.app (.bvar 1 (.hom source₂ target₂) (Option.mem_some_self _))
              (.bvar 0 source₂ (Option.mem_some_self source₂))) 0 (Eq.refl 0)
    exact (.congr_instantiate_left [] _ (.congr_incrementBVars [target₂]
      (.congr_incrementBVars [target₂] target.right_inv 1 (Eq.refl 1))
        1 (Eq.refl 1)) 0 (Eq.refl 0))

def Iso.elimUnit {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (o : Object ι) : Iso ζ ctx o (o.elimUnit.elim Object.unit Object₀.toObject) :=
  match o with
  | .of i => .refl ζ ctx (.of i)
  | .unit => .refl ζ ctx .unit
  | .prod left right =>
    Option.rec (motive := fun u => Iso ζ ctx left (u.elim Object.unit Object₀.toObject) →
        Iso ζ ctx (.prod left right) ((u.elim right.elimUnit fun l =>
          some (right.elimUnit.elim l (.prod l))).elim Object.unit Object₀.toObject))
      (fun ihl => .trans (.prodCongr ihl (.elimUnit ζ ctx right)) (.unitProd ζ ctx _))
      (fun u ihl =>
        Option.rec (motive := fun v => Iso ζ ctx right (v.elim Object.unit Object₀.toObject) →
            Iso ζ ctx (.prod left right) (v.elim u (.prod u)).toObject)
          (fun ihr => .trans (.prodCongr ihl ihr) (.prodUnit ζ ctx u.toObject))
          (fun _ ihr => .prodCongr ihl ihr) right.elimUnit (.elimUnit ζ ctx right))
      left.elimUnit (.elimUnit ζ ctx left)
  | .hom source target =>
    Option.rec (motive := fun u => Iso ζ ctx target (u.elim Object.unit Object₀.toObject) →
        Iso ζ ctx (.hom source target) (((u.map fun i => source.elimUnit.elim i fun k =>
          Object₀.hom k i)).elim Object.unit Object₀.toObject))
    (fun iht => .trans (.homCongr (.refl ζ ctx source) iht) (.homUnit ζ ctx source))
    (fun u iht =>
      Option.rec (motive := fun v => Iso ζ ctx source (v.elim Object.unit Object₀.toObject) →
          Iso ζ ctx (.hom source target) (v.elim u fun k => .hom k u).toObject)
        (fun ihs => .trans (.homCongr ihs iht) (.unitHom ζ ctx u.toObject))
        (fun _ ihs => .homCongr ihs iht) source.elimUnit (.elimUnit ζ ctx source))
    target.elimUnit (.elimUnit ζ ctx target)

def Iso.homProd {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (s t₁ t₂ : Object ι) : Iso ζ ctx (.hom s (.prod t₁ t₂)) (.prod (.hom s t₁) (.hom s t₂)) where
  hom := .prod
    (.lam s (.left (.app (.bvar 1) (.bvar 0))))
    (.lam s (.right (.app (.bvar 1) (.bvar 0))))
  inv := .lam s (.prod (.app (.left (.bvar 1)) (.bvar 0)) (.app (.right (.bvar 1)) (.bvar 0)))
  sath := .prod
    (.lam (.left (.app (.bvar 1 (.hom s (.prod t₁ t₂)) (Option.mem_some_self _))
      (.bvar 0 s (Option.mem_some_self s)))))
    (.lam (.right (.app (.bvar 1 (.hom s (.prod t₁ t₂)) (Option.mem_some_self _))
      (.bvar 0 s (Option.mem_some_self s)))))
  sati := .lam (.prod
    (.app (.left (.bvar 1 (.prod (.hom s t₁) (.hom s t₂)) (Option.mem_some_self _)))
      (.bvar 0 s (Option.mem_some_self s)))
    (.app (.right (.bvar 1 (.prod (.hom s t₁) (.hom s t₂)) (Option.mem_some_self _)))
      (.bvar 0 s (Option.mem_some_self s))))
  left_inv := .trans (.congr_lam (.trans (.congr_prod
      (.trans (.congr_app (.prod_left _ _) (.refl _)) (.beta _ _))
      (.trans (.congr_app (.prod_right _ _) (.refl _)) (.beta _ _)))
    (.symm (.prod_eta _)))) (.symm (.lam_eta _))
  right_inv := .trans (.congr_prod
      (.trans (.congr_lam (.trans (.congr_left (.beta _ _))
        (.prod_left _ _))) (.symm (.lam_eta _)))
      (.trans (.congr_lam (.trans (.congr_right (.beta _ _))
        (.prod_right _ _))) (.symm (.lam_eta _))))
    (.symm (.prod_eta _))

def Iso.curry {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (s₁ s₂ t : Object ι) : Iso ζ ctx (.hom (.prod s₁ s₂) t) (.hom s₁ (.hom s₂ t)) where
  hom := .lam s₁ (.lam s₂ (.app (.bvar 2) (.prod (.bvar 1) (.bvar 0))))
  inv := .lam (.prod s₁ s₂) (.app (.app (.bvar 1) (.left (.bvar 0))) (.right (.bvar 0)))
  sath := .lam (.lam (.app (.bvar 2 (.hom (.prod s₁ s₂) t) (Option.mem_some_self _))
    (.prod (.bvar 1 s₁ (Option.mem_some_self s₁)) (.bvar 0 s₂ (Option.mem_some_self s₂)))))
  sati := .lam (.app (.app (.bvar 1 (.hom s₁ (.hom s₂ t)) (Option.mem_some_self _))
    (.left (.bvar 0 (.prod s₁ s₂) (Option.mem_some_self _))))
    (.right (.bvar 0 (.prod s₁ s₂) (Option.mem_some_self _))))
  left_inv := .trans (.congr_lam (.trans (.congr_app (.beta _ _) (.refl _))
    (.trans (.beta _ _) (.congr_app (.refl _) (.symm (.prod_eta _)))))) (.symm (.lam_eta _))
  right_inv := .trans (.congr_lam (.trans (.congr_lam
    (.trans (.beta _ _) (.congr_app (.congr_app (.refl _) (.prod_left _ _)) (.prod_right _ _))))
      (.symm (.lam_eta _)))) (.symm (.lam_eta _))

def Iso.elimHom {ι : Type u} {κ : Type v} (ζ : κ → Object ι) (ctx : List (Object ι))
    (o : Object₀ ι) : Iso ζ ctx o.toObject o.elimHom.toObject₀.toObject :=
  match o with
  | .of i => .refl ζ ctx (.of i)
  | .prod left right => .prodCongr (.elimHom ζ ctx left) (.elimHom ζ ctx right)
  | .hom source target => coHom (.elimHom ζ ctx source) target
where
  coHom {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {source : Object₀ ι} (ihs : Iso ζ ctx source.toObject source.elimHom.toObject₀.toObject)
    (target : Object₀ ι) : Iso ζ ctx (Object₀.hom source target).toObject
      (Object₀.elimHom.coHom source.elimHom target).toObject₀.toObject :=
    match target with
    | .of i => .homCongr ihs (.refl ζ ctx (.of i))
    | .prod left right => .trans (.homProd ζ ctx source.toObject left.toObject right.toObject)
      (.prodCongr (coHom ihs left) (coHom ihs right))
    | .hom source' target => .trans (.symm
        (.curry ζ ctx source.toObject source'.toObject target.toObject))
      (@coHom ι κ ζ ctx (.prod source source') (.prodCongr ihs (elimHom ζ ctx source')) target)

def LambdaTerm.abstract {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ) (ks : List κ) (n : Nat) :
    LambdaTerm ι Empty × List κ :=
  match t with
  | .of k => (.bvar (ks.length + n), k :: ks)
  | .unit => (.unit, ks)
  | .prod l r =>
    letI c := l.abstract ks n
    letI d := r.abstract c.2 n
    (.prod c.1 d.1, d.2)
  | .lam dom body =>
    letI c := body.abstract ks (n + 1)
    (.lam dom c.1, c.2)
  | .app fn arg =>
    letI c := fn.abstract ks n
    letI d := arg.abstract c.2 n
    (.app c.1 d.1, d.2)
  | .left tup =>
    letI c := tup.abstract ks n
    (.left c.1, c.2)
  | .right tup =>
    letI c := tup.abstract ks n
    (.right c.1, c.2)
  | .bvar deBruijnIndex => (.bvar deBruijnIndex, ks)

inductive Morphism {ι : Type u} {κ : Type v} (s t : κ → Object ι) :
    (source target : Object ι) → Type (max u v) where
  | of (k : κ) : Morphism s t (s k) (t k)
  | id (obj : Object ι) : Morphism s t obj obj
  | comp {obj₁ obj₂ obj₃ : Object ι}
    (f : Morphism s t obj₁ obj₂) (g : Morphism s t obj₂ obj₃) : Morphism s t obj₁ obj₃
  | unit (src : Object ι) : Morphism s t src .unit
  | prod {src tl tr : Object ι} (left : Morphism s t src tl) (right : Morphism s t src tr) :
    Morphism s t src (.prod tl tr)
  | left (tl tr : Object ι) : Morphism s t (.prod tl tr) tl
  | right (tl tr : Object ι) : Morphism s t (.prod tl tr) tr
  | curry {tl tr ta : Object ι} (u : Morphism s t (.prod tl tr) ta) : Morphism s t tr (.hom tl ta)
  | eval (td ta : Object ι) : Morphism s t (.prod td (.hom td ta)) ta

def Morphism.read {ι : Type u} {κ : Type v} {s t : κ → Object ι}
    (ri : ι → Type w) (rk : (k : κ) → (s k).read ri → (t k).read ri)
    {src tgt : Object ι} (t : Morphism s t src tgt) : src.read ri → tgt.read ri :=
  match t with
  | .of k => rk k
  | .id _ => fun x => x
  | .comp f g => fun x => g.read ri rk (f.read ri rk x)
  | .unit _ => fun _ => PUnit.unit
  | .prod f g => fun x => (f.read ri rk x, g.read ri rk x)
  | .left _ _ => Prod.fst
  | .right _ _ => Prod.snd
  | .curry f => fun x y => f.read ri rk (y, x)
  | .eval _ _ => fun x => x.2 x.1

-- section CategoryTheory
-- open CategoryTheory MonoidalCategory

-- variable {C : Type w} [Category.{r} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

-- def Object.interpret {ι : Type u} (ri : ι → C) (t : Object ι) : C :=
--   match t with
--   | .of i => ri i
--   | .unit => 𝟙_ C
--   | .prod l r => l.interpret ri ⊗ r.interpret ri
--   | .hom s t => s.interpret ri ⟹ t.interpret ri

-- def Morphism.interpret {ι : Type u} {κ : Type v} {s t : κ → Object ι}
--     (ri : ι → C) (rk : (k : κ) → (s k).interpret ri ⟶ (t k).interpret ri)
--     {src tgt : Object ι} (t : Morphism s t src tgt) : src.interpret ri ⟶ tgt.interpret ri :=
--   match t with
--   | .of k => rk k
--   | .id _ => 𝟙 _
--   | .comp f g => f.interpret ri rk ≫ g.interpret ri rk
--   | .unit _ => CartesianMonoidalCategory.toUnit _
--   | .prod f g => CartesianMonoidalCategory.lift (f.interpret ri rk) (g.interpret ri rk)
--   | .left _ _ => CartesianMonoidalCategory.fst _ _
--   | .right _ _ => CartesianMonoidalCategory.snd _ _
--   | .curry f => CartesianClosed.curry (f.interpret ri rk)
--   | .eval _ _ => (CategoryTheory.exp.ev _).app _

-- end CategoryTheory

-- inductive Morphism.Equiv {ι : Type u} {κ : Type v} {s t : κ → Object ι} :
--     {source target : Object ι} → (left right : Morphism s t source target) → Prop where
--   | refl {source target : Object ι} (u : Morphism s t source target) : Morphism.Equiv u u
--   | symm {source target : Object ι} {u v : Morphism s t source target}
--     (h : Morphism.Equiv u v) : Morphism.Equiv v u
--   | trans {source target : Object ι} {u v w : Morphism s t source target}
--     (h₁ : Morphism.Equiv u v) (h₂ : Morphism.Equiv v w) : Morphism.Equiv u w
--   | congr_comp {obj₁ obj₂ obj₃ : Object ι}
--     {f₁ f₂ : Morphism s t obj₁ obj₂} {g₁ g₂ : Morphism s t obj₂ obj₃}
--     (hf : Morphism.Equiv f₁ f₂) (hg : Morphism.Equiv g₁ g₂) :
--     Morphism.Equiv (.comp f₁ g₂) (.comp f₂ g₂)
--   | congr_prod {src left right : Object ι}
--     {f₁ f₂ : Morphism s t src left} {g₁ g₂ : Morphism s t src right}
--     (hf : Morphism.Equiv f₁ f₂) (hg : Morphism.Equiv g₁ g₂) :
--     Morphism.Equiv (.prod f₁ g₂) (.prod f₂ g₂)
--   | congr_curry {tl tr ta : Object ι} {u₁ u₂ : Morphism s t (.prod tl tr) ta}
--     (h : Morphism.Equiv u₁ u₂) : Morphism.Equiv (.curry u₁) (.curry u₂)

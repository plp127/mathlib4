/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.CCC.Lambda.Basic

universe u v w

namespace Mathlib.Tactic.CCC

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

end Mathlib.Tactic.CCC

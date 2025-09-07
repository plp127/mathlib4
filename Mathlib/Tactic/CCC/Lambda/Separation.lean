/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.CCC.Lambda.Iso
import Mathlib.Tactic.CCC.Lambda.Normalization
import Mathlib.Data.Finsupp.Defs
import Mathlib.Logic.Equiv.Fin.Basic

universe u v w

namespace Mathlib.Tactic.CCC

mutual

inductive Normalu {ι : Type u} {κ : Type v} (ζ : κ → Object ι) :
    (ctx : List (Object ι)) → (typ : Object ι) → Type (max u v) where
  | ofNeutral {ctx : List (Object ι)} {t : ι} (n : Neutralu ζ ctx (.of t)) : Normalu ζ ctx (.of t)
  | lam {ctx : List (Object ι)} (dom : Object ι) {tb : Object ι}
    (body : Normalu ζ (dom :: ctx) tb) : Normalu ζ ctx (.hom dom tb)

inductive Neutralu {ι : Type u} {κ : Type v} (ζ : κ → Object ι) :
    (ctx : List (Object ι)) → (typ : Object ι) → Type (max u v) where
  | of (k : κ) (ctx : List (Object ι)) : Neutralu ζ ctx (ζ k)
  | app {ctx : List (Object ι)} {typed typea : Object ι}
    (fn : Neutralu ζ ctx (.hom typed typea)) (arg : Normalu ζ ctx typed) : Neutralu ζ ctx typea
  | bvar {ctx : List (Object ι)} (n : Nat) (typ : Object ι) (sat : typ ∈ ctx[n]?) :
    Neutralu ζ ctx typ

end

mutual

def Normalu.toNormal {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} (t : Normalu ζ ctx typ) : Normal ζ ctx typ :=
  match t with
  | .ofNeutral n => .ofNeutral n.toNeutral
  | .lam dom body => .lam dom body.toNormal

def Neutralu.toNeutral {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} (t : Neutralu ζ ctx typ) : Neutral ζ ctx typ :=
  match t with
  | .of k ctx => .of k ctx
  | .app fn arg => .app fn.toNeutral arg.toNormal
  | .bvar n typ sat => .bvar n typ sat

end

def extendI {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) : ι →₀ Nat where
  toFun := Function.update f i (f i + 1)
  support := if h : f i = 0 then f.support.cons i (f.notMem_support_iff.2 h) else f.support
  mem_support_toFun _ := by
    rw [Function.update_apply]
    split_ifs with hi hx hx <;> simp [hi, hx]

@[simp]
theorem coe_extendI {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) :
    ⇑(extendI f i) = Function.update f i (f i + 1) := rfl

def Extends {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) {typ : Object ι}
    (rk₁ : typ.read fun u => Fin (2 ^ f u))
    (rk₂ : typ.read fun u => Fin (2 ^ extendI f i u)) : Prop :=
  match typ with
  | .of u => rk₁ = if hu : u = i then
    (finProdFinEquiv.symm (rk₂.cast (by simp [hu, Nat.pow_add])) : Fin (2 ^ f u) × Fin 2).1
    else rk₂.cast (congrArg (2 ^ ·) (by simp [hu]))
  | .unit => True
  | .prod _ _ => Extends f i rk₁.1 rk₂.1 ∧ Extends f i rk₁.2 rk₂.2
  | .hom source target =>
    ∀ (ra₁ : source.read fun u => Fin (2 ^ f u))
      (ra₂ : source.read fun u => Fin (2 ^ extendI f i u)),
      Extends f i ra₁ ra₂ → Extends f i (rk₁ ra₁) (rk₂ ra₂)

def Separation {ι : Type u} (ri : ι → Type v) {typ : Object ι}
    (rk₁ rk₂ : typ.read ri) : Type v :=
  match typ with
  | .of _ => ULift (PLift (rk₁ ≠ rk₂))
  | .unit => PEmpty
  | .prod _ _ => Separation ri rk₁.1 rk₂.1 ⊕ Separation ri rk₁.2 rk₂.2
  | .hom source _ => (s : source.read ri) × Separation ri (rk₁ s) (rk₂ s)

theorem Separation.ne {ι : Type u} (ri : ι → Type v) {typ : Object ι}
    {rk₁ rk₂ : typ.read ri} (sep : Separation ri rk₁ rk₂) : rk₁ ≠ rk₂ := by
  induction typ with
  | of i => exact sep.down.down
  | unit => exact sep.elim
  | prod _ _ ihl ihr =>
    cases sep with
    | inl sep => exact ne_of_apply_ne Prod.fst (ihl sep)
    | inr sep => exact ne_of_apply_ne Prod.snd (ihr sep)
  | hom _ _ _ ih => exact ne_of_apply_ne (Function.eval sep.1) (ih sep.2)

mutual

def extend {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) {typ : Object ι}
    (rk₁ : typ.read fun u => Fin (2 ^ f u)) :
    { rk₂ : typ.read fun u => Fin (2 ^ extendI f i u) // Extends f i rk₁ rk₂ } :=
  match typ with
  | .of u => ⟨if hu : u = i then
    (finProdFinEquiv ((rk₁, 0) : Fin (2 ^ f u) × Fin 2)).cast (by simp [hu, Nat.pow_add])
    else rk₁.cast (by simp [hu]), by unfold Extends; split <;> simp⟩
  | .unit => ⟨rk₁, trivial⟩
  | .prod _ _ =>
    ⟨((extend f i rk₁.1).1, (extend f i rk₁.2).1),
      ⟨(extend f i rk₁.1).2, (extend f i rk₁.2).2⟩⟩
  | .hom source target =>
    ⟨fun k => (extend f i (rk₁ (restrict f i k).1)).1, fun ra₁ ra₂ h =>
      (plift_extends_unique f i ((restrict f i ra₂).2 ra₁ h) h).down ▸ (extend f i (rk₁ ra₁)).2⟩

def restrict {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) {typ : Object ι}
    (rk₂ : typ.read fun u => Fin (2 ^ extendI f i u)) :
    { rk₁ : typ.read fun u => Fin (2 ^ f u) // ∀ rk₃, Extends f i rk₃ rk₂ → Extends f i rk₁ rk₂ } :=
  match typ with
  | .of u => ⟨if hu : u = i then
    (finProdFinEquiv.symm (rk₂.cast (by simp [hu, Nat.pow_add])) : Fin (2 ^ f u) × Fin 2).1
    else rk₂.cast (by simp [hu]), fun _ _ => rfl⟩
  | .unit => ⟨rk₂, fun _ _ => trivial⟩
  | .prod _ _ =>
    ⟨((restrict f i rk₂.1).1, (restrict f i rk₂.2).1),
      fun k hk => ⟨(restrict f i rk₂.1).2 k.1 hk.1, (restrict f i rk₂.2).2 k.2 hk.2⟩⟩
  | .hom source target =>
    ⟨fun k => (restrict f i (rk₂ (extend f i k).1)).1, fun k hk ra₁ ra₂ h =>
      ((plift_extends_unique f i
        (hk ra₁ (extend f i ra₁).1 (extend f i ra₁).2)
        ((restrict f i (rk₂ (extend f i ra₁).1)).2 (k ra₁)
          (hk ra₁ (extend f i ra₁).1 (extend f i ra₁).2))).down ▸ hk ra₁ ra₂ h :)⟩

def plift_extends_unique {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) {typ : Object ι}
    {rk₁ rk₂ : typ.read fun u => Fin (2 ^ f u)} {rk₃ : typ.read fun u => Fin (2 ^ extendI f i u)}
    (h₁ : Extends f i rk₁ rk₃) (h₂ : Extends f i rk₂ rk₃) : PLift (rk₁ = rk₂) :=
  match typ with
  | .of _ => .up (h₁.trans h₂.symm)
  | .unit => .up rfl
  | .prod _ _ => .up (Prod.ext
    (plift_extends_unique f i h₁.1 h₂.1).down
    (plift_extends_unique f i h₁.2 h₂.2).down)
  | .hom _ _ => .up (funext fun k => (plift_extends_unique f i
    (h₁ k (extend f i k).1 (extend f i k).2)
    (h₂ k (extend f i k).1 (extend f i k).2)).down)

end

theorem extends_unique {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) {typ : Object ι}
    {rk₁ rk₂ : typ.read fun u => Fin (2 ^ f u)} {rk₃ : typ.read fun u => Fin (2 ^ extendI f i u)}
    (h₁ : Extends f i rk₁ rk₃) (h₂ : Extends f i rk₂ rk₃) : rk₁ = rk₂ :=
  (plift_extends_unique f i h₁ h₂).down

def IsRightProjection {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) (ss : List (Object ι))
    (rk₂ : (ss.foldr Object.hom (.of i)).read fun u => Fin (2 ^ extendI f i u))
    (fn : (ss.foldr (fun k t => k.read (fun u => Fin (2 ^ extendI f i u)) → t) (Fin 2))) : Prop :=
  match ss with
  | [] => (finProdFinEquiv.symm (rk₂.cast (by simp [Nat.pow_add])) : Fin (2 ^ f i) × Fin 2).2 = fn
  | s :: ss => ∀ k, IsRightProjection f i ss (rk₂ k) (fn k)

def extendWith {ι : Type u} [DecidableEq ι] (f : ι →₀ Nat) (i : ι) (ss : List (Object ι))
    (rk₁ : (ss.foldr Object.hom (.of i)).read fun u => Fin (2 ^ f u))
    (fn : (ss.foldr (fun k t => k.read (fun u => Fin (2 ^ extendI f i u)) → t) (Fin 2))) :
    { rk₂ : (ss.foldr Object.hom (.of i)).read fun u => Fin (2 ^ extendI f i u) //
      Extends f i rk₁ rk₂ ∧ IsRightProjection f i ss rk₂ fn } :=
  match ss with
  | [] =>
    ⟨(finProdFinEquiv ((rk₁, fn) : Fin (2 ^ f i) × Fin 2)).cast (by simp [Nat.pow_add]),
      by simp [Extends], by simp [IsRightProjection]⟩
  | s :: ss =>
    ⟨fun k => (extendWith f i ss (rk₁ (restrict f i k).1) (fn k)).1,
      fun ra₁ ra₂ h => extends_unique f i h ((restrict f i ra₂).2 ra₁ h) ▸
        (extendWith f i ss (rk₁ ra₁) (fn ra₂)).2.1,
      fun k => (extendWith f i ss (rk₁ (restrict f i k).1) (fn k)).2.2⟩

end Mathlib.Tactic.CCC

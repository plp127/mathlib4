/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.CCC.Lambda.Basic

universe u v w

namespace Mathlib.Tactic.CCC

@[simp]
def LambdaTerm.replaceBVars {ι : Type u} {κ : Type v} (sub : Nat → LambdaTerm ι κ)
    (t : LambdaTerm ι κ) : LambdaTerm ι κ :=
  match t with
  | .of k => .of k
  | .unit => .unit
  | .prod l r => .prod (l.replaceBVars sub) (r.replaceBVars sub)
  | .lam dom body => .lam dom (body.replaceBVars fun n =>
    n.casesOn (.bvar 0) fun u => (sub u).incrementBVars 0)
  | .app fn arg => .app (fn.replaceBVars sub) (arg.replaceBVars sub)
  | .left tup => .left (tup.replaceBVars sub)
  | .right tup => .right (tup.replaceBVars sub)
  | .bvar deBruijnIndex => sub deBruijnIndex

@[simp]
def Typing.replaceBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx₁ ctx₂ : List (Object ι)}
    {sub : Nat → LambdaTerm ι κ} {tt : Object ι} {t : LambdaTerm ι κ}
    (sats : (n : Nat) → (hn : n < ctx₁.length) → Typing ζ ctx₂ (sub n) ctx₁[n])
    (satt : Typing ζ ctx₁ t tt) : Typing ζ ctx₂ (t.replaceBVars sub) tt :=
  match satt with
  | .of k _ => .of k ctx₂
  | .unit _ => .unit ctx₂
  | .prod satl satr => .prod (satl.replaceBVars sats) (satr.replaceBVars sats)
  | .lam sat => .lam (sat.replaceBVars fun n => n.casesOn
    (fun hn => .bvar 0 _ (Option.mem_some_self _))
    (fun n hn => (sats n (Nat.lt_of_succ_lt_succ hn)).incrementBVars [] _ 0 (Eq.refl 0)))
  | .app satd sata => .app (satd.replaceBVars sats) (sata.replaceBVars sats)
  | .left sat => .left (sat.replaceBVars sats)
  | .right sat => .right (sat.replaceBVars sats)
  | .bvar deBruijnIndex type sat =>
    Option.mem_some.1 (List.getElem?_eq_getElem _ ▸ sat) ▸ sats deBruijnIndex (by grind)

theorem replaceBVars_incrementBVars {ι : Type u} {κ : Type v} (sub : Nat → LambdaTerm ι κ)
    (n : Nat) (t : LambdaTerm ι κ) : (t.incrementBVars n).replaceBVars sub =
      t.replaceBVars fun k => if k < n then sub k else sub (k + 1) := by
  induction t generalizing sub n with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl sub n) (ihr sub n)
  | lam dom body ih =>
    refine congrArg (LambdaTerm.lam dom) ((ih _ _).trans ?_)
    refine congrArg body.replaceBVars (funext fun u => u.casesOn (by simp) fun v => ?_)
    simp [apply_ite (LambdaTerm.incrementBVars 0)]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf sub n) (iha sub n)
  | left _ ih => exact congrArg LambdaTerm.left (ih sub n)
  | right _ ih => exact congrArg LambdaTerm.right (ih sub n)
  | bvar _ =>
    simp only [LambdaTerm.incrementBVars, apply_ite (LambdaTerm.replaceBVars sub),
      LambdaTerm.replaceBVars, ← Nat.not_lt, ite_not]

theorem incrementBVars_replaceBVars {ι : Type u} {κ : Type v} (sub : Nat → LambdaTerm ι κ)
    (n : Nat) (t : LambdaTerm ι κ) : (t.replaceBVars sub).incrementBVars n =
      t.replaceBVars fun k => (sub k).incrementBVars n := by
  induction t generalizing sub n with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl sub n) (ihr sub n)
  | lam dom body ih =>
    exact congrArg (LambdaTerm.lam dom) ((ih _ (n + 1)).trans
      (congrArg (fun sub ↦ LambdaTerm.replaceBVars sub body)
        (funext fun u ↦ Nat.casesOn u rfl fun v ↦
          (incrementBVars_incrementBVars_of_ge (sub v) (Nat.zero_le n)).symm)))
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf sub n) (iha sub n)
  | left _ ih => exact congrArg LambdaTerm.left (ih sub n)
  | right _ ih => exact congrArg LambdaTerm.right (ih sub n)
  | bvar _ => rfl

theorem replaceBVars_replaceBVars {ι : Type u} {κ : Type v} (sub₁ sub₂ : Nat → LambdaTerm ι κ)
    (t : LambdaTerm ι κ) : (t.replaceBVars sub₁).replaceBVars sub₂ =
      t.replaceBVars fun n => (sub₁ n).replaceBVars sub₂ := by
  induction t generalizing sub₁ sub₂ with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl sub₁ sub₂) (ihr sub₁ sub₂)
  | lam dom body ih =>
    refine congrArg (LambdaTerm.lam dom) ((ih _ _).trans ?_)
    refine congrArg body.replaceBVars (funext fun n => n.casesOn rfl fun u => ?_)
    simp [incrementBVars_replaceBVars, replaceBVars_incrementBVars]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf sub₁ sub₂) (iha sub₁ sub₂)
  | left _ ih => exact congrArg LambdaTerm.left (ih sub₁ sub₂)
  | right _ ih => exact congrArg LambdaTerm.right (ih sub₁ sub₂)
  | bvar _ => rfl

theorem instantiate_replaceBVars {ι : Type u} {κ : Type v} (sub : Nat → LambdaTerm ι κ)
    (n : Nat) (s t : LambdaTerm ι κ) : (t.replaceBVars sub).instantiate n s =
      t.replaceBVars fun k => (sub k).instantiate n s := by
  induction t generalizing sub n s with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl sub n s) (ihr sub n s)
  | lam dom body ih =>
    exact congrArg (LambdaTerm.lam dom) ((ih _ (n + 1) (s.incrementBVars 0)).trans
      (congrArg (fun sub ↦ LambdaTerm.replaceBVars sub body)
        (funext fun u ↦ Nat.casesOn u (by simp) fun v ↦
          (incrementBVars_instantiate_of_ge (sub v) s (Nat.zero_le n)).symm)))
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf sub n s) (iha sub n s)
  | left _ ih => exact congrArg LambdaTerm.left (ih sub n s)
  | right _ ih => exact congrArg LambdaTerm.right (ih sub n s)
  | bvar _ => rfl

mutual

inductive Normal {ι : Type u} {κ : Type v} (ζ : κ → Object ι) :
    (ctx : List (Object ι)) → (typ : Object ι) → Type (max u v) where
  | ofNeutral {ctx : List (Object ι)} {t : ι} (n : Neutral ζ ctx (.of t)) : Normal ζ ctx (.of t)
  | lam {ctx : List (Object ι)} (dom : Object ι) {tb : Object ι}
    (body : Normal ζ (dom :: ctx) tb) : Normal ζ ctx (.hom dom tb)
  | unit (ctx : List (Object ι)) : Normal ζ ctx .unit
  | prod {ctx : List (Object ι)} {tl tr : Object ι}
    (left : Normal ζ ctx tl) (right : Normal ζ ctx tr) : Normal ζ ctx (.prod tl tr)

inductive Neutral {ι : Type u} {κ : Type v} (ζ : κ → Object ι) :
    (ctx : List (Object ι)) → (typ : Object ι) → Type (max u v) where
  | of (k : κ) (ctx : List (Object ι)) : Neutral ζ ctx (ζ k)
  | app {ctx : List (Object ι)} {typed typea : Object ι}
    (fn : Neutral ζ ctx (.hom typed typea)) (arg : Normal ζ ctx typed) : Neutral ζ ctx typea
  | left {ctx : List (Object ι)} {tl tr : Object ι} (tup : Neutral ζ ctx (.prod tl tr)) :
    Neutral ζ ctx tl
  | right {ctx : List (Object ι)} {tl tr : Object ι} (tup : Neutral ζ ctx (.prod tl tr)) :
    Neutral ζ ctx tr
  | bvar {ctx : List (Object ι)} (n : Nat) (typ : Object ι) (sat : typ ∈ ctx[n]?) :
    Neutral ζ ctx typ

end

mutual

def Normal.toLambdaTerm {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} (t : Normal ζ ctx typ) : LambdaTerm ι κ :=
  match t with
  | .ofNeutral n => n.toLambdaTerm
  | .lam dom body => .lam dom body.toLambdaTerm
  | .unit _ => .unit
  | .prod left right => .prod left.toLambdaTerm right.toLambdaTerm

def Neutral.toLambdaTerm {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} (t : Neutral ζ ctx typ) : LambdaTerm ι κ :=
  match t with
  | .of k _ => .of k
  | .app fn arg => .app fn.toLambdaTerm arg.toLambdaTerm
  | .left tup => .left tup.toLambdaTerm
  | .right tup => .right tup.toLambdaTerm
  | .bvar n _ _ => .bvar n

end

mutual

def Normal.toTyping {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} (t : Normal ζ ctx typ) :
    Typing ζ ctx t.toLambdaTerm typ :=
  match t with
  | .ofNeutral n => n.toTyping
  | .lam dom body => .lam body.toTyping
  | .unit ctx => .unit ctx
  | .prod left right => .prod left.toTyping right.toTyping

def Neutral.toTyping {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} (t : Neutral ζ ctx typ) :
    Typing ζ ctx t.toLambdaTerm typ :=
  match t with
  | .of k ctx => .of k ctx
  | .app fn arg => .app fn.toTyping arg.toTyping
  | .left tup => .left tup.toTyping
  | .right tup => .right tup.toTyping
  | .bvar n typ sat => .bvar n typ sat

end

def RConv {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} {t : LambdaTerm ι κ} (satt : Typing ζ ctx t tt) : Type (max u v) :=
  match tt with
  | .of i => { c : Normal ζ ctx (.of i) // Convertible satt c.toTyping ∧
    ∀ d : Normal ζ ctx (.of i), Convertible satt d.toTyping → c = d}
  | .unit => PUnit
  | .prod _ _ => RConv (.left satt) × RConv (.right satt)
  | .hom s _ => ∀ (a : LambdaTerm ι κ) (sata : Typing ζ ctx a s),
    RConv sata → RConv (.app satt sata)

def RConv.congr {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} {t₁ t₂ : LambdaTerm ι κ} {satt₁ : Typing ζ ctx t₁ tt}
    {satt₂ : Typing ζ ctx t₂ tt} (conv : Convertible satt₁ satt₂) (rc : RConv satt₁) :
    RConv satt₂ :=
  match tt with
  | .of _ => ⟨rc.1, conv.symm.trans rc.2.1, fun d hd => rc.2.2 d (conv.trans hd)⟩
  | .unit => rc
  | .prod _ _ => (rc.1.congr (.congr_left conv), rc.2.congr (.congr_right conv))
  | .hom _ _ => fun a sata ra => (rc a sata ra).congr (.congr_app conv (.refl sata))

def RConv.replaceBVars {ι : Type u} {κ : Type v} [hκ : IsEmpty κ] {ζ : κ → Object ι}
    {ctx₁ ctx₂ : List (Object ι)} {sub : Nat → LambdaTerm ι κ} {tt : Object ι} {t : LambdaTerm ι κ}
    (sats : (n : Nat) → (hn : n < ctx₁.length) → Typing ζ ctx₂ (sub n) ctx₁[n])
    (satt : Typing ζ ctx₁ t tt) (rc : (n : Nat) → (hn : n < ctx₁.length) → RConv (sats n hn)) :
    RConv (satt.replaceBVars sats) :=
  match satt, hκ with
  | .unit _, _ => PUnit.unit
  | .prod satl satr, _ =>
    (.congr (.symm (.prod_left _ _)) (.replaceBVars sats satl rc),
      .congr (.symm (.prod_right _ _)) (.replaceBVars sats satr rc))
  | .lam sat, _ => fun a sata ra => .congr (.trans (.of_eq ((congrArg (LambdaTerm.replaceBVars · _)
      (funext fun n => n.casesOn rfl fun u => (instantiate_incrementBVars _ a 0).symm)).trans
        (instantiate_replaceBVars _ 0 a _).symm) _ _) (.symm (.beta _ _)))
    (@RConv.replaceBVars ι κ _ ζ (_ :: ctx₁) ctx₂ (fun n => n.casesOn a sub) _ _
      (fun n => n.casesOn (fun _ => sata) (fun u hu => sats u (Nat.lt_of_succ_lt_succ hu)))
      sat (fun n => n.casesOn (fun _ => ra) (fun u hu => rc u (Nat.lt_of_succ_lt_succ hu))))
  | .app satd sata, _ =>
    RConv.replaceBVars sats satd rc _ (sata.replaceBVars sats) (RConv.replaceBVars sats sata rc)
  | .left sat, _ => (RConv.replaceBVars sats sat rc).fst
  | .right sat, _ => (RConv.replaceBVars sats sat rc).snd
  | .bvar deBruijnIndex type sat, _ =>
    Eq.rec (motive := fun _ h => RConv (h ▸ sats deBruijnIndex (by grind)))
      (rc deBruijnIndex (by grind)) (Option.mem_some.1 (List.getElem?_eq_getElem
        (show deBruijnIndex < ctx₁.length by grind) ▸ sat))

end Mathlib.Tactic.CCC

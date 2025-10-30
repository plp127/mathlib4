/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.CCC.Lambda.Basic


-- following https://www.cs.ru.nl/masters-theses/2024/B_Kocsis___Normalization_for_the_simply_typed_%CE%BB-calculus.pdf

universe u v w

def Nat.cycleIcc (i j : Nat) : Equiv.Perm Nat where
  toFun k := if k < i then k else if k < j then k + 1 else if k = j then i else k
  invFun k := if j < k then k else if i < k then k - 1 else if k = i then j else k
  left_inv _ := by dsimp; split_ifs <;> omega
  right_inv _ := by dsimp; split_ifs <;> omega

theorem Nat.cycleIcc_apply (i j k : Nat) : Nat.cycleIcc i j k =
    if k < i then k else if k < j then k + 1 else if k = j then i else k := rfl

theorem Nat.cycleIcc_symm_apply (i j k : Nat) : (Nat.cycleIcc i j).symm k =
    if j < k then k else if i < k then k - 1 else if k = i then j else k := rfl

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

@[simp]
theorem replaceBVars_bvar {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ) :
    t.replaceBVars .bvar = t := by
  induction t with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod ihl ihr
  | lam dom body ih =>
    exact congrArg (LambdaTerm.lam dom) (.trans (congrArg body.replaceBVars (funext fun n =>
      n.casesOn rfl fun u => if_pos (Nat.zero_le u))) ih)
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app ihf iha
  | left _ ih => exact congrArg LambdaTerm.left ih
  | right _ ih => exact congrArg LambdaTerm.right ih
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

theorem replaceBVars_instantiate {ι : Type u} {κ : Type v} (sub : Nat → LambdaTerm ι κ)
    (n : Nat) (s t : LambdaTerm ι κ) : (t.instantiate n s).replaceBVars sub =
      t.replaceBVars fun k => ((LambdaTerm.bvar k).instantiate n s).replaceBVars sub := by
  induction t generalizing sub n s with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl sub n s) (ihr sub n s)
  | lam dom body ih =>
    exact congrArg (LambdaTerm.lam dom) ((ih _ (n + 1) (s.incrementBVars 0)).trans
      (congrArg (fun sub ↦ LambdaTerm.replaceBVars sub body) (funext fun u ↦ Nat.casesOn u
        (by simp) fun v ↦ ((congrArg (LambdaTerm.replaceBVars _)
          ((incrementBVars_instantiate_of_ge (.bvar v) s (Nat.zero_le n)).trans
            (congrArg (LambdaTerm.instantiate · (n + 1) _) (if_pos (Nat.zero_le v)))).symm).trans
              (replaceBVars_incrementBVars _ 0 _)).trans
          (incrementBVars_replaceBVars sub 0 _).symm)))
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf sub n s) (iha sub n s)
  | left _ ih => exact congrArg LambdaTerm.left (ih sub n s)
  | right _ ih => exact congrArg LambdaTerm.right (ih sub n s)
  | bvar _ => simp [apply_ite (LambdaTerm.replaceBVars sub)]

theorem incrementBVars_eq_replaceBVars {ι : Type u} {κ : Type v}
    (n : Nat) (t : LambdaTerm ι κ) : t.incrementBVars n =
      t.replaceBVars fun m => if n ≤ m then .bvar (m + 1) else .bvar m := by
  induction t generalizing n with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl n) (ihr n)
  | lam dom body ih =>
    rw [LambdaTerm.incrementBVars, ih, LambdaTerm.replaceBVars]
    apply congrArg (LambdaTerm.lam dom <| body.replaceBVars ·) (funext fun m => ?_)
    cases m with
    | zero => rfl
    | succ m => simp [apply_ite]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf n) (iha n)
  | left _ ih => exact congrArg LambdaTerm.left (ih n)
  | right _ ih => exact congrArg LambdaTerm.right (ih n)
  | bvar _ => rfl

theorem replaceBVars_congr_left_of_typing {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {sub₁ sub₂ : Nat → LambdaTerm ι κ} {tt : Object ι} {t : LambdaTerm ι κ}
    (satt : Typing ζ ctx t tt) (cong : ∀ n < ctx.length, sub₁ n = sub₂ n) :
    t.replaceBVars sub₁ = t.replaceBVars sub₂ := by
  induction satt generalizing sub₁ sub₂ with
  | of k ctx => rfl
  | unit ctx => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl cong) (ihr cong)
  | lam _ ih => exact congrArg (LambdaTerm.lam _) (ih fun n => n.casesOn (fun _ => rfl)
    (fun u hu => congrArg (LambdaTerm.incrementBVars 0) (cong u (Nat.lt_of_succ_lt_succ hu))))
  | app _ _ ihd iha => exact congrArg₂ LambdaTerm.app (ihd cong) (iha cong)
  | left _ ih => exact congrArg LambdaTerm.left (ih cong)
  | right _ ih => exact congrArg LambdaTerm.right (ih cong)
  | bvar deBruijnIndex _ _ => exact cong deBruijnIndex (by grind)

def Convertible.congr_replaceBVars_right {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx₁ ctx₂ : List (Object ι)} {sub : Nat → LambdaTerm ι κ}
    {tt : Object ι} {t₁ t₂ : LambdaTerm ι κ}
    (sats : (n : Nat) → (hn : n < ctx₁.length) → Typing ζ ctx₂ (sub n) ctx₁[n])
    (satt₁ : Typing ζ ctx₁ t₁ tt) (satt₂ : Typing ζ ctx₁ t₂ tt) (conv : Convertible satt₁ satt₂) :
    Convertible (satt₁.replaceBVars sats) (satt₂.replaceBVars sats) := by
  induction conv generalizing sub ctx₂ with
  | refl sat => exact .refl (sat.replaceBVars sats)
  | symm _ ih => exact (ih sats).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ sats).trans (ih₂ sats)
  | congr_prod _ _ ihl ihr => exact .congr_prod (ihl sats) (ihr sats)
  | congr_lam _ ih => exact .congr_lam (ih _)
  | congr_app _ _ ihf iha => exact .congr_app (ihf sats) (iha sats)
  | congr_left _ ih => exact .congr_left (ih sats)
  | congr_right _ ih => exact .congr_right (ih sats)
  | unit_eta sat => exact .unit_eta (sat.replaceBVars sats)
  | prod_eta sat => exact .prod_eta (sat.replaceBVars sats)
  | prod_left satl satr => exact .prod_left (satl.replaceBVars sats) (satr.replaceBVars sats)
  | prod_right satl satr => exact .prod_right (satl.replaceBVars sats) (satr.replaceBVars sats)
  | lam_eta sat =>
    exact .trans (.lam_eta _) (.of_eq (congrArg (LambdaTerm.lam _ <| .app · (.bvar 0))
      ((incrementBVars_replaceBVars sub 0 _).trans
        (.symm (replaceBVars_incrementBVars _ 0 _)))) _ _)
  | beta satb sata =>
    refine .trans (.beta _ _) (.of_eq ?_ _ _)
    rw [instantiate_replaceBVars, replaceBVars_instantiate]
    refine congrArg (LambdaTerm.replaceBVars · _) (funext fun n => n.casesOn rfl fun u => ?_)
    simp

@[simp]
def LambdaTerm.replace {ι : Type u} {κ : Type v}
    (subf : κ → LambdaTerm ι κ) (subb : Nat → LambdaTerm ι κ)
    (t : LambdaTerm ι κ) : LambdaTerm ι κ :=
  match t with
  | .of k => subf k
  | .unit => .unit
  | .prod l r => .prod (l.replace subf subb) (r.replace subf subb)
  | .lam dom body => .lam dom (body.replace
    (fun k => (subf k).incrementBVars 0)
    (fun n => n.casesOn (.bvar 0) fun u => (subb u).incrementBVars 0))
  | .app fn arg => .app (fn.replace subf subb) (arg.replace subf subb)
  | .left tup => .left (tup.replace subf subb)
  | .right tup => .right (tup.replace subf subb)
  | .bvar deBruijnIndex => subb deBruijnIndex

@[simp]
def Typing.replace {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx₁ ctx₂ : List (Object ι)}
    {subf : κ → LambdaTerm ι κ} {subb : Nat → LambdaTerm ι κ} {tt : Object ι} {t : LambdaTerm ι κ}
    (satf : (k : κ) → Typing ζ ctx₂ (subf k) (ζ k))
    (sats : (n : Nat) → (hn : n < ctx₁.length) → Typing ζ ctx₂ (subb n) ctx₁[n])
    (satt : Typing ζ ctx₁ t tt) : Typing ζ ctx₂ (t.replace subf subb) tt :=
  match satt with
  | .of k _ => satf k
  | .unit _ => .unit ctx₂
  | .prod satl satr => .prod (satl.replace satf sats) (satr.replace satf sats)
  | .lam sat => .lam (sat.replace
    (fun k => (satf k).incrementBVars [] _ 0 (Eq.refl 0))
    (fun n => n.casesOn
      (fun hn => .bvar 0 _ (Option.mem_some_self _))
      (fun n hn => (sats n (Nat.lt_of_succ_lt_succ hn)).incrementBVars [] _ 0 (Eq.refl 0))))
  | .app satd sata => .app (satd.replace satf sats) (sata.replace satf sats)
  | .left sat => .left (sat.replace satf sats)
  | .right sat => .right (sat.replace satf sats)
  | .bvar deBruijnIndex type sat =>
    Option.mem_some.1 (List.getElem?_eq_getElem _ ▸ sat) ▸ sats deBruijnIndex (by grind)

theorem instantiate_replace {ι : Type u} {κ : Type v} (subf : κ → LambdaTerm ι κ)
    (subb : Nat → LambdaTerm ι κ) (n : Nat) (s t : LambdaTerm ι κ) :
    (t.replace subf subb).instantiate n s =
      t.replace (fun k => (subf k).instantiate n s) fun k => (subb k).instantiate n s := by
  induction t generalizing subf subb n s with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl subf subb n s) (ihr subf subb n s)
  | lam dom body ih =>
    refine congrArg (LambdaTerm.lam dom) ((ih _ _ (n + 1) (s.incrementBVars 0)).trans ?_)
    refine congrArg₂ (fun f b => body.replace f b) ?_ ?_
    · funext k
      rw [← incrementBVars_instantiate_of_ge _ _ (Nat.zero_le n)]
    · funext k
      cases k
      · simp
      · rw [← incrementBVars_instantiate_of_ge _ _ (Nat.zero_le n)]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf subf subb n s) (iha subf subb n s)
  | left _ ih => exact congrArg LambdaTerm.left (ih subf subb n s)
  | right _ ih => exact congrArg LambdaTerm.right (ih subf subb n s)
  | bvar _ => rfl

theorem replace_of_bvar {ι : Type u} {κ : Type v}
    (t : LambdaTerm ι κ) : t.replace .of .bvar = t := by
  induction t with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod ihl ihr
  | lam dom body ih => exact congrArg (LambdaTerm.lam dom) (.trans (congrArg (body.replace .of ·)
    (funext fun n => n.casesOn rfl fun k => if_pos (Nat.zero_le k))) ih)
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app ihf iha
  | left _ ih => exact congrArg LambdaTerm.left ih
  | right _ ih => exact congrArg LambdaTerm.right ih
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

mutual

theorem Normal.toLambdaTerm_injective {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} : (@Normal.toLambdaTerm ι κ ζ ctx typ).Injective :=
  fun a b hab =>
    match a, b with
    | .ofNeutral _, .ofNeutral _ =>
      congrArg Normal.ofNeutral (Neutral.toLambdaTerm_injective hab)
    | .lam _ _, .lam _ _ =>
      congrArg (Normal.lam _) (Normal.toLambdaTerm_injective (LambdaTerm.lam.inj hab).2)
    | .unit _, .unit _ => rfl
    | .prod _ _, .prod _ _ =>
      congrArg₂ Normal.prod
        (Normal.toLambdaTerm_injective (LambdaTerm.prod.inj hab).1)
        (Normal.toLambdaTerm_injective (LambdaTerm.prod.inj hab).2)

theorem Neutral.toLambdaTerm_injective {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} : (@Neutral.toLambdaTerm ι κ ζ ctx typ).Injective :=
  fun a b hab =>
    match typ, a with
    | _, .of k₁ _ => sorry
    | _, .app fn₁ arg₁ =>
      match b with
      | .app fn₂ arg₂ => by
        stop
        cases Neutral.toLambdaTerm_injective (LambdaTerm.app.inj hab).1
        cases Normal.toLambdaTerm_injective (LambdaTerm.app.inj hab).2
    | _, .left _ =>
      match b with
      | .left _ => sorry
    | _, .right _ =>
      match b with
      | .right _ => sorry
    | _, .bvar _ _ _ =>
      match b with
      | .bvar _ _ _ => by cases hab; rfl

end

mutual

def Normal.incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι} (tot app : List (Object ι))
    {ctx : List (Object ι)} (tu : Object ι) {typ : Object ι} (t : Normal ζ tot typ)
    (n : Nat) (hn : app.length = n) (tt : app ++ ctx = tot) : Normal ζ (app ++ tu :: ctx) typ :=
  match t with
  | .ofNeutral nt => .ofNeutral (nt.incrementBVars tot app tu n hn tt)
  | .lam dom body => .lam dom (body.incrementBVars (dom :: tot) (dom :: app) tu
    (n + 1) (congrArg Nat.succ hn) (congrArg (List.cons dom) tt))
  | .unit _ => .unit _
  | .prod left right =>
    .prod (left.incrementBVars tot app tu n hn tt) (right.incrementBVars tot app tu n hn tt)

def Neutral.incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (tot app : List (Object ι)) {ctx : List (Object ι)} (tu : Object ι) {typ : Object ι}
    (t : Neutral ζ tot typ) (n : Nat) (hn : app.length = n) (tt : app ++ ctx = tot) :
    Neutral ζ (app ++ tu :: ctx) typ :=
  match t with
  | .of k _ => .of k _
  | .app fn arg =>
    .app (fn.incrementBVars tot app tu n hn tt) (arg.incrementBVars tot app tu n hn tt)
  | .left tup => .left (tup.incrementBVars tot app tu n hn tt)
  | .right tup => .right (tup.incrementBVars tot app tu n hn tt)
  | .bvar m typ _ => if _ : n ≤ m then .bvar (m + 1) typ (by grind) else .bvar m typ (by grind)

end

mutual

theorem Normal.toLambdaTerm_incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (tot app : List (Object ι)) {ctx : List (Object ι)} (tu : Object ι) {typ : Object ι}
    (t : Normal ζ tot typ) (n : Nat) (hn : app.length = n) (tt : app ++ ctx = tot) :
    (t.incrementBVars tot app tu n hn tt).toLambdaTerm = t.toLambdaTerm.incrementBVars n :=
  match t with
  | .ofNeutral nt => nt.toLambdaTerm_incrementBVars tot app tu n hn tt
  | .lam dom body => congrArg (LambdaTerm.lam dom)
    (body.toLambdaTerm_incrementBVars (dom :: tot) (dom :: app) tu
      (n + 1) (congrArg Nat.succ hn) (congrArg (List.cons dom) tt))
  | .unit _ => rfl
  | .prod left right => congrArg₂ LambdaTerm.prod
    (left.toLambdaTerm_incrementBVars tot app tu n hn tt)
    (right.toLambdaTerm_incrementBVars tot app tu n hn tt)

theorem Neutral.toLambdaTerm_incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (tot app : List (Object ι)) {ctx : List (Object ι)} (tu : Object ι) {typ : Object ι}
    (t : Neutral ζ tot typ) (n : Nat) (hn : app.length = n) (tt : app ++ ctx = tot) :
    (t.incrementBVars tot app tu n hn tt).toLambdaTerm = t.toLambdaTerm.incrementBVars n :=
  match t with
  | .of k _ => rfl
  | .app fn arg => congrArg₂ LambdaTerm.app
    (fn.toLambdaTerm_incrementBVars tot app tu n hn tt)
    (arg.toLambdaTerm_incrementBVars tot app tu n hn tt)
  | .left tup => congrArg LambdaTerm.left (tup.toLambdaTerm_incrementBVars tot app tu n hn tt)
  | .right tup => congrArg LambdaTerm.right (tup.toLambdaTerm_incrementBVars tot app tu n hn tt)
  | .bvar m typ _ => by
    simp [Neutral.incrementBVars, apply_dite Neutral.toLambdaTerm, Neutral.toLambdaTerm]

end

mutual

def Normal.replaceBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx₁ ctx₂ : List (Object ι)}
    (sub : (n : Nat) → (hn : n < ctx₁.length) → Neutral ζ ctx₂ ctx₁[n]) {tt : Object ι}
    (t : Normal ζ ctx₁ tt) : Normal ζ ctx₂ tt :=
  match t with
  | .ofNeutral n => .ofNeutral (n.replaceBVars sub)
  | .lam dom body => .lam dom (body.replaceBVars fun n =>
    n.casesOn (fun _ => .bvar 0 dom (Option.mem_some_self dom)) (fun u hu =>
      (sub u (Nat.lt_of_succ_lt_succ hu)).incrementBVars ctx₂ [] dom 0 (Eq.refl 0) rfl))
  | .unit _ => .unit ctx₂
  | .prod left right => .prod (left.replaceBVars sub) (right.replaceBVars sub)

def Neutral.replaceBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx₁ ctx₂ : List (Object ι)}
    (sub : (n : Nat) → (hn : n < ctx₁.length) → Neutral ζ ctx₂ ctx₁[n]) {tt : Object ι}
    (t : Neutral ζ ctx₁ tt) : Neutral ζ ctx₂ tt :=
  match t with
  | .of k _ => .of k ctx₂
  | .app fn arg => .app (fn.replaceBVars sub) (arg.replaceBVars sub)
  | .left tup => .left (tup.replaceBVars sub)
  | .right tup => .right (tup.replaceBVars sub)
  | .bvar n typ sat => Option.mem_some.1 (List.getElem?_eq_getElem _ ▸ sat) ▸ sub n (by grind)

end

mutual

theorem Normal.toLambdaTerm_replaceBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx₁ ctx₂ : List (Object ι)} (sub : Nat → LambdaTerm ι κ)
    (subn : (n : Nat) → (hn : n < ctx₁.length) → Neutral ζ ctx₂ ctx₁[n])
    {tt : Object ι} (ss : ∀ n hn, (subn n hn).toLambdaTerm = sub n) (t : Normal ζ ctx₁ tt) :
    (t.replaceBVars subn).toLambdaTerm = t.toLambdaTerm.replaceBVars sub :=
  match t with
  | .ofNeutral n => n.toLambdaTerm_replaceBVars sub subn ss
  | .lam dom body => congrArg (LambdaTerm.lam dom)
    (body.toLambdaTerm_replaceBVars _ _ fun n =>
      n.casesOn (fun _ => rfl) (fun u hu =>
        (Neutral.toLambdaTerm_incrementBVars ctx₂ [] dom (subn u (Nat.lt_of_succ_lt_succ hu))
          0 (Eq.refl 0) rfl).trans (congrArg (LambdaTerm.incrementBVars 0)
            (ss u (Nat.lt_of_succ_lt_succ hu)))))
  | .unit _ => rfl
  | .prod left right => congrArg₂ LambdaTerm.prod
    (left.toLambdaTerm_replaceBVars sub subn ss)
    (right.toLambdaTerm_replaceBVars sub subn ss)

theorem Neutral.toLambdaTerm_replaceBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx₁ ctx₂ : List (Object ι)} (sub : Nat → LambdaTerm ι κ)
    (subn : (n : Nat) → (hn : n < ctx₁.length) → Neutral ζ ctx₂ ctx₁[n])
    {tt : Object ι} (ss : ∀ n hn, (subn n hn).toLambdaTerm = sub n) (t : Neutral ζ ctx₁ tt) :
    (t.replaceBVars subn).toLambdaTerm = t.toLambdaTerm.replaceBVars sub :=
  match t with
  | .of k _ => rfl
  | .app fn arg => congrArg₂ LambdaTerm.app
    (fn.toLambdaTerm_replaceBVars sub subn ss)
    (arg.toLambdaTerm_replaceBVars sub subn ss)
  | .left tup => congrArg LambdaTerm.left (tup.toLambdaTerm_replaceBVars sub subn ss)
  | .right tup => congrArg LambdaTerm.right (tup.toLambdaTerm_replaceBVars sub subn ss)
  | .bvar m typ sat => by
    have hm : m < ctx₁.length := by grind
    obtain rfl : ctx₁[m] = typ := Option.mem_some.1 (List.getElem?_eq_getElem _ ▸ sat)
    exact ss m hm

end

mutual

def Normal.extend {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    (ex : List (Object ι)) {tt : Object ι} (t : Normal ζ ctx tt) : Normal ζ (ctx ++ ex) tt :=
  match t with
  | .ofNeutral n => .ofNeutral (n.extend ex)
  | .lam dom body => .lam dom (body.extend ex)
  | .unit _ => .unit _
  | .prod left right => .prod (left.extend ex) (right.extend ex)

def Neutral.extend {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    (ex : List (Object ι)) {tt : Object ι} (t : Neutral ζ ctx tt) : Neutral ζ (ctx ++ ex) tt :=
  match t with
  | .of k _ => .of k _
  | .app fn arg => .app (fn.extend ex) (arg.extend ex)
  | .left tup => .left (tup.extend ex)
  | .right tup => .right (tup.extend ex)
  | .bvar n typ sat => .bvar n typ (by grind)

end

mutual

theorem Normal.toLambdaTerm_extend {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} (ex : List (Object ι)) {tt : Object ι} (t : Normal ζ ctx tt) :
    (t.extend ex).toLambdaTerm = t.toLambdaTerm :=
  match t with
  | .ofNeutral n => n.toLambdaTerm_extend ex
  | .lam dom body => congrArg (LambdaTerm.lam dom) (body.toLambdaTerm_extend ex)
  | .unit _ => rfl
  | .prod left right => congrArg₂ LambdaTerm.prod
    (left.toLambdaTerm_extend ex) (right.toLambdaTerm_extend ex)

theorem Neutral.toLambdaTerm_extend {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} (ex : List (Object ι)) {tt : Object ι} (t : Neutral ζ ctx tt) :
    (t.extend ex).toLambdaTerm = t.toLambdaTerm :=
  match t with
  | .of _ _ => rfl
  | .app fn arg => congrArg₂ LambdaTerm.app
    (fn.toLambdaTerm_extend ex) (arg.toLambdaTerm_extend ex)
  | .left tup => congrArg LambdaTerm.left (tup.toLambdaTerm_extend ex)
  | .right tup => congrArg LambdaTerm.right (tup.toLambdaTerm_extend ex)
  | .bvar _ _ _ => rfl

end

mutual

def Normal.replace {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx₁ ctx₂ : List (Object ι)}
    (subf : (k : κ) → Neutral ζ ctx₂ (ζ k))
    (subb : (n : Nat) → (hn : n < ctx₁.length) → Neutral ζ ctx₂ ctx₁[n]) {tt : Object ι}
    (t : Normal ζ ctx₁ tt) : Normal ζ ctx₂ tt :=
  match t with
  | .ofNeutral n => .ofNeutral (n.replace subf subb)
  | .lam dom body => .lam dom (body.replace
    (fun k => (subf k).incrementBVars ctx₂ [] dom 0 (Eq.refl 0) rfl)
    (fun n => n.casesOn (fun _ => .bvar 0 dom (Option.mem_some_self dom)) (fun u hu =>
      (subb u (Nat.lt_of_succ_lt_succ hu)).incrementBVars ctx₂ [] dom 0 (Eq.refl 0) rfl)))
  | .unit _ => .unit ctx₂
  | .prod left right => .prod (left.replace subf subb) (right.replace subf subb)

def Neutral.replace {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx₁ ctx₂ : List (Object ι)}
    (subf : (k : κ) → Neutral ζ ctx₂ (ζ k))
    (subb : (n : Nat) → (hn : n < ctx₁.length) → Neutral ζ ctx₂ ctx₁[n]) {tt : Object ι}
    (t : Neutral ζ ctx₁ tt) : Neutral ζ ctx₂ tt :=
  match t with
  | .of k _ => subf k
  | .app fn arg => .app (fn.replace subf subb) (arg.replace subf subb)
  | .left tup => .left (tup.replace subf subb)
  | .right tup => .right (tup.replace subf subb)
  | .bvar n typ sat => Option.mem_some.1 (List.getElem?_eq_getElem _ ▸ sat) ▸ subb n (by grind)

end

def RConv {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} {t : LambdaTerm ι κ} (satt : Typing ζ ctx t tt) : Type (max u v) :=
  match tt with
  | .of i => { c : Normal ζ ctx (.of i) // Convertible satt c.toTyping}
  | .unit => PUnit
  | .prod _ _ => RConv (.left satt) × RConv (.right satt)
  | .hom s _ => ∀ (ex : List (Object ι)) (a : LambdaTerm ι κ) (sata : Typing ζ (ctx ++ ex) a s),
    RConv sata → RConv (.app (satt.extend ex) sata)

def RConv.congr {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} {t₁ t₂ : LambdaTerm ι κ} {satt₁ : Typing ζ ctx t₁ tt}
    {satt₂ : Typing ζ ctx t₂ tt} (conv : Convertible satt₁ satt₂) (rc : RConv satt₁) :
    RConv satt₂ :=
  match tt with
  | .of _ => ⟨rc.1, conv.symm.trans rc.2⟩
  | .unit => rc
  | .prod _ _ => (rc.1.congr (.congr_left conv), rc.2.congr (.congr_right conv))
  | .hom _ _ => fun ex a sata ra => (rc ex a sata ra).congr
    (.congr_app (.congr_extend ex conv) (.refl sata))

def RConv.replaceBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx₁ ctx₂ : List (Object ι)} {subh subi : Nat → Nat} {tt : Object ι} {t : LambdaTerm ι κ}
    (sath : ∀ (n : Nat) (hn : n < ctx₁.length), ctx₁[n] ∈ ctx₂[subh n]?)
    (sati : ∀ (n : Nat) (hn : n < ctx₂.length), ctx₂[n] ∈ ctx₁[subi n]?)
    (ih : ∀ n < ctx₁.length, subi (subh n) = n) (hi : ∀ n < ctx₂.length, subh (subi n) = n)
    (satt : Typing ζ ctx₁ t tt) (rc : RConv satt) :
    RConv (satt.replaceBVars (fun n hn => .bvar (subh n) ctx₁[n] (sath n hn))) :=
  match tt with
  | .of i => ⟨rc.1.replaceBVars fun n hn => .bvar (subh n) ctx₁[n] (sath n hn),
    .trans (.congr_replaceBVars_right _ satt _ rc.2) (.of_eq
      (rc.1.toLambdaTerm_replaceBVars _ _ fun _ _ => rfl).symm _ _)⟩
  | .unit => rc
  | .prod left right =>
    (rc.1.replaceBVars sath sati ih hi, rc.2.replaceBVars sath sati ih hi)
  | .hom source target => fun ex a sata ra => by
    letI ubh (n : Nat) : Nat := if n < ctx₁.length then subh n else n - ctx₁.length + ctx₂.length
    letI ubi (n : Nat) : Nat := if n < ctx₂.length then subi n else n - ctx₂.length + ctx₁.length
    haveI ath (n : Nat) (hn : n < (ctx₁ ++ ex).length) :
        (ctx₁ ++ ex)[n] ∈ (ctx₂ ++ ex)[ubh n]? := by
      unfold ubh
      rw [List.getElem_append]
      split_ifs with h
      · rw [List.getElem?_append_left (by grind)]
        exact sath n h
      · rw [List.getElem?_append_right (by grind)]
        simp
    haveI ati (n : Nat) (hn : n < (ctx₂ ++ ex).length) :
        (ctx₂ ++ ex)[n] ∈ (ctx₁ ++ ex)[ubi n]? := by
      unfold ubi
      rw [List.getElem_append]
      split_ifs with h
      · rw [List.getElem?_append_left (by grind)]
        exact sati n h
      · rw [List.getElem?_append_right (by grind)]
        simp
    haveI sih (n : Nat) (hn : n < (ctx₁ ++ ex).length) : ubi (ubh n) = n := by
      unfold ubh ubi
      by_cases h : n < ctx₁.length
      · rw [if_pos h, if_pos (by grind), ih n h]
      · rw [if_neg h, if_neg (by grind),
          Nat.add_sub_cancel, Nat.sub_add_cancel (Nat.le_of_not_lt h)]
    haveI shi (n : Nat) (hn : n < (ctx₂ ++ ex).length) : ubh (ubi n) = n := by
      unfold ubh ubi
      by_cases h : n < ctx₂.length
      · rw [if_pos h, if_pos (by grind), hi n h]
      · rw [if_neg h, if_neg (by grind),
          Nat.add_sub_cancel, Nat.sub_add_cancel (Nat.le_of_not_lt h)]
    refine .congr (.of_eq (congrArg₂ LambdaTerm.app ?_ (.trans ?_ (replaceBVars_bvar a))) _ _)
      ((rc ex (a.replaceBVars fun n => .bvar (ubi n))
        (sata.replaceBVars fun n hn => .bvar _ _ (ati n hn))
        (ra.replaceBVars ati ath shi sih sata)).replaceBVars ath ati sih shi _)
    · apply replaceBVars_congr_left_of_typing satt
      intro n hn
      unfold ubh
      rw [if_pos hn]
    · rw [replaceBVars_replaceBVars]
      apply replaceBVars_congr_left_of_typing sata
      intro n hn
      simp [shi n hn]

def RConv.extend {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    (ex : List (Object ι)) {tt : Object ι} {t : LambdaTerm ι κ}
    {satt : Typing ζ ctx t tt} (rc : RConv satt) : RConv (satt.extend ex) :=
  match tt with
  | .of i => ⟨rc.1.extend ex, .trans (.congr_extend ex rc.2)
    (.of_eq (rc.1.toLambdaTerm_extend ex).symm _ _)⟩
  | .unit => rc
  | .prod left right => (rc.1.extend ex, rc.2.extend ex)
  | .hom source target => fun ex' a sata ra =>
    .congr (.of_eq (.trans (replaceBVars_bvar _) (congrArg (.app t) (replaceBVars_bvar a))) _ _)
      (@RConv.replaceBVars ι κ ζ (ctx ++ (ex ++ ex')) (ctx ++ ex ++ ex') id id
        target _ (by grind) (by grind) (fun _ _ => rfl) (fun _ _ => rfl) _
        (rc (ex ++ ex') (a.replaceBVars .bvar)
          (sata.replaceBVars fun n hn => .bvar n (ctx ++ ex ++ ex')[n] (by grind))
          (ra.replaceBVars (by grind) (by grind) (fun _ _ => rfl) (fun _ _ => rfl))))

def RConv.incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι} (app : List (Object ι))
    {ctx : List (Object ι)} (tu : Object ι) {tt : Object ι} {t : LambdaTerm ι κ}
    {satt : Typing ζ (app ++ ctx) t tt} (rc : RConv satt) (n : Nat) (hn : app.length = n) :
    RConv (satt.incrementBVars app tu n hn) :=
  match tt with
  | .of i => ⟨rc.1.incrementBVars (app ++ ctx) app tu n hn rfl,
    .trans (.congr_incrementBVars app rc.2 n hn)
      (.of_eq (rc.1.toLambdaTerm_incrementBVars (app ++ ctx) app tu n hn rfl).symm _ _)⟩
  | .unit => rc
  | .prod left right => (rc.1.incrementBVars app tu n hn, rc.2.incrementBVars app tu n hn)
  | .hom source target => fun ex a sata ra =>
    letI uf := ⇑(Nat.cycleIcc app.length (app.length + ctx.length))
    letI ui := ⇑(Nat.cycleIcc app.length (app.length + ctx.length)).symm
    haveI sf (k : ℕ) (hk : k < (app ++ ctx ++ tu :: ex).length) :
        (app ++ ctx ++ tu :: ex)[k] ∈ (app ++ tu :: ctx ++ ex)[uf k]? := by
      simp_rw [uf, Nat.cycleIcc_apply]
      simp only [List.getElem_append, List.getElem_cons]
      simp only [List.getElem?_append, List.getElem?_cons]
      by_cases hka : k < app.length
      · simp [hka, Nat.lt_add_right]
      have uk : ¬k + 1 < app.length := by omega
      by_cases hkc : k < app.length + ctx.length
      · simp [hka, hkc, ← Nat.add_assoc, uk, Nat.sub_eq_zero_iff_le,
          Nat.sub_add_comm (Nat.le_of_not_lt hka)]
      by_cases hkk : k = app.length + ctx.length
      · simp [hka, ← hkk]
      have vk : app.length + ctx.length < k := by omega
      simp [hka, hkc, hkk, Nat.sub_eq_zero_iff_le, ← Nat.add_assoc, Nat.not_le_of_lt vk,
        Nat.not_lt_of_le (Nat.add_one_le_of_lt vk),
        Nat.sub_add_eq k (app.length + ctx.length) 1]
    haveI si (k : ℕ) (hk : k < (app ++ tu :: ctx ++ ex).length) :
        (app ++ tu :: ctx ++ ex)[k] ∈ (app ++ ctx ++ tu :: ex)[ui k]? := by
      simp_rw [ui, Nat.cycleIcc_symm_apply]
      simp only [List.getElem_append, List.getElem_cons]
      simp only [List.getElem?_append, List.getElem?_cons]
      by_cases hkac : app.length + ctx.length < k
      · simp [hkac, Nat.lt_asymm, Nat.sub_eq_zero_iff_le, Nat.not_le_of_lt,
          ← Nat.add_assoc, Nat.lt_add_one_iff, Nat.sub_add_eq k (app.length + ctx.length) 1]
      by_cases hka : app.length < k
      · simp [hkac, hka, Nat.sub_lt_iff_lt_add (Nat.one_le_of_lt hka), Nat.lt_add_one_iff,
          Nat.le_of_not_lt, ← Nat.add_assoc, Nat.lt_asymm, Nat.sub_eq_zero_iff_le,
          Nat.sub_sub, Nat.add_comm 1, Nat.not_le_of_lt hka]
      by_cases hkk : k = app.length
      · have hkcl : ¬k + ctx.length < k := by omega
        simp [← hkk, hkcl]
      have vk : k < app.length := by omega
      simp [hka, hkac, hkk, vk, Nat.lt_add_right]
    .congr (.of_eq (by
        simp only [LambdaTerm.replaceBVars, replaceBVars_replaceBVars, uf, ui,
          Equiv.apply_symm_apply, replaceBVars_bvar]
        rw [incrementBVars_eq_replaceBVars]
        refine congrArg (LambdaTerm.app · a) (replaceBVars_congr_left_of_typing satt ?_)
        rw [List.length_append]
        intro k hk
        rw [Nat.cycleIcc_apply]
        split_ifs <;> first | rfl | omega) _ _)
      (@RConv.replaceBVars ι κ ζ (app ++ ctx ++ tu :: ex) (app ++ tu :: ctx ++ ex)
        uf ui target _ sf si (by simp [uf, ui]) (by simp [uf, ui]) _ (rc (tu :: ex) _ _
          (@RConv.replaceBVars ι κ ζ (app ++ tu :: ctx ++ ex) (app ++ ctx ++ tu :: ex)
            ui uf source a si sf (by simp [uf, ui]) (by simp [uf, ui]) _ ra)))

def RConv.replace {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx₁ ctx₂ : List (Object ι)} {subf : κ → LambdaTerm ι κ} {subb : Nat → LambdaTerm ι κ}
    {tt : Object ι} {t : LambdaTerm ι κ} (satf : (k : κ) → Typing ζ ctx₂ (subf k) (ζ k))
    (sats : (n : Nat) → (hn : n < ctx₁.length) → Typing ζ ctx₂ (subb n) ctx₁[n])
    (satt : Typing ζ ctx₁ t tt) (ru : (k : κ) → RConv (satf k))
    (rc : (n : Nat) → (hn : n < ctx₁.length) → RConv (sats n hn)) :
    RConv (satt.replace satf sats) :=
  match satt with
  | .of k _ => ru k
  | .unit _ => PUnit.unit
  | .prod satl satr =>
    (.congr (.symm (.prod_left _ _)) (.replace satf sats satl ru rc),
      .congr (.symm (.prod_right _ _)) (.replace satf sats satr ru rc))
  | .lam sat => fun ex a sata ra => by
    refine .congr (.trans (.of_eq ?_ _ _)
        (.symm (.beta _ _)))
      (@RConv.replace ι κ ζ (_ :: ctx₁) (ctx₂ ++ ex) subf
        (fun n => n.casesOn a fun u => subb u) _ _ (fun k => (satf k).extend ex)
        (fun n => n.casesOn (fun _ => sata) (fun u hu =>
          (sats u (Nat.lt_of_succ_lt_succ hu)).extend ex))
        sat (fun k => (ru k).extend ex) (fun n => n.casesOn (fun _ => ra) (fun u hu =>
          (rc u (Nat.lt_of_succ_lt_succ hu)).extend ex)))
    rw [instantiate_replace]
    refine congrArg₂ (fun f k => LambdaTerm.replace f k _) ?_ ?_
    · funext k
      rw [instantiate_incrementBVars]
    · funext k
      cases k
      · simp
      · simp
  | .app satd sata =>
    .congr (.of_eq (by simp) _ _) (@RConv.replaceBVars ι κ ζ (ctx₂ ++ []) ctx₂ id id
      tt _ (by grind) (by grind) (fun _ _ => rfl) (fun _ _ => rfl) _
      (RConv.replace satf sats satd ru rc [] _
        (sata.replace (fun k => (satf k).replaceBVars fun u hu => .bvar u ctx₂[u] (by simp))
        (fun n hn => (sats n hn).replaceBVars fun u hu => .bvar u ctx₂[u] (by simp)))
        ((RConv.replace _ _ sata (fun k => (ru k).replaceBVars (by grind) (by grind)
          (fun _ _ => rfl) (fun _ _ => rfl) _) (fun n hn => (rc n hn).replaceBVars
          (by grind) (by grind) (fun _ _ => rfl) (fun _ _ => rfl) _)))))
  | .left sat => (RConv.replace satf sats sat ru rc).fst
  | .right sat => (RConv.replace satf sats sat ru rc).snd
  | .bvar deBruijnIndex type sat =>
    Eq.rec (motive := fun _ h => RConv (h ▸ sats deBruijnIndex (by grind)))
      (rc deBruijnIndex (by grind)) (Option.mem_some.1 (List.getElem?_eq_getElem
        (show deBruijnIndex < ctx₁.length by grind) ▸ sat))

mutual

def RConv.toNormal {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} {t : LambdaTerm ι κ} {satt : Typing ζ ctx t tt} (rc : RConv satt) :
    { c : Normal ζ ctx tt // Convertible satt c.toTyping} :=
  match tt with
  | .of _ => rc
  | .unit => ⟨.unit ctx, .unit_eta satt⟩
  | .prod _ _ => ⟨.prod rc.1.toNormal.1 rc.2.toNormal.1,
    .trans (.prod_eta satt) (.congr_prod rc.1.toNormal.2 rc.2.toNormal.2)⟩
  | .hom source target => ⟨.lam source
    (@RConv.replaceBVars ι κ ζ (source :: ctx ++ []) (source :: ctx) id id
      target _ (by grind) (by grind) (fun _ _ => rfl) (fun _ _ => rfl) _
      (rc.incrementBVars [] source 0 (Eq.refl 0) [] (.bvar 0)
        (.bvar 0 source (Option.mem_some_self source))
          (.ofNeutral ⟨.bvar 0 source (Option.mem_some_self source), .refl _⟩))).toNormal.1,
    .trans (.lam_eta satt) (.congr_lam
      (.trans (.of_eq (replaceBVars_bvar _).symm _ _) (RConv.toNormal _).2))⟩

def RConv.ofNeutral {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} {t : LambdaTerm ι κ} {satt : Typing ζ ctx t tt}
    (ne : { c : Neutral ζ ctx tt // Convertible satt c.toTyping}) :
    RConv satt :=
  match tt with
  | .of _ => ⟨.ofNeutral ne.1, ne.2⟩
  | .unit => PUnit.unit
  | .prod _ _ =>
    (.ofNeutral ⟨.left ne.1, .congr_left ne.2⟩, .ofNeutral ⟨.right ne.1, .congr_right ne.2⟩)
  | .hom _ _ => fun ex _ _ ra =>
    .ofNeutral ⟨.app (ne.1.extend ex) ra.toNormal.1, .congr_app (.trans (.congr_extend ex ne.2)
      (.of_eq (ne.1.toLambdaTerm_extend ex).symm _ _)) ra.toNormal.2⟩

end

def LambdaTerm.normalize {ι : Type u} {κ : Type v} {ζ : κ → Object ι} (ctx : List (Object ι))
    (tt : Object ι) (t : LambdaTerm ι κ) (satt : Typing ζ ctx t tt) :
    { c : Normal ζ ctx tt // Convertible satt c.toTyping} :=
  RConv.toNormal (.congr (.of_eq (replace_of_bvar t) _ _) (RConv.replace (fun k => .of k ctx)
    (fun n hn => .bvar n ctx[n] (Option.mem_def.2 (List.getElem?_eq_getElem hn))) satt
      (fun k => RConv.ofNeutral ⟨.of k ctx, .refl (.of k ctx)⟩)
      (fun n hn => RConv.ofNeutral
        ⟨.bvar n ctx[n] (Option.mem_def.2 (List.getElem?_eq_getElem hn)), .refl _⟩)))

end Mathlib.Tactic.CCC

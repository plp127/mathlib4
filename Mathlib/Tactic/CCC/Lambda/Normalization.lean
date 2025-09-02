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
    sorry

def RConv.replace {ι : Type u} {κ : Type v} [hκ : IsEmpty κ] {ζ : κ → Object ι}
    {ctx₁ ctx₂ : List (Object ι)} {sub : Nat → LambdaTerm ι κ} {tt : Object ι} {t : LambdaTerm ι κ}
    (sats : (n : Nat) → (hn : n < ctx₁.length) → Typing ζ ctx₂ (sub n) ctx₁[n])
    (satt : Typing ζ ctx₁ t tt) (rc : (n : Nat) → (hn : n < ctx₁.length) → RConv (sats n hn)) :
    RConv (satt.replaceBVars sats) :=
  match satt, hκ with
  | .unit _, _ => PUnit.unit
  | .prod satl satr, _ =>
    (.congr (.symm (.prod_left _ _)) (.replace sats satl rc),
      .congr (.symm (.prod_right _ _)) (.replace sats satr rc))
  | .lam sat, _ => fun ex a sata ra => by
    refine .congr (.trans (.of_eq ?_ _ _)
        (.symm (.beta _ _)))
      (@RConv.replace ι κ _ ζ (_ :: ctx₁) (ctx₂ ++ ex)
        (fun n => n.casesOn a fun u => sub u) _ _
        (fun n => n.casesOn (fun _ => sata) (fun u hu =>
          (sats u (Nat.lt_of_succ_lt_succ hu)).extend ex))
        sat (fun n => n.casesOn (fun _ => ra) (fun u hu =>
          (rc u (Nat.lt_of_succ_lt_succ hu)).extend ex)))
    rw [instantiate_replaceBVars]
    refine congrArg (LambdaTerm.replaceBVars · _) (funext fun n => n.casesOn rfl fun u => ?_)
    simp
  | .app satd sata, _ =>
    .congr (.of_eq (by simp) _ _) (@RConv.replaceBVars ι κ ζ (ctx₂ ++ []) ctx₂ id id
      tt _ (by grind) (by grind) (fun _ _ => rfl) (fun _ _ => rfl) _
      (RConv.replace sats satd rc [] _
        (sata.replaceBVars fun n hn =>
          (sats n hn).replaceBVars fun u hu => .bvar u ctx₂[u] (by simp))
        ((RConv.replace _ sata (fun n hn => (rc n hn).replaceBVars
          (by grind) (by grind) (fun _ _ => rfl) (fun _ _ => rfl) _)))))
  | .left sat, _ => (RConv.replace sats sat rc).fst
  | .right sat, _ => (RConv.replace sats sat rc).snd
  | .bvar deBruijnIndex type sat, _ =>
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

end Mathlib.Tactic.CCC

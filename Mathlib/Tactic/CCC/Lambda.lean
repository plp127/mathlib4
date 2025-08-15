/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Data.Prod.TProd
import Mathlib.Tactic.DepRewrite

universe u v w r

def List.TProd.get {ι : Type u} {α : ι → Type v} {l : List ι}
    (t : l.TProd α) (n : Nat) (i : ι) (hi : i ∈ l[n]?) : α i :=
  match l, n, hi with
  | _ :: _, 0, rfl => t.1
  | _ :: _, n + 1, hi => List.TProd.get t.2 n i hi

def List.TProd.insert {ι : Type u} {α : ι → Type v} (app : List ι) {ctx : List ι} {tu : ι}
    (x : α tu) (t : (app ++ ctx).TProd α) : (app ++ tu :: ctx).TProd α :=
  match app with
  | [] => (x, t)
  | _ :: xs => (t.1, List.TProd.insert xs x t.2)

theorem List.TProd.get_insert_self {ι : Type u} {α : ι → Type v} (app : List ι) {ctx : List ι}
    {tu : ι} (x : α tu) (t : (app ++ ctx).TProd α) (n : Nat) (hn : app.length = n) :
    (t.insert app x).get n tu (by grind) = x := by
  subst hn
  induction app with
  | nil => rfl
  | cons i xs ih => exact ih t.2

theorem List.TProd.get_insert_of_lt {ι : Type u} {α : ι → Type v} (app : List ι) {ctx : List ι}
    {tu : ι} (x : α tu) (t : (app ++ ctx).TProd α) (n : Nat) (hn : n < app.length) {i : ι}
    (hi : i ∈ (app ++ tu :: ctx)[n]?) : (t.insert app x).get n i hi =
      t.get n i (by grind) := by
  induction app generalizing n with
  | nil => cases hn
  | cons u xs ih =>
    cases n with
    | zero => cases hi; rfl
    | succ n => exact ih t.2 n (Nat.lt_of_add_lt_add_right hn) hi

theorem List.TProd.get_insert_of_gt {ι : Type u} {α : ι → Type v} (app : List ι) {ctx : List ι}
    {tu : ι} (x : α tu) (t : (app ++ ctx).TProd α) (n : Nat) (hn : app.length < n) {i : ι}
    (hi : i ∈ (app ++ tu :: ctx)[n]?) : (t.insert app x).get n i hi =
      t.get (n - 1) i (by grind) := by
  induction app generalizing n with
  | nil =>
    cases n with
    | zero => cases hn
    | succ n => rfl
  | cons u xs ih =>
    cases n with
    | zero => cases hi; rfl
    | succ n =>
      cases n with
      | zero => simp at hn
      | succ n => exact ih t.2 (n + 1) (Nat.lt_of_add_lt_add_right hn) hi

namespace Mathlib.Tactic.CCC

inductive Object (ι : Type u) : Type u where
  | of (i : ι) : Object ι
  | unit : Object ι
  | prod (left right : Object ι) : Object ι
  | hom (source target : Object ι) : Object ι

@[simp]
def Object.read {ι : Type u} (ri : ι → Type w) (t : Object ι) : Type w :=
  match t with
  | .of i => ri i
  | .unit => PUnit
  | .prod l r => l.read ri × r.read ri
  | .hom s t => s.read ri → t.read ri

inductive LambdaTerm (ι : Type u) (κ : Type v) : Type (max u v) where
  | of (k : κ) : LambdaTerm ι κ
  | unit : LambdaTerm ι κ
  | prod (left right : LambdaTerm ι κ) : LambdaTerm ι κ
  | lam (dom : Object ι) (body : LambdaTerm ι κ) : LambdaTerm ι κ
  | app (fn arg : LambdaTerm ι κ) : LambdaTerm ι κ
  | left (tup : LambdaTerm ι κ) : LambdaTerm ι κ
  | right (tup : LambdaTerm ι κ) : LambdaTerm ι κ
  | bvar (deBruijnIndex : Nat) : LambdaTerm ι κ

inductive Typing {ι : Type u} {κ : Type v} (ζ : κ → Object ι) : (ctx : List (Object ι)) →
    (term : LambdaTerm ι κ) → (type : Object ι) → Type (max u v) where
  | of (k : κ) (ctx : List (Object ι)) : Typing ζ ctx (.of k) (ζ k)
  | unit (ctx : List (Object ι)) : Typing ζ ctx .unit .unit
  | prod {ctx : List (Object ι)}
    {left right : LambdaTerm ι κ} {typel typer : Object ι}
    (satl : Typing ζ ctx left typel) (satr : Typing ζ ctx right typer) :
    Typing ζ ctx (.prod left right) (.prod typel typer)
  | lam {ctx : List (Object ι)} {dom : Object ι}
    {body : LambdaTerm ι κ} {type : Object ι} (sat : Typing ζ (dom :: ctx) body type) :
    Typing ζ ctx (.lam dom body) (.hom dom type)
  | app {ctx : List (Object ι)}
    {fn arg : LambdaTerm ι κ} {typed typea : Object ι}
    (satd : Typing ζ ctx fn (.hom typed typea)) (sata : Typing ζ ctx arg typed) :
    Typing ζ ctx (.app fn arg) typea
  | left {ctx : List (Object ι)}
    {tup : LambdaTerm ι κ} {left right : Object ι}
    (sat : Typing ζ ctx tup (.prod left right)) :
    Typing ζ ctx (.left tup) left
  | right {ctx : List (Object ι)}
    {tup : LambdaTerm ι κ} {left right : Object ι}
    (sat : Typing ζ ctx tup (.prod left right)) :
    Typing ζ ctx (.right tup) right
  | bvar {ctx : List (Object ι)} (deBruijnIndex : Nat)
    (type : Object ι) (sat : type ∈ ctx[deBruijnIndex]?) :
    Typing ζ ctx (.bvar deBruijnIndex) type

@[simp]
def LambdaTerm.read {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (ri : ι → Type w) (rk : (k : κ) → (ζ k).read ri) (ctx : List (Object ι))
    (ci : ctx.TProd (Object.read ri)) (t : LambdaTerm ι κ) (type : Object ι)
    (sat : Typing ζ ctx t type) : type.read ri :=
  match sat with
  | .of k _ => rk k
  | .unit _ => PUnit.unit
  | .prod satl satr =>
    (LambdaTerm.read ri rk ctx ci _ _ satl, LambdaTerm.read ri rk ctx ci _ _ satr)
  | .lam sat => fun i => LambdaTerm.read ri rk (_ :: ctx) (i, ci) _ _ sat
  | .app satd sata => LambdaTerm.read ri rk ctx ci _ _ satd (LambdaTerm.read ri rk ctx ci _ _ sata)
  | .left sat => (LambdaTerm.read ri rk ctx ci _ _ sat).1
  | .right sat => (LambdaTerm.read ri rk ctx ci _ _ sat).2
  | .bvar n i sat => ci.get n i sat

theorem unique_typing {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {t : LambdaTerm ι κ}
    {type₁ : Object ι} {type₂ : Object ι}
    (typing₁ : Typing ζ ctx t type₁) (typing₂ : Typing ζ ctx t type₂) :
    type₁ = type₂ := by
  induction typing₁ generalizing type₂ with
  | of _ _ => cases typing₂; rfl
  | unit _ => cases typing₂; rfl
  | prod _ _ ih₁ ih₂ =>
    cases typing₂ with
    | prod satl satr => rw [ih₁ satl, ih₂ satr]
  | lam _ ih =>
    cases typing₂ with
    | lam sat => rw [ih sat]
  | app _ _ ih _ =>
    cases typing₂ with
    | app sat => exact (Object.hom.inj (ih sat)).right
  | left _ ih =>
    cases typing₂ with
    | left sat => exact (Object.prod.inj (ih sat)).left
  | right _ ih =>
    cases typing₂ with
    | right sat => exact (Object.prod.inj (ih sat)).right
  | bvar _ _ sat₁ =>
    cases typing₂ with
    | bvar _ _ sat₂ => exact Option.mem_unique sat₁ sat₂

instance subsingleton_typing {ι : Type u} {κ : Type v} (ζ : κ → Object ι)
    (ctx : List (Object ι)) (t : LambdaTerm ι κ) (type : Object ι) :
    Subsingleton (Typing ζ ctx t type) where
  allEq a b := by
    induction a with
    | of _ _ => cases b; rfl
    | unit _ => cases b; rfl
    | prod _ _ ihl ihr => cases b; rw [ihl, ihr]
    | lam _ ih => cases b; rw [ih]
    | app satd₁ sata₁ ihl ihr =>
      cases b with
      | app satd₂ sata₂ =>
        cases unique_typing satd₁ satd₂
        rw [ihl, ihr]
    | left sat₁ ih =>
      cases b with
      | left sat₂ =>
        cases unique_typing sat₁ sat₂
        rw [ih]
    | right sat₁ ih =>
      cases b with
      | right sat₂ =>
        cases unique_typing sat₁ sat₂
        rw [ih]
    | bvar => cases b; rfl

@[simp]
def LambdaTerm.incrementBVars {ι : Type u} {κ : Type v}
    (n : Nat) (t : LambdaTerm ι κ) : LambdaTerm ι κ :=
  match t with
  | .of k => .of k
  | .unit => .unit
  | .prod l r => .prod (l.incrementBVars n) (r.incrementBVars n)
  | .lam d b => .lam d (b.incrementBVars (n + 1))
  | .app f a => .app (f.incrementBVars n) (a.incrementBVars n)
  | .left u => .left (u.incrementBVars n)
  | .right u => .right (u.incrementBVars n)
  | .bvar m => if n ≤ m then .bvar (m + 1) else .bvar m

@[simp]
def LambdaTerm.instantiate {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ) (n : Nat)
    (s : LambdaTerm ι κ) : LambdaTerm ι κ :=
  match t with
  | .of k => .of k
  | .unit => .unit
  | .prod l r => .prod (l.instantiate n s) (r.instantiate n s)
  | .lam d b => .lam d (b.instantiate (n + 1) (s.incrementBVars 0))
  | .app f a => .app (f.instantiate n s) (a.instantiate n s)
  | .left u => .left (u.instantiate n s)
  | .right u => .right (u.instantiate n s)
  | .bvar m => if m = n then s else if n < m then .bvar (m - 1) else .bvar m

@[simp]
def Typing.incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι} (app : List (Object ι))
    {ctx : List (Object ι)} {t : LambdaTerm ι κ} {tt : Object ι} (tu : Object ι)
    (sat : Typing ζ (app ++ ctx) t tt) (n : Nat) (hn : app.length = n) :
    Typing ζ (app ++ tu :: ctx) (t.incrementBVars n) tt :=
  match sat with
  | .of k _ => .of k _
  | .unit _ => .unit _
  | .prod l r => .prod (l.incrementBVars app tu n hn) (r.incrementBVars app tu n hn)
  | .lam b => .lam (b.incrementBVars (_ :: app) tu (n + 1) (congrArg Nat.succ hn))
  | .app f a => .app (f.incrementBVars app tu n hn) (a.incrementBVars app tu n hn)
  | .left u => .left (u.incrementBVars app tu n hn)
  | .right u => .right (u.incrementBVars app tu n hn)
  | .bvar _ _ _ => iteInduction (motive := fun i => Typing ζ (app ++ tu :: ctx) i tt)
    (fun hl => .bvar _ _ (by grind)) (fun hn => .bvar _ _ (by grind))

@[simp]
def Typing.instantiate {ι : Type u} {κ : Type v} {ζ : κ → Object ι} (app : List (Object ι))
    {ctx : List (Object ι)} {s t : LambdaTerm ι κ} {ts tt : Object ι}
    (satt : Typing ζ (app ++ ts :: ctx) t tt) (sats : Typing ζ (app ++ ctx) s ts)
    (n : Nat) (hn : app.length = n) : Typing ζ (app ++ ctx) (t.instantiate n s) tt :=
  match satt with
  | .of k _ => .of k _
  | .unit _ => .unit _
  | .prod l r => .prod (l.instantiate app sats n hn) (r.instantiate app sats n hn)
  | .lam b => .lam (b.instantiate (_ :: app) (sats.incrementBVars [] _ 0 (Eq.refl 0))
    (n + 1) (congrArg Nat.succ hn))
  | .app f a => .app (f.instantiate app sats n hn) (a.instantiate app sats n hn)
  | .left u => .left (u.instantiate app sats n hn)
  | .right u => .right (u.instantiate app sats n hn)
  | .bvar _ _ _ =>
    iteInduction (motive := fun i => Typing ζ (app ++ ctx) i tt)
      (fun hl => (show ts = tt by grind) ▸ sats)
      (fun hn => iteInduction (motive := fun i => Typing ζ (app ++ ctx) i tt)
        (fun hl => .bvar _ _ (by grind))
        (fun hl => .bvar _ _ (by grind)))

inductive Convertible {ι : Type u} {κ : Type v} {ζ : κ → Object ι} :
    {ctx : List (Object ι)} → {t₁ t₂ : LambdaTerm ι κ} → {typ : Object ι} →
    (sat₁ : Typing ζ ctx t₁ typ) → (sat₂ : Typing ζ ctx t₂ typ) → Prop where
  | refl {ctx : List (Object ι)} {t : LambdaTerm ι κ} {typ : Object ι}
    (sat : Typing ζ ctx t typ) : Convertible sat sat
  | symm {ctx : List (Object ι)} {t₁ t₂ : LambdaTerm ι κ} {typ : Object ι}
    {sat₁ : Typing ζ ctx t₁ typ} {sat₂ : Typing ζ ctx t₂ typ}
    (h : Convertible sat₁ sat₂) : Convertible sat₂ sat₁
  | trans {ctx : List (Object ι)} {t₁ t₂ t₃ : LambdaTerm ι κ} {typ : Object ι}
    {sat₁ : Typing ζ ctx t₁ typ} {sat₂ : Typing ζ ctx t₂ typ} {sat₃ : Typing ζ ctx t₃ typ}
    (h₁ : Convertible sat₁ sat₂) (h₂ : Convertible sat₂ sat₃) : Convertible sat₁ sat₃
  | congr_prod {ctx : List (Object ι)}
    {left₁ left₂ right₁ right₂ : LambdaTerm ι κ} {tl tr : Object ι}
    {satl₁ : Typing ζ ctx left₁ tl} {satl₂ : Typing ζ ctx left₂ tl}
    {satr₁ : Typing ζ ctx right₁ tr} {satr₂ : Typing ζ ctx right₂ tr}
    (hl : Convertible satl₁ satl₂) (hr : Convertible satr₁ satr₂) :
    Convertible (.prod satl₁ satr₁) (.prod satl₂ satr₂)
  | congr_lam {ctx : List (Object ι)}
    {body₁ body₂ : LambdaTerm ι κ} {dom tb : Object ι}
    {satb₁ : Typing ζ (dom :: ctx) body₁ tb} {satb₂ : Typing ζ (dom :: ctx) body₂ tb}
    (hf : Convertible satb₁ satb₂) : Convertible (.lam satb₁) (.lam satb₂)
  | congr_app {ctx : List (Object ι)} {fn₁ fn₂ arg₁ arg₂ : LambdaTerm ι κ} {td ta : Object ι}
    {satf₁ : Typing ζ ctx fn₁ (.hom td ta)} {satf₂ : Typing ζ ctx fn₂ (.hom td ta)}
    {sata₁ : Typing ζ ctx arg₁ td} {sata₂ : Typing ζ ctx arg₂ td}
    (hf : Convertible satf₁ satf₂) (ha : Convertible sata₁ sata₂) :
    Convertible (.app satf₁ sata₁) (.app satf₂ sata₂)
  | congr_left {ctx : List (Object ι)}
    {tup₁ tup₂ : LambdaTerm ι κ} {tl tr : Object ι}
    {sat₁ : Typing ζ ctx tup₁ (.prod tl tr)} {sat₂ : Typing ζ ctx tup₂ (.prod tl tr)}
    (hu : Convertible sat₁ sat₂) : Convertible (.left sat₁) (.left sat₂)
  | congr_right {ctx : List (Object ι)}
    {tup₁ tup₂ : LambdaTerm ι κ} {tl tr : Object ι}
    {sat₁ : Typing ζ ctx tup₁ (.prod tl tr)} {sat₂ : Typing ζ ctx tup₂ (.prod tl tr)}
    (hu : Convertible sat₁ sat₂) : Convertible (.right sat₁) (.right sat₂)
  | unit_eta {ctx : List (Object ι)} {t : LambdaTerm ι κ}
    (sat : Typing ζ ctx t .unit) : Convertible sat (.unit ctx)
  | prod_eta {ctx : List (Object ι)} {tup : LambdaTerm ι κ} {tl tr : Object ι}
    (sat : Typing ζ ctx tup (.prod tl tr)) : Convertible sat (.prod (.left sat) (.right sat))
  | prod_left {ctx : List (Object ι)} {left right : LambdaTerm ι κ} {tl tr : Object ι}
    (satl : Typing ζ ctx left tl) (satr : Typing ζ ctx right tr) :
    Convertible (.left (.prod satl satr)) satl
  | prod_right {ctx : List (Object ι)} {left right : LambdaTerm ι κ} {tl tr : Object ι}
    (satl : Typing ζ ctx left tl) (satr : Typing ζ ctx right tr) :
    Convertible (.right (.prod satl satr)) satr
  | lam_eta {ctx : List (Object ι)} {lam : LambdaTerm ι κ} {dom tb : Object ι}
    (sat : Typing ζ ctx lam (.hom dom tb)) :
    Convertible sat (.lam (.app (.incrementBVars [] dom sat 0 (Eq.refl 0))
      (.bvar 0 dom (Option.mem_some_self dom))))
  | beta {ctx : List (Object ι)} {body a : LambdaTerm ι κ} {td ta : Object ι}
    (satb : Typing ζ (ta :: ctx) body td) (sata : Typing ζ ctx a ta) :
    Convertible (.app (.lam satb) sata) (satb.instantiate [] sata 0 (Eq.refl 0))

attribute [refl] Convertible.refl
attribute [symm] Convertible.symm
attribute [trans] Convertible.trans

theorem Convertible.of_eq {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {t₁ t₂ : LambdaTerm ι κ} {typ : Object ι} (h : t₁ = t₂)
    (sat₁ : Typing ζ ctx t₁ typ) (sat₂ : Typing ζ ctx t₂ typ) : Convertible sat₁ sat₂ := by
  cases h
  cases Subsingleton.elim sat₁ sat₂
  rfl

theorem read_incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (ri : ι → Type w) (rk : (k : κ) → (ζ k).read ri) (app : List (Object ι))
    {ctx : List (Object ι)} (ci : (app ++ ctx).TProd (Object.read ri))
    {t : LambdaTerm ι κ} {tt : Object ι} {tu : Object ι} (x : Object.read ri tu)
    (sat : Typing ζ (app ++ ctx) t tt) (n : Nat) (hn : app.length = n) :
    (t.incrementBVars n).read ri rk (app ++ tu :: ctx) (ci.insert app x)
      tt (sat.incrementBVars app tu n hn) = t.read ri rk (app ++ ctx) ci tt sat := by
  induction t generalizing tt app n with
  | of _ => cases sat; rfl
  | unit => cases sat; rfl
  | prod _ _ ihl ihr => cases sat; exact congrArg₂ Prod.mk (ihl ..) (ihr ..)
  | lam dom _ ih =>
    cases sat with
    | lam sat =>
      exact funext fun i => ih (dom :: app) (i, ci) sat (n + 1) (congrArg Nat.succ hn)
  | app _ _ ihf iha => cases sat; exact congr (ihf ..) (iha ..)
  | left _ ih => cases sat; exact congrArg Prod.fst (ih ..)
  | right _ ih => cases sat; exact congrArg Prod.snd (ih ..)
  | bvar deBruijnIndex =>
    cases sat with
    | bvar sat =>
      dsimp only [LambdaTerm.incrementBVars, Typing.incrementBVars, LambdaTerm.read]
      by_cases hd : n ≤ deBruijnIndex
      · rewrite! (castMode := .all) [if_pos hd]
        rw [Subsingleton.elim (Eq.rec ..) (.bvar _ _ (by grind))]
        apply List.TProd.get_insert_of_gt
        exact hn.trans_lt (Nat.lt_add_one_of_le hd)
      · rewrite! (castMode := .all) [if_neg hd]
        rw [Subsingleton.elim (Eq.rec ..) (.bvar _ _ (by grind))]
        apply List.TProd.get_insert_of_lt
        exact (Nat.lt_of_not_ge hd).trans_eq hn.symm

theorem read_instantiate {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (ri : ι → Type w) (rk : (k : κ) → (ζ k).read ri) (app : List (Object ι))
    {ctx : List (Object ι)} {ci : (app ++ ctx).TProd (Object.read ri)}
    {s t : LambdaTerm ι κ} {ts tt : Object ι} (satt : Typing ζ (app ++ ts :: ctx) t tt)
    (sats : Typing ζ (app ++ ctx) s ts) (n : Nat) (hn : app.length = n) :
    (t.instantiate n s).read ri rk (app ++ ctx) ci tt (satt.instantiate app sats n hn) =
      t.read ri rk (app ++ ts :: ctx)
        (ci.insert app (s.read ri rk (app ++ ctx) ci ts sats)) tt satt := by
  induction t generalizing s tt app n with
  | of _ => cases satt; rfl
  | unit => cases satt; rfl
  | prod _ _ ihl ihr => cases satt; exact congrArg₂ Prod.mk (ihl ..) (ihr ..)
  | lam dom body ih =>
    cases satt with
    | lam sat =>
      exact funext fun i =>
        (ih (dom :: app) sat (sats.incrementBVars [] dom 0 (Eq.refl 0))
          (n + 1) (congrArg Nat.succ hn)).trans
        (congrArg
          (fun c => LambdaTerm.read ri rk (dom :: (app ++ ts :: ctx))
            (i, ci.insert app c) body _ sat)
          (read_incrementBVars ri rk [] ci i sats 0 (Eq.refl 0)))
  | app _ _ ihf iha => cases satt; exact congr (ihf ..) (iha ..)
  | left _ ih => cases satt; exact congrArg Prod.fst (ih ..)
  | right _ ih => cases satt; exact congrArg Prod.snd (ih ..)
  | bvar deBruijnIndex =>
    cases satt with
    | bvar sat =>
      dsimp only [LambdaTerm.instantiate, Typing.instantiate, LambdaTerm.read]
      symm
      by_cases hd : deBruijnIndex = n
      · rewrite! (castMode := .all) [if_pos hd]
        obtain rfl : tt = ts := by grind
        rw [Subsingleton.elim (Eq.rec ..) sats]
        apply List.TProd.get_insert_self
        exact hn.trans hd.symm
      · rewrite! (castMode := .all) [if_neg hd]
        by_cases hl : n < deBruijnIndex
        · rewrite! (castMode := .all) [if_pos hl]
          rw [Subsingleton.elim (Eq.rec ..) (.bvar _ _ (by grind))]
          apply List.TProd.get_insert_of_gt
          exact hn.trans_lt hl
        · rewrite! (castMode := .all) [if_neg hl]
          rw [Subsingleton.elim (Eq.rec ..) (.bvar _ _ (by grind))]
          apply List.TProd.get_insert_of_lt
          exact (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hl) hd).trans_eq hn.symm

theorem read_eq_of_convertible {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (ri : ι → Type w) (rk : (k : κ) → (ζ k).read ri) (ctx : List (Object ι))
    (ci : ctx.TProd (Object.read ri)) (t₁ t₂ : LambdaTerm ι κ) (type : Object ι)
    (sat₁ : Typing ζ ctx t₁ type) (sat₂ : Typing ζ ctx t₂ type) (conv : Convertible sat₁ sat₂) :
    t₁.read ri rk ctx ci type sat₁ = t₂.read ri rk ctx ci type sat₂ := by
  induction conv with
  | refl sat => rfl
  | symm _ ih => exact (ih ci).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ ci).trans (ih₂ ci)
  | congr_prod _ _ ihl ihr => exact congrArg₂ Prod.mk (ihl ci) (ihr ci)
  | congr_lam _ ih => exact funext fun x => ih (x, ci)
  | congr_app _ _ ihf iha => exact congr (ihf ci) (iha ci)
  | congr_left _ ih => exact congrArg Prod.fst (ih ci)
  | congr_right _ ih => exact congrArg Prod.snd (ih ci)
  | unit_eta _ => rfl
  | prod_eta _ => rfl
  | prod_left _ _ => rfl
  | prod_right _ _ => rfl
  | lam_eta sat =>
    exact funext fun x => congrFun (read_incrementBVars ri rk [] ci x sat 0 (Eq.refl 0)).symm x
  | beta satb sata => exact (read_instantiate ri rk [] satb sata 0 (Eq.refl 0)).symm

theorem instantiate_incrementBVars {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ)
    (s : LambdaTerm ι κ) (n : ℕ) : (t.incrementBVars n).instantiate n s = t := by
  induction t generalizing n s with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl s n) (ihr s n)
  | lam dom _ ih => exact congrArg (LambdaTerm.lam dom) (ih (s.incrementBVars 0) (n + 1))
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf s n) (iha s n)
  | left _ ih => exact congrArg LambdaTerm.left (ih s n)
  | right _ ih => exact congrArg LambdaTerm.right (ih s n)
  | bvar deBruijnIndex =>
    rw [LambdaTerm.incrementBVars]
    by_cases hn : n ≤ deBruijnIndex
    · rw [if_pos hn, LambdaTerm.instantiate, if_neg (Nat.ne_of_gt (Nat.lt_add_one_of_le hn)),
        if_pos (Nat.lt_add_one_of_le hn), Nat.add_sub_cancel]
    · rw [if_neg hn, LambdaTerm.instantiate, if_neg (Nat.ne_of_lt (Nat.lt_of_not_ge hn)),
        if_neg (mt Nat.le_of_lt hn)]

theorem incrementBVars_incrementBVars_of_ge {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ)
    {n m : ℕ} (h : m ≤ n) :
    (t.incrementBVars n).incrementBVars m =
      (t.incrementBVars m).incrementBVars (n + 1) := by
  induction t generalizing n m with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl h) (ihr h)
  | lam dom _ ih => exact congrArg (LambdaTerm.lam dom) (ih (Nat.add_le_add_right h 1))
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf h) (iha h)
  | left _ ih => exact congrArg LambdaTerm.left (ih h)
  | right _ ih => exact congrArg LambdaTerm.right (ih h)
  | bvar deBruijnIndex =>
    simp only [LambdaTerm.incrementBVars, apply_ite (LambdaTerm.incrementBVars _)]
    grind

theorem incrementBVars_instantiate_of_le {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ)
    (s : LambdaTerm ι κ) {n m : ℕ} (h : n ≤ m) :
    (t.instantiate n s).incrementBVars m =
      (t.incrementBVars (m + 1)).instantiate n (s.incrementBVars m) := by
  induction t generalizing n m s with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl s h) (ihr s h)
  | lam _ _ ih =>
    rw [LambdaTerm.instantiate, LambdaTerm.incrementBVars, ih _ (Nat.add_le_add_right h 1),
      ← incrementBVars_incrementBVars_of_ge _ (Nat.zero_le m), ← LambdaTerm.instantiate,
      ← LambdaTerm.incrementBVars]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf s h) (iha s h)
  | left _ ih => exact congrArg LambdaTerm.left (ih s h)
  | right _ ih => exact congrArg LambdaTerm.right (ih s h)
  | bvar deBruijnIndex =>
    simp only [LambdaTerm.instantiate, LambdaTerm.incrementBVars,
      apply_ite (LambdaTerm.incrementBVars _), apply_ite LambdaTerm.instantiate, ite_apply]
    grind

theorem incrementBVars_instantiate_of_ge {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ)
    (s : LambdaTerm ι κ) {n m : ℕ} (h : m ≤ n) :
    (t.instantiate n s).incrementBVars m =
      (t.incrementBVars m).instantiate (n + 1) (s.incrementBVars m) := by
  induction t generalizing n m s with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl s h) (ihr s h)
  | lam _ _ ih =>
    rw [LambdaTerm.instantiate, LambdaTerm.incrementBVars, ih _ (Nat.add_le_add_right h 1),
      ← incrementBVars_incrementBVars_of_ge _ (Nat.zero_le m), ← LambdaTerm.instantiate,
      ← LambdaTerm.incrementBVars]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf s h) (iha s h)
  | left _ ih => exact congrArg LambdaTerm.left (ih s h)
  | right _ ih => exact congrArg LambdaTerm.right (ih s h)
  | bvar deBruijnIndex =>
    simp only [LambdaTerm.instantiate, LambdaTerm.incrementBVars,
      apply_ite (LambdaTerm.incrementBVars _), apply_ite LambdaTerm.instantiate, ite_apply]
    grind

theorem instantiate_instantiate_of_le {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ)
    (s₁ s₂ : LambdaTerm ι κ) {n m : ℕ} (h : n ≤ m) :
    (t.instantiate n s₁).instantiate m s₂ =
      (t.instantiate (m + 1) (s₂.incrementBVars n)).instantiate n (s₁.instantiate m s₂) := by
  induction t generalizing n m s₁ s₂ with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl s₁ s₂ h) (ihr s₁ s₂ h)
  | lam _ _ ih =>
    rw [LambdaTerm.instantiate, LambdaTerm.instantiate, ih _ _ (Nat.add_le_add_right h 1),
      ← incrementBVars_instantiate_of_ge _ _ (Nat.zero_le m), ← LambdaTerm.instantiate,
      ← incrementBVars_incrementBVars_of_ge _ (Nat.zero_le n), ← LambdaTerm.instantiate]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf s₁ s₂ h) (iha s₁ s₂ h)
  | left _ ih => exact congrArg LambdaTerm.left (ih s₁ s₂ h)
  | right _ ih => exact congrArg LambdaTerm.right (ih s₁ s₂ h)
  | bvar deBruijnIndex =>
    simp only [LambdaTerm.instantiate, apply_ite LambdaTerm.instantiate, ite_apply,
      instantiate_incrementBVars]
    grind

theorem instantiate_instantiate_of_ge {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ)
    (s₁ s₂ : LambdaTerm ι κ) {n m : ℕ} (h : m ≤ n) :
    (t.instantiate (n + 1) s₁).instantiate m s₂ =
      (t.instantiate m (s₂.incrementBVars n)).instantiate n (s₁.instantiate m s₂) := by
  induction t generalizing n m s₁ s₂ with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl s₁ s₂ h) (ihr s₁ s₂ h)
  | lam _ _ ih =>
    rw [LambdaTerm.instantiate, LambdaTerm.instantiate, ih _ _ (Nat.add_le_add_right h 1),
      ← incrementBVars_instantiate_of_ge _ _ (Nat.zero_le m), ← LambdaTerm.instantiate,
      ← incrementBVars_incrementBVars_of_ge _ (Nat.zero_le n), ← LambdaTerm.instantiate]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf s₁ s₂ h) (iha s₁ s₂ h)
  | left _ ih => exact congrArg LambdaTerm.left (ih s₁ s₂ h)
  | right _ ih => exact congrArg LambdaTerm.right (ih s₁ s₂ h)
  | bvar deBruijnIndex =>
    simp only [LambdaTerm.instantiate, apply_ite LambdaTerm.instantiate, ite_apply,
      instantiate_incrementBVars]
    grind

theorem instantiate_incrementBVars_comm {ι : Type u} {κ : Type v}
    (t₁ t₂ : LambdaTerm ι κ) (n : ℕ) :
    (t₁.incrementBVars n).instantiate (n + 1) t₂ =
      (t₁.incrementBVars (n + 1)).instantiate n t₂ := by
  induction t₁ generalizing n t₂ with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl t₂ n) (ihr t₂ n)
  | lam dom _ ih => exact congrArg (LambdaTerm.lam dom) (ih (t₂.incrementBVars 0) (n + 1))
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf t₂ n) (iha t₂ n)
  | left _ ih => exact congrArg LambdaTerm.left (ih t₂ n)
  | right _ ih => exact congrArg LambdaTerm.right (ih t₂ n)
  | bvar deBruijnIndex =>
    simp only [LambdaTerm.incrementBVars, LambdaTerm.instantiate,
      apply_ite LambdaTerm.instantiate, ite_apply]
    grind

theorem instantiate_incrementBVars_assoc {ι : Type u} {κ : Type v}
    (t₁ t₂ t₃ : LambdaTerm ι κ) (n : ℕ) :
    (((t₁.incrementBVars (n + 1)).instantiate n t₂).incrementBVars (n + 1)).instantiate n t₃ =
      (t₁.incrementBVars (n + 1)).instantiate n ((t₂.incrementBVars (n + 1)).instantiate n t₃) := by
  induction t₁ generalizing n t₂ t₃ with
  | of _ => rfl
  | unit => rfl
  | prod _ _ ihl ihr => exact congrArg₂ LambdaTerm.prod (ihl t₂ t₃ n) (ihr t₂ t₃ n)
  | lam dom _ ih =>
    simp [LambdaTerm.incrementBVars, LambdaTerm.instantiate, ih,
      ← incrementBVars_incrementBVars_of_ge, ← incrementBVars_instantiate_of_ge]
  | app _ _ ihf iha => exact congrArg₂ LambdaTerm.app (ihf t₂ t₃ n) (iha t₂ t₃ n)
  | left _ ih => exact congrArg LambdaTerm.left (ih t₂ t₃ n)
  | right _ ih => exact congrArg LambdaTerm.right (ih t₂ t₃ n)
  | bvar deBruijnIndex =>
    simp only [LambdaTerm.incrementBVars, LambdaTerm.instantiate,
      apply_ite (LambdaTerm.incrementBVars _), apply_ite LambdaTerm.instantiate, ite_apply]
    grind

theorem Convertible.congr_incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (app : List (Object ι)) {ctx : List (Object ι)} {t₁ t₂ : LambdaTerm ι κ} {tu tt : Object ι}
    {satt₁ : Typing ζ (app ++ ctx) t₁ tt} {satt₂ : Typing ζ (app ++ ctx) t₂ tt}
    (convt : Convertible satt₁ satt₂) (n : Nat) (hn : app.length = n) :
    Convertible (satt₁.incrementBVars app tu n hn) (satt₂.incrementBVars app tu n hn) := by
  obtain ⟨c, hc⟩ : ∃ l, app ++ ctx = l := ⟨_, rfl⟩
  revert t₁ t₂
  rewrite! (castMode := .all) [hc]
  intro t₁ t₂ satt₁ satt₂ convt
  induction convt generalizing n app with subst hc
  | refl _ => rfl
  | symm _ ih => exact .symm (ih app n hn rfl)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ app n hn rfl) (ih₂ app n hn rfl)
  | congr_prod _ _ ihl ihr => exact .congr_prod (ihl app n hn rfl) (ihr app n hn rfl)
  | congr_lam hf ih => exact .congr_lam (ih (_ :: app) (n + 1) (congrArg Nat.succ hn) rfl)
  | congr_app _ _ ihf iha => exact .congr_app (ihf app n hn rfl) (iha app n hn rfl)
  | congr_left hu ih => exact .congr_left (ih app n hn rfl)
  | congr_right hu ih => exact .congr_right (ih app n hn rfl)
  | unit_eta _ => exact .unit_eta _
  | prod_eta _ => exact .prod_eta _
  | prod_left _ _ => exact .prod_left _ _
  | prod_right _ _ => exact .prod_right _ _
  | lam_eta sat =>
    refine .trans (.lam_eta _) (.of_eq ?_ _ _)
    rw [incrementBVars_incrementBVars_of_ge _ (Nat.zero_le n), LambdaTerm.incrementBVars,
      LambdaTerm.incrementBVars, LambdaTerm.incrementBVars, if_neg (Nat.not_add_one_le_zero n)]
  | beta satb sata =>
    exact .trans (.beta _ _) (.of_eq
      (incrementBVars_instantiate_of_le _ _ (Nat.zero_le n)).symm _ _)

theorem Convertible.congr_instantiate_left {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (app : List (Object ι)) {ctx : List (Object ι)} {s t₁ t₂ : LambdaTerm ι κ} {ts tt : Object ι}
    {satt₁ : Typing ζ (app ++ ts :: ctx) t₁ tt} {satt₂ : Typing ζ (app ++ ts :: ctx) t₂ tt}
    (sats : Typing ζ (app ++ ctx) s ts) (convt : Convertible satt₁ satt₂)
    (n : Nat) (hn : app.length = n) :
    Convertible (satt₁.instantiate app sats n hn) (satt₂.instantiate app sats n hn) := by
  obtain ⟨c, hc⟩ : ∃ l, app ++ ts :: ctx = l := ⟨_, rfl⟩
  revert t₁ t₂
  rewrite! (castMode := .all) [hc]
  intro t₁ t₂ satt₁ satt₂ convt
  induction convt generalizing s n app with subst hc
  | refl _ => rfl
  | symm _ ih => exact .symm (ih app sats n hn rfl)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ app sats n hn rfl) (ih₂ app sats n hn rfl)
  | congr_prod _ _ ihl ihr => exact .congr_prod (ihl app sats n hn rfl) (ihr app sats n hn rfl)
  | congr_lam hf ih => exact .congr_lam (ih (_ :: app) _ (n + 1) (congrArg Nat.succ hn) rfl)
  | congr_app _ _ ihf iha => exact .congr_app (ihf app sats n hn rfl) (iha app sats n hn rfl)
  | congr_left hu ih => exact .congr_left (ih app sats n hn rfl)
  | congr_right hu ih => exact .congr_right (ih app sats n hn rfl)
  | unit_eta _ => exact .unit_eta _
  | prod_eta _ => exact .prod_eta _
  | prod_left _ _ => exact .prod_left _ _
  | prod_right _ _ => exact .prod_right _ _
  | lam_eta sat =>
    exact .trans (.lam_eta _) (.congr_lam
      (.congr_app (.of_eq (incrementBVars_instantiate_of_ge _ _ (Nat.zero_le n)) _ _) (.refl _)))
  | beta satb sata =>
    exact .trans (.beta _ _) (.of_eq (instantiate_instantiate_of_le _ _ _ (Nat.zero_le n)).symm _ _)

theorem Convertible.congr_instantiate_right {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (app : List (Object ι)) {ctx : List (Object ι)} {s₁ s₂ t : LambdaTerm ι κ} {ts tt : Object ι}
    (satt : Typing ζ (app ++ ts :: ctx) t tt) {sats₁ : Typing ζ (app ++ ctx) s₁ ts}
    {sats₂ : Typing ζ (app ++ ctx) s₂ ts} (convs : Convertible sats₁ sats₂)
    (n : Nat) (hn : app.length = n) :
    Convertible (satt.instantiate app sats₁ n hn) (satt.instantiate app sats₂ n hn) := by
  induction t generalizing s₁ s₂ n app tt with
  | of _ => exact .of_eq rfl _ _
  | unit => exact .of_eq rfl _ _
  | prod _ _ ihl ihr =>
    cases satt with
    | prod satl satr => exact .congr_prod (ihl app satl convs n hn) (ihr app satr convs n hn)
  | lam dom body ih =>
    cases satt with
    | lam satb =>
      exact .congr_lam (ih (dom :: app) satb (.congr_incrementBVars [] convs 0 (Eq.refl 0))
        (n + 1) (congrArg Nat.succ hn))
  | app fn arg ihf iha =>
    cases satt with
    | app satf sata => exact .congr_app (ihf app satf convs n hn) (iha app sata convs n hn)
  | left _ ih =>
    cases satt with
    | left sat => exact .congr_left (ih app sat convs n hn)
  | right _ ih =>
    cases satt with
    | right sat => exact .congr_right (ih app sat convs n hn)
  | bvar deBruijnIndex =>
    cases satt with
    | bvar satt =>
      by_cases hd : deBruijnIndex = n
      · obtain rfl : ts = tt := by grind
        rw! (castMode := .all) [LambdaTerm.instantiate, if_pos hd,
          LambdaTerm.instantiate, if_pos hd]
        rwa [Subsingleton.elim (Eq.rec ..) sats₁, Subsingleton.elim (Eq.rec ..) sats₂]
      · refine .of_eq ?_ _ _
        rw [LambdaTerm.instantiate, if_neg hd, LambdaTerm.instantiate, if_neg hd]

theorem Convertible.congr_instantiate {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (app : List (Object ι)) {ctx : List (Object ι)}
    {s₁ s₂ t₁ t₂ : LambdaTerm ι κ} {ts tt : Object ι}
    {satt₁ : Typing ζ (app ++ ts :: ctx) t₁ tt} {satt₂ : Typing ζ (app ++ ts :: ctx) t₂ tt}
    {sats₁ : Typing ζ (app ++ ctx) s₁ ts} {sats₂ : Typing ζ (app ++ ctx) s₂ ts}
    (convt : Convertible satt₁ satt₂) (convs : Convertible sats₁ sats₂)
    (n : Nat) (hn : app.length = n) :
    Convertible (satt₁.instantiate app sats₁ n hn) (satt₂.instantiate app sats₂ n hn) :=
  .trans
    (.congr_instantiate_left app sats₁ convt n hn)
    (.congr_instantiate_right app satt₂ convs n hn)

nonrec theorem Convertible.instantiate_incrementBVars {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    (app : List (Object ι)) {ctx : List (Object ι)} {s t : LambdaTerm ι κ} {ts tt : Object ι}
    (satt : Typing ζ (app ++ ctx) t tt) (sats : Typing ζ (app ++ ctx) s ts)
    (n : Nat) (hn : app.length = n) :
    Convertible (.instantiate app (.incrementBVars app ts satt n hn) sats n hn) satt :=
  .of_eq (instantiate_incrementBVars t s n) _ _

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

def Objectu.homs {ι : Type u} (sources : List (Objectu ι)) (target : Objectu ι) : Objectu ι :=
  match sources with
  | [] => target
  | source :: sources => .hom source (.homs sources target)

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
  | .hom source target => coHom source target source.elimHom
where
  coHom {ι : Type u} (source target : Object₀ ι) (kk : Objectq ι) : Objectq ι :=
    match target with
    | .of i => .hom kk i
    | .prod left right => .prod (coHom source left kk) (coHom source right kk)
    | .hom source' target => coHom (.prod source source') target (.prod kk source'.elimHom)

def Objectq.elimProd {ι : Type u} (o : Objectq ι) : List (Objectu ι) :=
  match o with
  | .of i => [.of i]
  | .prod left right => left.elimProd ++ right.elimProd
  | .hom source target => [.homs source.elimProd (.of target)]

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
            ((left.sath.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sath.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
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
            ((left.sath.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₁ right₁) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sath.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
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
            ((left.sati.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sati.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
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
            ((left.sati.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
              (.left (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))
            ((right.sati.incrementBVars [_] _ 1 (Eq.refl 1)).instantiate []
              (.right (.bvar 0 (.prod left₂ right₂) (Option.mem_some_self _))) 0 (Eq.refl 0))))
          0 (Eq.refl 0))) ?_
      refine .trans (.congr_instantiate_right [] _ (.prod_right _ _) 0 (Eq.refl 0)) (.of_eq ?_ _ _)
      simp only [instantiate_incrementBVars_assoc]

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
            Iso ζ ctx (.prod left right) (Object₀.toObject (v.elim u (.prod u))))
          (fun ihr => .trans (.prodCongr ihl ihr) (.prodUnit ζ ctx u.toObject))
          (fun _ ihr => .prodCongr ihl ihr) right.elimUnit (.elimUnit ζ ctx right))
      left.elimUnit (.elimUnit ζ ctx left)
  | .hom source target => sorry

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

def LambdaTerm.lams {ι : Type u} {κ : Type v} (t : LambdaTerm ι κ)
    (ks : List (Object ι)) : LambdaTerm ι κ :=
  match ks with
  | [] => t
  | k :: ks => .lam k (t.lams ks)

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

section CategoryTheory
open CategoryTheory MonoidalCategory

variable {C : Type w} [Category.{r} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

def Object.interpret {ι : Type u} (ri : ι → C) (t : Object ι) : C :=
  match t with
  | .of i => ri i
  | .unit => 𝟙_ C
  | .prod l r => l.interpret ri ⊗ r.interpret ri
  | .hom s t => s.interpret ri ⟹ t.interpret ri

def Morphism.interpret {ι : Type u} {κ : Type v} {s t : κ → Object ι}
    (ri : ι → C) (rk : (k : κ) → (s k).interpret ri ⟶ (t k).interpret ri)
    {src tgt : Object ι} (t : Morphism s t src tgt) : src.interpret ri ⟶ tgt.interpret ri :=
  match t with
  | .of k => rk k
  | .id _ => 𝟙 _
  | .comp f g => f.interpret ri rk ≫ g.interpret ri rk
  | .unit _ => CartesianMonoidalCategory.toUnit _
  | .prod f g => CartesianMonoidalCategory.lift (f.interpret ri rk) (g.interpret ri rk)
  | .left _ _ => CartesianMonoidalCategory.fst _ _
  | .right _ _ => CartesianMonoidalCategory.snd _ _
  | .curry f => CartesianClosed.curry (f.interpret ri rk)
  | .eval _ _ => (CategoryTheory.exp.ev _).app _

end CategoryTheory

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

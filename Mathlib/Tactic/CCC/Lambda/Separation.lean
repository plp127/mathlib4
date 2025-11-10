/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.CCC.Lambda.Iso
import Mathlib.Tactic.CCC.Lambda.Normalization
import Mathlib.Data.Finsupp.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/- following
S. V. Solov'ev,
The category of finite sets and Cartesian closed categories,
Zap. Nauchn. Sem. LOMI, 1981, Volume 105, 174–194 -/


universe u v w r

theorem List.TProd.get_ext {ι : Type u} {α : ι → Type v} {l : List ι}
    {t₁ t₂ : l.TProd α} (h : ∀ n i hi, t₁.get n i hi = t₂.get n i hi) : t₁ = t₂ := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    exact Prod.ext (h 0 x (Option.mem_some_self x)) (ih fun n i hi => h (n + 1) i hi)

@[simp]
theorem List.TProd.get_mk {ι : Type u} {α : ι → Type v} {l : List ι} (f : (i : ι) → α i)
    (n : Nat) (i : ι) (hi : i ∈ l[n]?) : (List.TProd.mk l f).get n i hi = f i := by
  induction l generalizing n with
  | nil => cases hi
  | cons x xs ih =>
    cases n with
    | zero => cases hi; rfl
    | succ n => exact ih n hi

def List.TProd.ofFn {ι : Type u} {α : ι → Type v} (l : List ι)
    (f : (n : Fin l.length) → α l[n]) : List.TProd α l :=
  match l with
  | [] => PUnit.unit
  | _ :: xs => (f ⟨0, Nat.zero_lt_succ _⟩, List.TProd.ofFn xs fun n => f n.succ)

theorem List.TProd.get_ofFn {ι : Type u} {α : ι → Type v} (l : List ι)
    (f : (n : Fin l.length) → α l[n]) (n : Fin l.length) : (List.TProd.ofFn l f).get n (l[n.1]'n.2)
      (Option.mem_def.2 (getElem?_eq_getElem n.2)) = f n := by
  induction l with
  | nil => exact n.elim0
  | cons x xs ih =>
    cases n using Fin.cases with
    | zero => rfl
    | succ n => exact ih _ n

@[simp]
def List.TProd.castList {ι : Type u} {α : ι → Type v} {l₁ l₂ : List ι}
    (eq : l₁ = l₂) (t : l₁.TProd α) : l₂.TProd α :=
  match l₁, l₂  with
  | [], [] => t
  | _ :: _, _ :: _ =>
    (cast (congrArg α (List.cons_eq_cons.1 eq).1) t.1,
      List.TProd.castList (List.cons_eq_cons.1 eq).2 t.2)

@[simp]
theorem List.TProd.castList_refl {ι : Type u} {α : ι → Type v} (l : List ι)
    (eq : l = l) (t : l.TProd α) : t.castList eq = t := by
  induction l <;> simp_all

@[simp]
theorem List.TProd.castList_castList {ι : Type u} {α : ι → Type v} {l₁ l₂ l₃ : List ι}
    (eq₁ : l₁ = l₂) (eq₂ : l₂ = l₃) (t : l₁.TProd α) :
    (t.castList eq₁).castList eq₂ = t.castList (eq₁.trans eq₂) := by
  subst eq₁ eq₂; simp

@[simp]
theorem List.TProd.get_castList {ι : Type u} {α : ι → Type v} {l₁ l₂ : List ι}
    (eq : l₁ = l₂) (t : l₁.TProd α) (n : Nat) {i : ι} (hi : i ∈ l₂[n]?) :
    (t.castList eq).get n i hi = t.get n i (by grind) := by
  subst eq; simp

def List.TProd.append {ι : Type u} {α : ι → Type v} {l₁ l₂ : List ι}
    (t₁ : List.TProd α l₁) (t₂ : List.TProd α l₂) : List.TProd α (l₁ ++ l₂) :=
  match l₁ with
  | [] => t₂
  | _ :: _ => (t₁.1, List.TProd.append t₁.2 t₂)

theorem List.TProd.get_append_of_lt {ι : Type u} {α : ι → Type v} {l₁ l₂ : List ι}
    (t₁ : l₁.TProd α) (t₂ : l₂.TProd α) (n : Nat) (hn : n < l₁.length) {i : ι}
    (hi : i ∈ (l₁ ++ l₂)[n]?) : (t₁.append t₂).get n i hi = t₁.get n i (by grind) := by
  induction l₁ generalizing n with
  | nil => cases hn
  | cons x xs ih =>
    cases n with
    | zero => cases hi; rfl
    | succ n => exact ih t₁.2 n (Nat.lt_of_add_lt_add_right hn) hi

theorem List.TProd.get_append_of_ge {ι : Type u} {α : ι → Type v} {l₁ l₂ : List ι}
    (t₁ : l₁.TProd α) (t₂ : l₂.TProd α) (n : Nat) (hn : l₁.length ≤ n) {i : ι}
    (hi : i ∈ (l₁ ++ l₂)[n]?) :
    (t₁.append t₂).get n i hi = t₂.get (n - l₁.length) i (by grind) := by
  induction l₁ generalizing n with
  | nil => rfl
  | cons x xs ih =>
    cases n with
    | zero => cases hn
    | succ n =>
      conv =>
        enter [2, 2]
        rw [List.length_cons, Nat.add_sub_add_right]
      exact ih t₁.2 n (Nat.le_of_add_le_add_right hn) hi

def List.TProd.map {ι : Type u} {κ : Type v} {α : ι → Type w} {β : κ → Type r} {l : List ι}
    (fi : ι → κ) (f : (i : ι) → α i → β (fi i)) (t : List.TProd α l) : List.TProd β (l.map fi) :=
  match l with
  | [] => PUnit.unit
  | _ :: _ => (f _ t.1, List.TProd.map fi f t.2)

@[simp]
theorem List.TProd.get_map {ι : Type u} {κ : Type v} {α : ι → Type w} {β : κ → Type r} {l : List ι}
    (fi : ι → κ) (f : (i : ι) → α i → β (fi i)) (t : List.TProd α l) (n : Nat) {i : ι}
    (hi : i ∈ l[n]?) : (t.map fi f).get n (fi i) (by grind) = f i (t.get n i hi) := by
  induction l generalizing n with
  | nil => cases hi
  | cons x xs ih =>
    cases n with
    | zero => cases hi; rfl
    | succ n => exact ih t.2 n hi

theorem List.TProd.map_append {ι : Type u} {κ : Type v} {α : ι → Type w} {β : κ → Type r}
    {l₁ l₂ : List ι} (fi : ι → κ) (f : (i : ι) → α i → β (fi i))
    (t₁ : List.TProd α l₁) (t₂ : List.TProd α l₂) : (t₁.append t₂).map fi f =
      ((t₁.map fi f).append (t₂.map fi f)).castList List.map_append.symm := by
  apply List.TProd.get_ext
  intro n i hi
  obtain hn | hn := Nat.lt_or_ge n l₁.length
  · simp only [List.map_append, length_map, hn, getElem?_append_left, getElem?_pos, getElem_map,
      Option.mem_def, Option.some_inj] at hi
    subst hi
    simp [List.getElem?_append_left, hn, List.TProd.get_append_of_lt]
  · have nu : n - l₁.length < (l₂.map fi).length := by grind
    simp only [List.map_append, length_map, hn, getElem?_append_right, Option.mem_def] at hi
    rw [getElem?_pos (l₂.map fi) (n - l₁.length) nu, Option.some_inj, List.getElem_map] at hi
    subst hi
    simp [List.getElem?_append_right, hn, List.TProd.get_append_of_ge]

theorem List.TProd.castList_append_castList {ι : Type u} {α : ι → Type w}
    {l₁₁ l₂₁ l₁₂ l₂₂ : List ι} (eq₁ : l₁₁ = l₁₂) (eq₂ : l₂₁ = l₂₂)
    (t₁ : List.TProd α l₁₁) (t₂ : List.TProd α l₂₁) :
    (t₁.castList eq₁).append (t₂.castList eq₂) =
      (t₁.append t₂).castList (congrArg₂ (· ++ ·) eq₁ eq₂) := by
  cases eq₁; cases eq₂; simp

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

mutual

theorem Normalu.toNormal_injective {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} : (@Normalu.toNormal ι κ ζ ctx typ).Injective :=
  fun a b hab =>
    match a, b with
    | .ofNeutral _, .ofNeutral _ =>
      congrArg Normalu.ofNeutral (Neutralu.toNeutral_injective (Normal.ofNeutral.inj hab))
    | .lam _ _, .lam _ _ =>
      congrArg (Normalu.lam _) (Normalu.toNormal_injective (Normal.lam.inj hab))

theorem Neutralu.toNeutral_injective {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} : (@Neutralu.toNeutral ι κ ζ ctx typ).Injective :=
  fun a b hab =>
    match typ, a with
    | _, .of k₁ _=>
        @id (∀ (t : Object ι) (ht : ζ k₁ = t) (b : Neutralu ζ ctx t)
          (hb : ht ▸ Neutral.of k₁ ctx = b.toNeutral),
          Neutralu.of k₁ ctx = ht ▸ b) (fun t ht b hb =>
            match t, b with
            | _, .of k₂ _ => by
              let f {ctx : List (Object ι)} {typ : Object ι} (t : Neutral ζ ctx typ) : Option κ :=
                t.casesOn
                  (of := fun k _ => some k)
                  (app := fun _ _ => none)
                  (left := fun _ => none)
                  (right := fun _ => none)
                  (bvar := fun _ _ _ => none)
              have hf := congrArg f hb
              change _ = some k₂ at hf
              rewrite! [← ht] at hf
              cases hf
              rfl
          ) (ζ k₁) rfl b hab
    | _, .bvar n _ _ =>
      match b with
      | .bvar _ _ _ => by cases hab; rfl
    | _, .app _ _ =>
      match b with
      | .app _ _ => by
        cases (Neutral.app.inj hab).1
        exact congr (congrArg Neutralu.app
          (Neutralu.toNeutral_injective (Neutral.app.inj hab).2.1.eq))
          (Normalu.toNormal_injective (Neutral.app.inj hab).2.2.eq)

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

def Separation.symm {ι : Type u} {ri : ι → Type v} {typ : Object ι}
    {rk₁ rk₂ : typ.read ri} (sep : Separation ri rk₁ rk₂) : Separation ri rk₂ rk₁ :=
  match typ with
  | .of _ => .up (.up sep.down.down.symm)
  | .unit => sep
  | .prod _ _ => sep.map Separation.symm Separation.symm
  | .hom _ _ => ⟨sep.1, sep.2.symm⟩

def Separation.cast {ι : Type u} {ri : ι → Type v} {typ : Object ι}
    {rk₁ rk₂ rk₁' rk₂' : typ.read ri} (h₁ : rk₁ = rk₁') (h₂ : rk₂ = rk₂')
    (sep : Separation ri rk₁ rk₂) : Separation ri rk₁' rk₂' :=
  match typ with
  | .of _ => .up (.up ((h₁.symm.trans_ne sep.down.down).trans_eq h₂))
  | .unit => sep
  | .prod _ _ => sep.map
    (Separation.cast (congrArg Prod.fst h₁) (congrArg Prod.fst h₂))
    (Separation.cast (congrArg Prod.snd h₁) (congrArg Prod.snd h₂))
  | .hom _ _ => ⟨sep.1, sep.2.cast (congrFun h₁ sep.1) (congrFun h₂ sep.1)⟩

theorem Separation.ne {ι : Type u} {ri : ι → Type v} {typ : Object ι}
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
      fun ra₁ ra₂ h => Eq.rec (motive := fun x _ =>
          Extends f i (rk₁ ra₁) (extendWith f i ss (rk₁ x) (fn ra₂)).1)
        (extendWith f i ss (rk₁ ra₁) (fn ra₂)).2.1
        (extends_unique f i h ((restrict f i ra₂).2 ra₁ h)),
      fun k => (extendWith f i ss (rk₁ (restrict f i k).1) (fn k)).2.2⟩

mutual

def Normalu.decEq {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} (t₁ t₂ : Normalu ζ ctx typ) : Decidable (t₁ = t₂) :=
  match typ, t₁ with
  | _, .ofNeutral n₁ =>
    match t₂ with
    | .ofNeutral n₂ => @decidable_of_iff _ (HEq n₁ n₂) (by simp) (Neutralu.decHEq rfl n₁ n₂)
  | _, .lam _ body₁ =>
    match t₂ with
    | .lam _ body₂ => @decidable_of_iff _ (body₁ = body₂) (by simp) (Normalu.decEq body₁ body₂)

def Neutralu.decHEq {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ₁ typ₂ : Object ι} (eq : typ₁ = typ₂)
    (t₁ : Neutralu ζ ctx typ₁) (t₂ : Neutralu ζ ctx typ₂) : Decidable (HEq t₁ t₂) :=
  match ctx, typ₁, t₁ with
  | _, _, .of k₁ _ =>
    match t₂ with
    | .of k₂ _ => decidable_of_iff (k₁ = k₂)
      ⟨fun h => h ▸ HEq.rfl, fun h => Option.some.inj
        (congr_heq (congr_arg_heq (fun typ (x : Neutralu ζ _ typ) =>
          (x.casesOn
            (of := fun k _ => some k)
            (app := fun _ _ => none)
            (bvar := fun _ _ _ => none) : Option κ)) eq) h :)⟩
    | .app _ _ => .isFalse (by intro h; cases eq; cases h)
    | .bvar _ _ _ => .isFalse (by intro h; cases eq; cases h)
  | ctx, _, .app fn₁ arg₁ =>
    match ctx, typ₂, t₂ with
    | _, _, .of _ _ => .isFalse (by intro h; cases eq; cases h)
    | _, _, .app fn₂ arg₂ => @decidable_of_iff _ (∃ (_ : _ = _), HEq fn₁ fn₂ ∧ HEq arg₁ arg₂)
      ⟨fun h => by cases eq; cases h.1; cases h.2.1; cases h.2.2; rfl,
        fun h => by cases eq; cases h; simp⟩
      (@exists_prop_decidable _ _ _
        (fun h => @instDecidableAnd _ _ (Neutralu.decHEq (congrArg₂ Object.hom h eq) fn₁ fn₂)
          (@decidable_of_iff _ (h ▸ arg₁ = arg₂)
            (by cases h; simp) (Normalu.decEq (h ▸ arg₁) arg₂))))
    | _, _, .bvar _ _ _ => .isFalse (by intro h; cases eq; cases h)
  | ctx, _, .bvar n₁ _ _ =>
    match ctx, typ₂, t₂ with
    | _, _, .of _ _ => .isFalse (by intro h; cases eq; cases h)
    | _, _, .app _ _ => .isFalse (by intro h; cases eq; cases h)
    | _, _, .bvar n₂ _ _ => decidable_of_iff (n₁ = n₂)
      (by constructor <;> (intro h; cases eq; cases h; rfl))

end

instance {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} : DecidableEq (Normalu ζ ctx typ) := Normalu.decEq

instance {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Object ι}
    {ctx : List (Object ι)} {typ : Object ι} : DecidableEq (Neutralu ζ ctx typ) :=
  fun u v => @decidable_of_iff (u = v) (HEq u v) heq_iff_eq (Neutralu.decHEq rfl u v)

def Objectu.splitArrows {ι : Type u} (o : Objectu ι) : List (Objectu ι) × ι :=
  match o with
  | .of i => ([], i)
  | .hom source target => (source :: target.splitArrows.1, target.splitArrows.2)

theorem Objectu.foldr_splitArrows {ι : Type u} (o : Objectu ι) :
    o.splitArrows.1.foldr Objectu.hom (.of o.splitArrows.2) = o := by
  induction o with
  | of _ => rfl
  | hom source _ _ ih => exact congrArg (Objectu.hom source) ih

def Neutralu.telescope {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} (t : Neutralu ζ ctx tt) :
    (typs : List (Object ι)) × typs.TProd (Normalu ζ ctx) ×
      Neutralu ζ ctx (typs.foldl (fun t s => .hom s t) tt) :=
  match t with
  | .of k ctx => ⟨[], PUnit.unit, .of k ctx⟩
  | .app fn arg => ⟨_ :: fn.telescope.1, (arg, fn.telescope.2.1), fn.telescope.2.2⟩
  | .bvar n typ sat => ⟨[], PUnit.unit, .bvar n typ sat⟩

def Neutralu.detelescope {ι : Type u} {κ : Type v} {ζ : κ → Object ι} {ctx : List (Object ι)}
    {tt : Object ι} (typs : List (Object ι)) (args : typs.TProd (Normalu ζ ctx))
    (t : Neutralu ζ ctx (typs.foldl (fun t s => .hom s t) tt)) : Neutralu ζ ctx tt :=
  match typs with
  | [] => t
  | _ :: _ => .app (Neutralu.detelescope _ args.2 t) args.1

theorem Neutralu.detelescope_telescope {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {tt : Object ι} (t : Neutralu ζ ctx tt) :
    Neutralu.detelescope t.telescope.1 t.telescope.2.1 t.telescope.2.2 = t :=
  match t with
  | .of _ _ => rfl
  | .app fn arg => congrFun (congrArg Neutralu.app fn.detelescope_telescope) arg
  | .bvar _ _ _ => rfl

theorem Neutralu.detelescope_append {ι : Type u} {κ : Type v} {ζ : κ → Object ι}
    {ctx : List (Object ι)} {tt : Object ι} (typs₁ typs₂ : List (Object ι))
    (args₁ : typs₁.TProd (Normalu ζ ctx)) (args₂ : typs₂.TProd (Normalu ζ ctx))
    (t : Neutralu ζ ctx ((typs₁ ++ typs₂).foldl (fun t s => .hom s t) tt)) :
    Neutralu.detelescope (typs₁ ++ typs₂) (args₁.append args₂) t =
      Neutralu.detelescope typs₁ args₁
        (Neutralu.detelescope typs₂ args₂ (List.foldl_append ▸ t)) := by
  induction typs₁ generalizing tt with
  | nil => rfl
  | cons t ts ih => exact congrFun (congrArg Neutralu.app (ih args₁.2 t)) args₁.1

def interpretZero {ι : Type u} (f : ι →₀ Nat) (t : Object ι) :
    t.read fun u => Fin (2 ^ f u) :=
  match t with
  | .of _ => ⟨0, by simp [Nat.pow_pos]⟩
  | .unit => PUnit.unit
  | .prod left right => (interpretZero f left, interpretZero f right)
  | .hom _ target => fun _ => interpretZero f target

def interpretOne {ι : Type u} (f : ι →₀ Nat) (t : Objectu ι) (ht : f t.splitArrows.2 ≠ 0) :
    t.toObject₀.toObject.read fun u => Fin (2 ^ f u) :=
  match t with
  | .of _ => ⟨1, by simpa [Objectu.splitArrows] using ht⟩
  | .hom _ target => fun _ => interpretOne f target ht

def castInterpretZeroOneSeparation {ι : Type u} (f : ι →₀ Nat) (t₁ t₂ : Object ι) (t₃ : Objectu ι)
    (ht : f t₃.splitArrows.2 ≠ 0) (htt : t₁ = t₂) (htu : t₃.toObject₀.toObject = t₂) :
    Separation (fun u => Fin (2 ^ f u)) (htt ▸ interpretZero f t₁) (htu ▸ interpretOne f t₃ ht) :=
  match t₃, t₂ with
  | .of _, .of _ =>
    .up (.up (by cases htt; cases htu; exact ne_of_apply_ne Fin.val Nat.zero_ne_one))
  | .hom sourceu targetu, .hom source target =>
    ⟨interpretZero f source,
      (castInterpretZeroOneSeparation f target target targetu ht rfl (Object.hom.inj htu).2).cast
        (by cases htt; rfl) (by cases htu; rfl)⟩

def detelescopeInterpretation {ι : Type u} (ri : ι → Type w) {tt : Object ι}
    (typs : List (Object ι)) (args : typs.TProd (Object.read ri))
    (t : Object.read ri (typs.foldl (fun t s => .hom s t) tt)) : tt.read ri :=
  match typs with
  | [] => t
  | _ :: _ => detelescopeInterpretation ri _ args.2 t args.1

def detelescopeInterpretation_append {ι : Type u} (ri : ι → Type w) {tt : Object ι}
    (typs₁ typs₂ : List (Object ι))
    (args₁ : typs₁.TProd (Object.read ri)) (args₂ : typs₂.TProd (Object.read ri))
    (t : Object.read ri ((typs₁ ++ typs₂).foldl (fun t s => .hom s t) tt)) :
    detelescopeInterpretation ri (typs₁ ++ typs₂) (args₁.append args₂) t =
      detelescopeInterpretation ri typs₁ args₁
        (detelescopeInterpretation ri typs₂ args₂ (List.foldl_append ▸ t)) := by
  induction typs₁ generalizing tt with
  | nil => rfl
  | cons _ _ ih => exact congrFun (ih args₁.2 t) args₁.1

theorem read_detelescope {ι : Type u} {κ : Type v} {ζ : κ → Object ι} (ri : ι → Type w)
    (rk : (k : κ) → (ζ k).read ri) {ctx : List (Object ι)} {tt : Object ι}
    (ci : ctx.TProd (Object.read ri)) (typs : List (Object ι)) (args : typs.TProd (Normalu ζ ctx))
    (t : Neutralu ζ ctx (typs.foldl (fun t s => .hom s t) tt)) :
    (t.detelescope typs args).toNeutral.toLambdaTerm.read ri rk ctx ci tt
        (t.detelescope typs args).toNeutral.toTyping =
      detelescopeInterpretation ri typs ((args.map id fun ta arg =>
        arg.toNormal.toLambdaTerm.read ri rk ctx ci ta arg.toNormal.toTyping).castList typs.map_id)
        (t.toNeutral.toLambdaTerm.read ri rk ctx ci _ t.toNeutral.toTyping) := by
  induction typs generalizing tt with
  | nil => rfl
  | cons _ _ ih => exact congrFun (ih args.2 t) _

theorem detelescopeInterpretation_interpretZero {ι : Type u} (f : ι →₀ Nat) (tt : Object ι)
    (typs : List (Object ι)) (args : typs.TProd (Object.read fun i => Fin (2 ^ f i))) :
    detelescopeInterpretation (fun i => Fin (2 ^ f i)) typs args
      (interpretZero f (typs.foldl (fun t s => .hom s t) tt)) = interpretZero f tt := by
  induction typs generalizing tt with
  | nil => rfl
  | cons _ _ ih => exact congrFun (ih (.hom _ tt) args.2) args.1

def interpretSingleObject {ι : Type u} [DecidableEq ι] (t : Objectu ι) : ι →₀ Nat where
  toFun := Pi.single t.splitArrows.2 1
  support := {t.splitArrows.2}
  mem_support_toFun := by simp [Pi.single_apply]

@[simp]
theorem interpretSingleObject_hom {ι : Type u} [DecidableEq ι] (s t : Objectu ι) :
    interpretSingleObject (.hom s t) = interpretSingleObject t := rfl

theorem splitArrows_eq_of_foldl_eq {ι : Type u} (l : List (Object ι)) (t₁ t₂ : Objectu ι)
    (h : List.foldl (fun t s => .hom s t) t₁.toObject₀.toObject l = t₂.toObject₀.toObject) :
    t₁.splitArrows.2 = t₂.splitArrows.2 := by
  rw [← List.foldr_reverse] at h
  generalize l.reverse = k at h
  induction k generalizing t₂ with
  | nil =>
    exact congrArg (fun t => t.splitArrows.2)
      (Objectu.toObject₀_injective (Object₀.toObject_injective h))
  | cons _ _ ih =>
    cases t₂ with
    | of => cases h
    | hom s t => exact ih t (Object.hom.inj h).2

def readSingleFVarHead {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ]
    {ζ : κ → Objectu ι} {ctx : List (Object ι)} {t : Objectu ι}
    (v : Neutralu (fun k => (ζ k).toObject₀.toObject) ctx t.toObject₀.toObject)
    (k : κ) : (ζ k).toObject₀.toObject.read fun u => Fin (2 ^ interpretSingleObject t u) :=
  if h : ∃ h : (List.foldl (fun t s ↦ s.hom t) t.toObject₀.toObject v.telescope.1) =
      (ζ k).toObject₀.toObject, h ▸ v.telescope.2.2 = Neutralu.of k ctx then
    interpretOne (interpretSingleObject t) (ζ k) (Finsupp.mem_support_iff.mp
      (Finset.mem_singleton.mpr (splitArrows_eq_of_foldl_eq _ _ _ h.1).symm))
  else interpretZero (interpretSingleObject t) (ζ k).toObject₀.toObject

@[simp]
theorem readSingleFVarHead_app {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ]
    {ζ : κ → Objectu ι} {ctx : List (Object ι)} {typed t : Objectu ι}
    (v : Neutralu (fun k => (ζ k).toObject₀.toObject) ctx (Objectu.hom typed t).toObject₀.toObject)
    (a : Normalu (fun k => (ζ k).toObject₀.toObject) ctx typed.toObject₀.toObject) :
    readSingleFVarHead (.app v a) = readSingleFVarHead v := rfl

def readSingleBVarHead {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ]
    {ζ : κ → Object ι} {ctx : List (Objectu ι)} {t : Objectu ι}
    (v : Neutralu ζ (ctx.map fun t => t.toObject₀.toObject) t.toObject₀.toObject) :
    (ctx.map fun t => t.toObject₀.toObject).TProd
      (Object.read fun u => Fin (2 ^ interpretSingleObject t u)) :=
  .ofFn (ctx.map fun t => t.toObject₀.toObject) fun n =>
    if h : ∃ h : (List.foldl (fun t s ↦ s.hom t) t.toObject₀.toObject v.telescope.1) =
        ctx[n].toObject₀.toObject,
        h ▸ v.telescope.2.2 = Neutralu.bvar n ctx[n].toObject₀.toObject (by grind) then
      List.getElem_map _ ▸
        interpretOne (interpretSingleObject t) ctx[n] (Finsupp.mem_support_iff.mp
          (Finset.mem_singleton.mpr (splitArrows_eq_of_foldl_eq _ _ _ h.1).symm))
    else interpretZero (interpretSingleObject t) (ctx.map fun t => t.toObject₀.toObject)[n]

@[simp]
theorem readSingleBVarHead_app {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ]
    {ζ : κ → Object ι} {ctx : List (Objectu ι)} {typed t : Objectu ι}
    (v : Neutralu ζ (ctx.map fun t => t.toObject₀.toObject)
      (Objectu.hom typed t).toObject₀.toObject)
    (a : Normalu ζ (ctx.map fun t => t.toObject₀.toObject) typed.toObject₀.toObject) :
    @readSingleBVarHead ι _ κ _ ζ ctx t (.app v a) =
      @readSingleBVarHead ι _ κ _ ζ ctx (.hom typed t) v := rfl

def Neutralu.uType {ι : Type u} {κ : Type v} {ζ : κ → Objectu ι}
    {ctx : List (Objectu ι)} {typ : Object ι}
    (t : Neutralu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map (fun t => t.toObject₀.toObject)) typ) :
    { tu : Objectu ι // tu.toObject₀.toObject = typ } :=
  match ctx, t with
  | _, .of k _ => ⟨ζ k, rfl⟩
  | _, .app fn arg =>
    match fn.uType with
    | ⟨.hom _ target, h⟩ => ⟨target, (Object.hom.inj h).2⟩
  | ctx, .bvar n typ sat => ⟨ctx[n]'(by grind), by grind⟩

theorem Neutralu.separateHead.extracted_1 {ι : Type u} [DecidableEq ι] {κ : Type v}
    [DecidableEq κ] {ζ : κ → Objectu ι} {ctx : List (Objectu ι)} {t₁ t₂ : Objectu ι}
    (u : Neutralu (fun k ↦ (ζ k).toObject₀.toObject)
      (List.map (fun t ↦ t.toObject₀.toObject) ctx) t₁.toObject₀.toObject)
    (v : Neutralu (fun k ↦ (ζ k).toObject₀.toObject)
      (List.map (fun t ↦ t.toObject₀.toObject) ctx) t₂.toObject₀.toObject)
    (huv : ∀ (h : List.foldl (fun t s ↦ s.hom t) t₁.toObject₀.toObject u.telescope.fst =
        List.foldl (fun t s ↦ s.hom t) t₂.toObject₀.toObject v.telescope.fst),
        h ▸ u.telescope.snd.2 ≠ v.telescope.snd.2) :
    interpretZero (interpretSingleObject t₂) t₁.toObject₀.toObject =
      LambdaTerm.read (fun u ↦ Fin (2 ^ (interpretSingleObject t₂) u)) (readSingleFVarHead v)
        (List.map (fun t ↦ t.toObject₀.toObject) ctx) (readSingleBVarHead v)
          u.toNeutral.toLambdaTerm t₁.toObject₀.toObject
        u.toNeutral.toTyping := by
  have (eq := hc) c := u.toNeutral.toLambdaTerm
  induction c generalizing t₁ with
  | of k =>
    have tc := u.toNeutral.toTyping
    have (eq := hut) ut := t₁.toObject₀.toObject
    rw [← hc, ← hut] at tc
    rw [Subsingleton.elim u.toNeutral.toTyping (hc ▸ hut ▸ tc)]
    cases tc
    cases Objectu.toObject₀_injective (Object₀.toObject_injective hut)
    rewrite! [← hc]
    rw [LambdaTerm.read, readSingleFVarHead]
    symm
    apply dif_neg
    intro ⟨h, hh⟩
    obtain rfl : .of k _ = u := Neutralu.toNeutral_injective (Neutral.toLambdaTerm_injective hc)
    apply huv h.symm
    rewrite! (castMode := .all) [← h] at hh
    exact hh.symm
  | app fn arg ihf =>
    have tc := u.toNeutral.toTyping
    have (eq := hut) ut := t₁.toObject₀.toObject
    rw [← hc, ← hut] at tc
    rw [Subsingleton.elim u.toNeutral.toTyping (hc ▸ hut ▸ tc)]
    cases hut
    cases tc with | app satd sata
    rewrite! [← hc]
    obtain ⟨tf, uf, ua, rfl⟩ : ∃ tf : Objectu ι,
        ∃ uf : Neutralu (fun k ↦ (ζ k).toObject₀.toObject)
            (List.map (fun t : Objectu ι ↦ t.toObject₀.toObject) ctx)
              (Objectu.hom tf t₁).toObject₀.toObject,
          ∃ ua : Normalu (fun k ↦ (ζ k).toObject₀.toObject)
              (List.map (fun t : Objectu ι ↦ t.toObject₀.toObject) ctx) tf.toObject₀.toObject,
                u = .app uf ua := by
      dsimp only [Objectu.toObject₀, Object₀.toObject]
      clear huv
      generalize hut : t₁.toObject₀.toObject = ut at u
      cases u with
      | app uf ua =>
        obtain ⟨tu, htu⟩ := Neutralu.uType uf
        cases tu with
        | hom =>
          cases (Object.hom.inj htu).1
          exact ⟨_, _, _, rfl⟩
        | _ => cases htu
      | _ => cases hc
    cases hc
    cases unique_typing sata ua.toNormal.toTyping
    cases Subsingleton.elim satd uf.toNeutral.toTyping
    cases Subsingleton.elim sata ua.toNormal.toTyping
    specialize ihf uf huv rfl
    dsimp only [interpretSingleObject_hom, readSingleFVarHead_app, readSingleBVarHead_app,
      Objectu.toObject₀, Object₀.toObject] at ihf ⊢
    rw [LambdaTerm.read, ← ihf, interpretZero]
  | bvar deBruijnIndex =>
    have tc := u.toNeutral.toTyping
    have (eq := hut) ut := t₁.toObject₀.toObject
    rw [← hc, ← hut] at tc
    rw [Subsingleton.elim u.toNeutral.toTyping (hc ▸ hut ▸ tc)]
    cases hut
    cases tc
    obtain ⟨h, ht⟩ := List.getElem?_eq_some_iff.1 (Option.mem_def.1 ‹_›)
    rewrite! (castMode := .all) [← hc, ← ht]
    rw [LambdaTerm.read, readSingleBVarHead, List.TProd.get_ofFn _ _ ⟨deBruijnIndex, h⟩]
    symm
    cases Objectu.toObject₀_injective (Object₀.toObject_injective
      ((List.getElem_map fun t : Objectu ι => t.toObject₀.toObject).symm.trans ht))
    apply dif_neg
    intro ⟨he, hhe⟩
    obtain rfl : .bvar deBruijnIndex _ ‹_› = u := by
      exact Neutralu.toNeutral_injective (Neutral.toLambdaTerm_injective hc)
    apply huv he.symm
    rewrite! (castMode := .all) [← he] at hhe
    refine (hhe.trans ?_).symm
    rewrite! [he]
    rfl
  | _ =>
    exfalso
    clear *-hc
    generalize t₁.toObject₀.toObject = ut at u
    cases u <;> cases hc

theorem Neutralu.separateHead.extracted_2 {ι : Type u} {κ : Type v} {ζ : κ → Objectu ι}
    {ctx : List (Objectu ι)} {t : Object ι}
    (u v : Neutralu (fun k ↦ (ζ k).toObject₀.toObject)
      (List.map (fun t ↦ t.toObject₀.toObject) ctx) t)
    (huv : ∀ (h : u.telescope.fst = v.telescope.fst), h ▸ u.telescope.snd.2 ≠ v.telescope.snd.2)
    (h : List.foldl (fun t s ↦ s.hom t) t u.telescope.fst =
      List.foldl (fun t s ↦ s.hom t) t v.telescope.fst) :
    h ▸ u.telescope.snd.2 ≠ v.telescope.snd.2 := by
  have tt : u.telescope.1 = v.telescope.1 := by
    generalize u.telescope.1 = tu at h
    generalize v.telescope.1 = tv at h
    let f (o : Object ι) : Nat :=
      Object.rec
        (of := fun _ => 0)
        (unit := 0)
        (prod := fun _ _ _ _ => 0)
        (hom := fun _ _ _ => Nat.succ) o
    have hf (init : Object ι) (ul : List (Object ι)) :
        f (ul.foldl (fun t s ↦ .hom s t) init) = f init + ul.length := by
      induction ul generalizing init with
      | nil => rfl
      | cons _ _ ih => exact (ih (.hom _ init)).trans (Nat.add_right_comm _ 1 _)
    induction tu using List.reverseRecOn generalizing tv with
    | nil =>
      cases tv with
      | nil => rfl
      | cons =>
        have hh := congrArg f h
        rw [hf, hf] at hh
        simp at hh
    | append_singleton _ _ ih =>
      cases tv using List.reverseRecOn with
      | nil =>
        have hh := congrArg f h
        rw [hf, hf] at hh
        simp at hh
      | append_singleton =>
        rw [List.foldl_append, List.foldl_append] at h
        rw [(Object.hom.inj h).1, ih _ (Object.hom.inj h).2]
  grind only

theorem Neutralu.separateHead.extracted_3 {ι : Type u} [DecidableEq ι] {κ : Type v}
    [DecidableEq κ] {ζ : κ → Objectu ι} {ctx : List (Objectu ι)} {t : Objectu ι}
    (v : Neutralu (fun k ↦ (ζ k).toObject₀.toObject)
      (List.map (fun t ↦ t.toObject₀.toObject) ctx) t.toObject₀.toObject) :
    interpretOne (interpretSingleObject t) t (Finsupp.mem_support_iff.mp
      (Finset.mem_singleton_self t.splitArrows.2)) =
      LambdaTerm.read (fun u ↦ Fin (2 ^ (interpretSingleObject t) u)) (readSingleFVarHead v)
        (List.map (fun t ↦ t.toObject₀.toObject) ctx)
          (readSingleBVarHead v) v.toNeutral.toLambdaTerm t.toObject₀.toObject
        v.toNeutral.toTyping := by
  have (eq := hc) c := v.toNeutral.toLambdaTerm
  induction c generalizing t with
  | of k =>
    have tc := v.toNeutral.toTyping
    have (eq := hut) ut := t.toObject₀.toObject
    rw [← hc, ← hut] at tc
    rw [Subsingleton.elim v.toNeutral.toTyping (hc ▸ hut ▸ tc)]
    cases tc
    cases Objectu.toObject₀_injective (Object₀.toObject_injective hut)
    rewrite! [← hc]
    rw [LambdaTerm.read, readSingleFVarHead]
    symm
    apply dif_pos
    rw [← v.detelescope_telescope] at hc
    generalize v.telescope.1 = typs, v.telescope.2.1 = args, v.telescope.2.2 = t at hc
    cases typs with
    | nil => exact ⟨rfl, Neutralu.toNeutral_injective (Neutral.toLambdaTerm_injective hc.symm)⟩
    | cons => cases hc
  | app fn arg ihf =>
    have tc := v.toNeutral.toTyping
    have (eq := hut) ut := t.toObject₀.toObject
    rw [← hc, ← hut] at tc
    rw [Subsingleton.elim v.toNeutral.toTyping (hc ▸ hut ▸ tc)]
    cases hut
    cases tc with | app satd sata
    rewrite! [← hc]
    obtain ⟨tf, vf, va, rfl⟩ : ∃ tf : Objectu ι,
        ∃ vf : Neutralu (fun k ↦ (ζ k).toObject₀.toObject)
            (List.map (fun t : Objectu ι ↦ t.toObject₀.toObject) ctx)
              (Objectu.hom tf t).toObject₀.toObject,
          ∃ va : Normalu (fun k ↦ (ζ k).toObject₀.toObject)
              (List.map (fun t : Objectu ι ↦ t.toObject₀.toObject) ctx) tf.toObject₀.toObject,
                v = .app vf va := by
      dsimp only [Objectu.toObject₀, Object₀.toObject]
      generalize hut : t.toObject₀.toObject = ut at v
      cases v with
      | app vf va =>
        obtain ⟨tv, htv⟩ := Neutralu.uType vf
        cases tv with
        | hom =>
          cases (Object.hom.inj htv).1
          exact ⟨_, _, _, rfl⟩
        | _ => cases htv
      | _ => cases hc
    cases hc
    cases unique_typing sata va.toNormal.toTyping
    cases Subsingleton.elim satd vf.toNeutral.toTyping
    cases Subsingleton.elim sata va.toNormal.toTyping
    specialize ihf vf rfl
    dsimp only [interpretSingleObject_hom, readSingleFVarHead_app, readSingleBVarHead_app,
      Objectu.toObject₀, Object₀.toObject] at ihf ⊢
    rw [LambdaTerm.read, ← ihf, interpretOne]
  | bvar deBruijnIndex =>
    have tc := v.toNeutral.toTyping
    have (eq := hut) ut := t.toObject₀.toObject
    rw [← hc, ← hut] at tc
    rw [Subsingleton.elim v.toNeutral.toTyping (hc ▸ hut ▸ tc)]
    cases hut
    cases tc
    obtain ⟨h, ht⟩ := List.getElem?_eq_some_iff.1 (Option.mem_def.1 ‹_›)
    rewrite! (castMode := .all) [← hc, ← ht]
    rw [LambdaTerm.read, readSingleBVarHead, List.TProd.get_ofFn _ _ ⟨deBruijnIndex, h⟩]
    symm
    cases Objectu.toObject₀_injective (Object₀.toObject_injective
      ((List.getElem_map fun t : Objectu ι => t.toObject₀.toObject).symm.trans ht))
    apply dif_pos
    rw [← v.detelescope_telescope] at hc
    generalize v.telescope.1 = typs, v.telescope.2.1 = args, v.telescope.2.2 = t at hc
    cases typs with
    | nil => exact ⟨rfl, Neutralu.toNeutral_injective (Neutral.toLambdaTerm_injective hc.symm)⟩
    | cons => cases hc
  | _ =>
    exfalso
    clear *-hc
    generalize t.toObject₀.toObject = ut at v
    cases v <;> cases hc

def Neutralu.separateHead {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ]
    {ζ : κ → Objectu ι} {ctx : List (Objectu ι)} {t : Objectu ι}
    (u v : Neutralu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) t.toObject₀.toObject)
    (huv : ∀ h : u.telescope.1 = v.telescope.1, h ▸ u.telescope.2.2 ≠ v.telescope.2.2) :
    Separation (fun u => Fin (2 ^ interpretSingleObject t u))
      (u.toNeutral.toLambdaTerm.read (fun u => Fin (2 ^ interpretSingleObject t u))
        (readSingleFVarHead v) (ctx.map fun t => t.toObject₀.toObject)
        (readSingleBVarHead v) t.toObject₀.toObject u.toNeutral.toTyping)
      (v.toNeutral.toLambdaTerm.read (fun u => Fin (2 ^ interpretSingleObject t u))
        (readSingleFVarHead v) (ctx.map fun t => t.toObject₀.toObject)
        (readSingleBVarHead v) t.toObject₀.toObject v.toNeutral.toTyping) :=
  (castInterpretZeroOneSeparation (interpretSingleObject t)
    t.toObject₀.toObject t.toObject₀.toObject t (Finsupp.mem_support_iff.mp
      (Finset.mem_singleton_self t.splitArrows.2)) rfl rfl).cast
    (Neutralu.separateHead.extracted_1 u v (Neutralu.separateHead.extracted_2 u v huv))
      (Neutralu.separateHead.extracted_3 v)

set_option debug.skipKernelTC true

mutual

unsafe def Normalu.separate {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Objectu ι}
    {ctx : List (Objectu ι)} (typ : Objectu ι) (typ₁ typ₂ : Object ι)
    (ht₁ : typ₁ = typ.toObject₀.toObject) (ht₂ : typ₂ = typ.toObject₀.toObject)
    (t₁ : Normalu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) typ₁)
    (t₂ : Normalu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) typ₂) (h : ht₁ ▸ t₁ ≠ ht₂ ▸ t₂) :
    (f : ι →₀ Nat) × (rk : (k : κ) → (ζ k).toObject₀.toObject.read fun u => Fin (2 ^ f u)) ×
    (ci : (ctx.map (fun t => t.toObject₀.toObject)).TProd (Object.read fun u ↦ Fin (2 ^ f u))) ×
    Separation (fun u => Fin (2 ^ f u))
      (ht₁ ▸ t₁.toNormal.toLambdaTerm.read (fun u => Fin (2 ^ f u))
        rk (ctx.map (fun t : Objectu ι => t.toObject₀.toObject)) ci typ₁ t₁.toNormal.toTyping)
      (ht₂ ▸ t₂.toNormal.toLambdaTerm.read (fun u => Fin (2 ^ f u))
        rk (ctx.map (fun t : Objectu ι => t.toObject₀.toObject)) ci typ₂ t₂.toNormal.toTyping) :=
  match typ, typ₁, typ₂, t₁, t₂ with
  | .of i, .of u, .of v, .ofNeutral n₁, .ofNeutral n₂ =>
    if ht : _ then
      haveI k := Neutralu.separate i (.of u) (.of v) [] PUnit.unit ht₁ ht₂ n₁ n₂ (by grind) ht
      ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.cast (by cases ht₁; rfl) (by cases ht₂; rfl)⟩
    else
      haveI k := Neutralu.separateHead (ht₁ ▸ n₁) (ht₂ ▸ n₂) fun htt hhtt => by
        cases ht₁; cases ht₂; exact ht ⟨htt, hhtt⟩
      ⟨interpretSingleObject (.of i), readSingleFVarHead (ht₂ ▸ n₂), readSingleBVarHead (ht₂ ▸ n₂),
        k.cast (by cases ht₁; rfl) (by cases ht₂; rfl)⟩
  | .hom dom tb, .hom dom₁ tb₁, .hom dom₂ tb₂, .lam _ body₁, .lam _ body₂ =>
    match dom, dom₁, dom₂, (Object.hom.inj ht₁).1, (Object.hom.inj ht₂).1 with
    | dom, _, _, rfl, rfl =>
      haveI k := @Normalu.separate ι _ κ _ ζ (dom :: ctx) tb tb₁ tb₂
        (Object.hom.inj ht₁).2 (Object.hom.inj ht₂).2 body₁ body₂ (by grind)
      ⟨k.1, k.2.1, k.2.2.1.2, k.2.2.1.1, k.2.2.2.cast (by cases ht₁; rfl) (by cases ht₂; rfl)⟩

unsafe def Neutralu.separate {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Objectu ι}
    {ctx : List (Objectu ι)} (i : ι) (typ₁ typ₂ : Object ι) (ss : List (Objectu ι))
    (as : (ss.map fun t => t.toObject₀.toObject).TProd
      (Normalu (fun k => (ζ k).toObject₀.toObject) (ctx.map fun t => t.toObject₀.toObject)))
    (ht₁ : typ₁ = (ss.map fun t => t.toObject₀.toObject).foldl (fun t s => .hom s t) (.of i))
    (ht₂ : typ₂ = (ss.map fun t => t.toObject₀.toObject).foldl (fun t s => .hom s t) (.of i))
    (t₁ : Neutralu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) typ₁)
    (t₂ : Neutralu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) typ₂) (h : ht₁ ▸ t₁ ≠ ht₂ ▸ t₂)
    (ht : ∃ h : t₁.telescope.1 = t₂.telescope.1,
      ht₁ ▸ h ▸ t₁.telescope.2.2 = ht₂ ▸ t₂.telescope.2.2) :
    (f : ι →₀ Nat) × (rk : (k : κ) → (ζ k).toObject₀.toObject.read fun u => Fin (2 ^ f u)) ×
    (ci : (ctx.map (fun t => t.toObject₀.toObject)).TProd (Object.read fun u ↦ Fin (2 ^ f u))) ×
    Separation (fun u => Fin (2 ^ f u))
      (((ht₁ ▸ t₁).detelescope (ss.map _) as).toNeutral.toLambdaTerm.read
        (fun u => Fin (2 ^ f u)) rk (ctx.map _) ci (.of i)
          ((ht₁ ▸ t₁).detelescope (ss.map _) as).toNeutral.toTyping)
      (((ht₂ ▸ t₂).detelescope (ss.map _) as).toNeutral.toLambdaTerm.read
        (fun u => Fin (2 ^ f u)) rk (ctx.map _) ci (.of i)
          ((ht₂ ▸ t₂).detelescope (ss.map _) as).toNeutral.toTyping) :=
  match ctx, typ₁, t₁ with
  | _, _, .of _ _
  | _, _, .bvar _ _ _ => False.elim <| by
    apply h
    rw [← t₂.detelescope_telescope]
    generalize t₂.telescope.1 = typs, t₂.telescope.2.1 = args, t₂.telescope.2.2 = t at ht
    cases ht.1; cases ht₂
    exact ht.2
  | ctx, tt₁, .app fn₁ arg₁ =>
    match ctx, typ₂, t₂ with
    | _, _, .of _ _
    | _, _, .bvar _ _ _ => (List.cons_ne_nil _ _ ht.1).elim
    | _, _, .app fn₂ arg₂ =>
      if haa : (List.cons.inj ht.1).1 ▸ arg₁ = arg₂ then
        match fn₂.uType with
        | ⟨.hom uTyp _, huTyp⟩ =>
          haveI k := Neutralu.separate i _ _ (ss ++ [uTyp])
            (.castList List.map_append.symm
              (as.append (((Object.hom.inj huTyp).1 ▸ arg₂ :), PUnit.unit)))
            (by cases huTyp; simpa [(List.cons.inj ht.1).1] using ht₁)
            (by cases huTyp; simpa using ht₂) fn₁ fn₂
            (by grind) ⟨(List.cons.inj ht.1).2, by grind [Neutralu.telescope]⟩
          ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.cast
            (by
              cases ht₁; cases (List.cons.inj ht.1).1; cases (Object.hom.inj huTyp).1
              congr 3 <;> (
                rewrite! [← haa, List.map_append]
                rw [List.TProd.castList_refl, Neutralu.detelescope_append]
                rewrite! [List.foldl_append]
                rfl))
            (by
              cases ht₂; cases (List.cons.inj ht.1).1; cases (Object.hom.inj huTyp).1
              congr 3 <;> (
                rewrite! [List.map_append]
                rw [List.TProd.castList_refl, Neutralu.detelescope_append]
                rewrite! [List.foldl_append]
                rfl))⟩
      else
        sorry
termination_by ι
decreasing_by all_goals sorry

end

end Mathlib.Tactic.CCC

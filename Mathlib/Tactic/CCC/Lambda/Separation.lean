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


universe u v w

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
  match t₃ with
  | .of _ =>
    match t₂ with
    | .of _ => .up (.up (by cases htt; cases htu; exact ne_of_apply_ne Fin.val Nat.zero_ne_one))
  | .hom sourceu targetu =>
    match t₂ with
    | .hom source target =>
      ⟨interpretZero f source,
        (castInterpretZeroOneSeparation f target target targetu ht rfl (Object.hom.inj htu).2).cast
          (by cases htt; rfl) (by cases htu; rfl)⟩

def Neutralu.separateOf {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ]
    {ζ : κ → Objectu ι} {ctx : List (Object ι)} {typ₁ typ₂ : Object ι}
    (t : Neutralu (fun k => (ζ k).toObject₀.toObject) ctx typ₁) (k : κ)
    (tt : typ₁ = typ₂) (tz : (ζ k).toObject₀.toObject = typ₂)
    (h : tt ▸ t ≠ tz ▸ Neutralu.of k ctx) :
    (f : ι →₀ Nat) × (rk : (k : κ) → (ζ k).toObject₀.toObject.read fun u => Fin (2 ^ f u)) ×
    (ci : ctx.TProd (Object.read fun u ↦ Fin (2 ^ f u))) ×
      Separation (fun u => Fin (2 ^ f u))
        (tt ▸ t.toNeutral.toLambdaTerm.read (fun u => Fin (2 ^ f u))
          rk ctx ci typ₁ t.toNeutral.toTyping)
        (tz ▸ rk k) := by
  refine ⟨{
    toFun := Pi.single (ζ k).splitArrows.2 1
    support := {(ζ k).splitArrows.2}
    mem_support_toFun := by simp [Pi.single_apply]
  }, Function.update (fun _ => interpretZero _ _) k (interpretOne _ (ζ k) (by simp)),
    .mk ctx (interpretZero _),
    (castInterpretZeroOneSeparation _ typ₁ typ₂ (ζ k) (by simp) tt tz).cast
      (congrArg (@Eq.rec _ _ _ · _ tt) (.symm ?_))
      (congrArg (@Eq.rec _ _ _ · _ tz) (.symm (by apply Function.update_self)))⟩
  have hc (ht : List.foldl (fun t s ↦ s.hom t) typ₁ t.telescope.fst = (ζ k).toObject₀.toObject) :
      ¬ht ▸ t.telescope.2.2 = .of k ctx := by
    cases t with
    | of _ _ => cases tz; exact h
    | app fn _ =>
      exfalso
      cases tz
      rw [← tt] at ht
      dsimp only [Neutralu.telescope, List.foldl] at ht
      rw [← List.foldr_reverse] at ht
      generalize fn.telescope.1.reverse = u at ht
      revert ht
      apply ne_of_apply_ne (fun x => (x.rec
        (of := fun _ => 0)
        (unit := 0)
        (prod := fun _ _ _ _ => 0)
        (hom := fun _ _ _ ih => ih + 1) : Nat))
      apply Nat.ne_of_gt
      induction u with
      | nil => apply Nat.lt_add_one
      | cons _ _ ih => exact Nat.lt_add_right 1 ih
    | bvar _ _ _ => cases tz; exact h
  refine Neutralu.rec (motive_1 := fun _ _ _ => True)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) ?_ ?_ ?_ t hc
  · intro _ _ hc
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hc rfl rfl
  · intro ctx _ _ fn arg ih _ hc
    dsimp only [Neutralu.toNeutral, Neutral.toTyping, LambdaTerm.read]
    rw [ih hc, interpretZero]
  · intro _ _ _ _ _
    apply List.TProd.get_mk

def Neutralu.separateBVar {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ]
    {ζ : κ → Object ι} {ctx : List (Object ι)} {typ₁ typ₂ : Object ι}
    (t : Neutralu ζ ctx typ₁) (n : Nat) (tb : Objectu ι)
    (ht : tb.toObject₀.toObject ∈ ctx[n]?) (tt : typ₁ = typ₂) (tz : tb.toObject₀.toObject = typ₂)
    (h : tt ▸ t ≠ tz ▸ Neutralu.bvar n tb.toObject₀.toObject ht) :
    (f : ι →₀ Nat) × (rk : (k : κ) → (ζ k).read fun u => Fin (2 ^ f u)) ×
    (ci : ctx.TProd (Object.read fun u ↦ Fin (2 ^ f u))) ×
      Separation (fun u => Fin (2 ^ f u))
        (tt ▸ t.toNeutral.toLambdaTerm.read (fun u => Fin (2 ^ f u))
          rk ctx ci typ₁ t.toNeutral.toTyping)
        (tz ▸ ci.get n tb.toObject₀.toObject ht) := by
  refine ⟨{
    toFun := Pi.single tb.splitArrows.2 1
    support := {tb.splitArrows.2}
    mem_support_toFun := by simp [Pi.single_apply]
  }, fun _ => interpretZero _ _,
    .ofFn ctx (Function.update (fun u => interpretZero _ ctx[u]) ⟨n, by grind⟩
      ((show tb.toObject₀.toObject = ctx[Fin.mk n _] by grind) ▸ interpretOne _ tb
        (Finsupp.mem_support_iff.1 (Finset.mem_singleton_self tb.splitArrows.2)))),
    (castInterpretZeroOneSeparation _ typ₁ typ₂ tb (by simp) tt tz).cast
      (congrArg (@Eq.rec _ _ _ · _ tt) (.symm ?_))
      (congrArg (@Eq.rec _ _ _ · _ tz) (.symm (by
        rewrite! (castMode := .all) [show tb.toObject₀.toObject = ctx[n]'(by grind) by grind]
        rw [List.TProd.get_ofFn ctx _ ⟨n, _⟩, Function.update_self])))⟩
  have hc (hb : List.foldl (fun t s ↦ s.hom t) typ₁ t.telescope.fst = tb.toObject₀.toObject) :
      ¬hb ▸ t.telescope.2.2 = .bvar n tb.toObject₀.toObject ht := by
    cases t with
    | of _ _ => cases tz; exact h
    | app fn _ =>
      exfalso
      cases tz
      rw [← tt] at hb
      dsimp only [Neutralu.telescope, List.foldl] at hb
      rw [← List.foldr_reverse] at hb
      generalize fn.telescope.1.reverse = u at hb
      revert hb
      apply ne_of_apply_ne (fun x => (x.rec
        (of := fun _ => 0)
        (unit := 0)
        (prod := fun _ _ _ _ => 0)
        (hom := fun _ _ _ ih => ih + 1) : Nat))
      apply Nat.ne_of_gt
      induction u with
      | nil => apply Nat.lt_add_one
      | cons _ _ ih => exact Nat.lt_add_right 1 ih
    | bvar _ _ _ => cases tz; exact h
  refine Neutralu.rec (motive_1 := fun _ _ _ => True)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) ?_ ?_ ?_ t ht hc
  · intro _ _ _ _
    rfl
  · intro ctx _ _ fn arg ih _ ht hc
    dsimp only [Neutralu.toNeutral, Neutral.toTyping, LambdaTerm.read]
    rw [ih ht hc, interpretZero]
  · intro ctx m typ _ hl h
    have hm : m < ctx.length := by grind
    cases show ctx[m]'hm = typ by grind
    dsimp [Neutralu.toNeutral, Neutral.toTyping]

    apply (List.TProd.get_ofFn _ _ ⟨m, hm⟩).trans
    apply Function.update_of_ne
    intro hnm
    cases hnm
    have eq := Option.some.inj ((List.getElem?_eq_getElem hm).symm.trans (Option.mem_def.1 hl))
    apply h eq
    rewrite! [eq]
    rfl

mutual

def Normalu.separate {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Objectu ι}
    {ctx : List (Objectu ι)} {typ : Objectu ι}
    (t₁ t₂ : Normalu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) typ.toObject₀.toObject) (h : t₁ ≠ t₂) :
    (f : ι →₀ Nat) × (rk : (k : κ) → (ζ k).toObject₀.toObject.read fun u => Fin (2 ^ f u)) ×
    (ci : (ctx.map fun t => t.toObject₀.toObject).TProd (Object.read fun u ↦ Fin (2 ^ f u))) ×
    Separation (fun u => Fin (2 ^ f u))
      (t₁.toNormal.toLambdaTerm.read (fun u => Fin (2 ^ f u)) rk
        (ctx.map fun t => t.toObject₀.toObject) ci typ.toObject₀.toObject t₁.toNormal.toTyping)
      (t₂.toNormal.toLambdaTerm.read (fun u => Fin (2 ^ f u)) rk
        (ctx.map fun t => t.toObject₀.toObject) ci typ.toObject₀.toObject t₂.toNormal.toTyping) :=
  match typ, t₁ with
  | .of i, .ofNeutral n₁ =>
    match t₂ with
    | .ofNeutral n₂ => @Neutralu.separate ι _ κ _ ζ ctx (.of i) (.of i) (.of i) rfl rfl n₁ n₂
      (ne_of_apply_ne Normalu.ofNeutral h)
  | .hom dom _, .lam _ body₁ =>
    match t₂ with
    | .lam _ body₂ =>
      haveI k := @Normalu.separate ι _ κ _ ζ (_ :: _) _ body₁ body₂
        (ne_of_apply_ne (Normalu.lam dom.toObject₀.toObject) h)
      ⟨k.1, k.2.1, k.2.2.1.2, k.2.2.1.1, k.2.2.2⟩

def Neutralu.separate {ι : Type u} [DecidableEq ι] {κ : Type v} [DecidableEq κ] {ζ : κ → Objectu ι}
    {ctx : List (Objectu ι)} {typ : Objectu ι} (tt₁ tt₂ : Object ι)
    (ht₁ : tt₁ = typ.toObject₀.toObject) (ht₂ : tt₂ = typ.toObject₀.toObject)
    (t₁ : Neutralu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) tt₁)
    (t₂ : Neutralu (fun k => (ζ k).toObject₀.toObject)
      (ctx.map fun t => t.toObject₀.toObject) tt₂) (h : ht₁ ▸ t₁ ≠ ht₂ ▸ t₂) :
    (f : ι →₀ Nat) × (rk : (k : κ) → (ζ k).toObject₀.toObject.read fun u => Fin (2 ^ f u)) ×
    (ci : (ctx.map fun t => t.toObject₀.toObject).TProd (Object.read fun u ↦ Fin (2 ^ f u))) ×
    Separation (fun u => Fin (2 ^ f u))
      (ht₁ ▸ t₁.toNeutral.toLambdaTerm.read (fun u => Fin (2 ^ f u)) rk
        (ctx.map fun t : Objectu ι => t.toObject₀.toObject) ci tt₁ t₁.toNeutral.toTyping)
      (ht₂ ▸ t₂.toNeutral.toLambdaTerm.read (fun u => Fin (2 ^ f u)) rk
        (ctx.map fun t : Objectu ι => t.toObject₀.toObject) ci tt₂ t₂.toNeutral.toTyping) :=
  match ctx, tt₁, t₁ with
  | _, _, .of u _ =>
    haveI k := Neutralu.separateOf t₂ u ht₂ ht₁ h.symm
    ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.symm⟩
  | ctx, tt₁, .app fn arg =>
    match ctx, tt₂, t₂ with
    | _, _, .of u _ => Neutralu.separateOf (.app fn arg) u ht₁ ht₂ h
    | _, _, .app fn arg => sorry
    | ctx, _, .bvar n tb sat => Eq.rec
      (fun hct hh =>
        by exact Neutralu.separateBVar (.app fn arg) n (ctx[n]'(by grind)) hh ht₁ hct (by grind))
      (show (ctx[n]'(by grind)).toObject₀.toObject = tb by grind) ht₂ sat
  | ctx, _, .bvar n tb sat =>
    haveI kk (hct : (ctx[n]'(by grind)).toObject₀.toObject = typ.toObject₀.toObject)
        (hh : (ctx[n]'(by grind)).toObject₀.toObject ∈
          (ctx.map fun t ↦ t.toObject₀.toObject)[n]?) :=
      Neutralu.separateBVar t₂ n (ctx[n]'(by grind)) hh ht₂ hct (by grind)
    Eq.rec (fun hct hh =>
        haveI k := kk hct hh
        ⟨k.1, k.2.1, k.2.2.1, by exact k.2.2.2.symm⟩)
      (show (ctx[n]'(by grind)).toObject₀.toObject = tb by grind) ht₁ sat

end

end Mathlib.Tactic.CCC

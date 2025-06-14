/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Vector.Defs

namespace Tactic.Polyrith.Groebner

structure Monomial (n : Nat) : Type where
  ofVec ::
    toVec : List.Vector Nat n
deriving DecidableEq

instance {n} : Mul (Monomial n) where
  mul a b := .ofVec (.map₂ (· + ·) a.toVec b.toVec)

def Monomial.gcd {n} (a b : Monomial n) : Monomial n :=
  .ofVec (.map₂ min a.toVec b.toVec)

def Monomial.lcm {n} (a b : Monomial n) : Monomial n :=
  .ofVec (.map₂ max a.toVec b.toVec)

def Monomial.ldiv {n} (a b : Monomial n) : Monomial n :=
  .ofVec (.map₂ (· - ·) a.toVec b.toVec)

structure Polynomial (𝕜 m : Type*) (cmp : m → m → Ordering) where
  protected ofArray ::
    protected toArray : Array (𝕜 × m)

def Polynomial.removeZero {𝕜 m cmp} [Zero 𝕜] [BEq 𝕜] (p : Polynomial 𝕜 m cmp) :
    Polynomial 𝕜 m cmp := .ofArray (p.toArray.filter (·.fst != 0))

instance {𝕜 m cmp} [Add 𝕜] [Zero 𝕜] [BEq 𝕜] : Add (Polynomial 𝕜 m cmp) where
  add a b := .removeZero <| .ofArray
    -- I wish `Array.mergeDedupWith` came with a version that would take `merge : α → α → Option α`
    (Array.mergeDedupWith (ord := {compare a b := cmp b.snd a.snd})
    a.toArray b.toArray (fun a b => (a.fst + b.fst, a.snd)))

instance {𝕜 m cmp} [Neg 𝕜] : Neg (Polynomial 𝕜 m cmp) where
  neg a := .ofArray (a.toArray.map fun c => (-c.fst, c.snd))

instance {𝕜 m cmp} [Sub 𝕜] [Zero 𝕜] [BEq 𝕜] : Sub (Polynomial 𝕜 m cmp) where
  sub a b := .removeZero <| .ofArray
    -- I wish `Array.mergeDedupWith` came with a version that would take `merge : α → α → Option α`
    (Array.mergeDedupWith (ord := {compare a b := cmp b.snd a.snd})
    a.toArray b.toArray (fun a b => (a.fst - b.fst, a.snd)))

instance {𝕜 m cmp} : Zero (Polynomial 𝕜 m cmp) where
  zero := .ofArray #[]

abbrev Polynomial₀ (𝕜 m : Type*) (cmp : m → m → Ordering) := { k : Polynomial 𝕜 m cmp // k ≠ 0}

instance {𝕜 m cmp} [Mul 𝕜] : HMul 𝕜 (Polynomial 𝕜 m cmp) (Polynomial 𝕜 m cmp) where
  hMul a b := .ofArray (b.toArray.map fun p => (a * p.fst, p.snd))

instance {𝕜 m cmp} [Mul m] : HMul m (Polynomial 𝕜 m cmp) (Polynomial 𝕜 m cmp) where
  hMul a b := .ofArray (b.toArray.map fun p => (p.fst, a * p.snd))

def Polynomial₀.lead {𝕜 m cmp} (p : Polynomial₀ 𝕜 m cmp) : 𝕜 × m :=
  p.val.toArray[0]'(Array.size_pos_iff.mpr fun ha => p.prop (congrArg Polynomial.ofArray ha))

def Polynomial₀.leadCoeff {𝕜 m cmp} (p : Polynomial₀ 𝕜 m cmp) : 𝕜 :=
  (p.val.toArray[0]'(Array.size_pos_iff.mpr fun ha => p.prop (congrArg Polynomial.ofArray ha))).fst

def Polynomial₀.leadMon {𝕜 m cmp} (p : Polynomial₀ 𝕜 m cmp) : m :=
  (p.val.toArray[0]'(Array.size_pos_iff.mpr fun ha => p.prop (congrArg Polynomial.ofArray ha))).snd

def Polynomial₀.S {𝕜 n cmp} [Mul 𝕜] [Sub 𝕜] [Zero 𝕜] [BEq 𝕜]
    (p q : Polynomial₀ 𝕜 (Monomial n) cmp) : Polynomial 𝕜 (Monomial n) cmp :=
  q.leadCoeff * (q.leadMon.ldiv (p.leadMon) * p.val) -
  p.leadCoeff * (p.leadMon.ldiv (q.leadMon) * q.val)

def Polynomial₀.dvd {𝕜 n cmp} (p q : Polynomial₀ 𝕜 (Monomial n) cmp) : Bool :=
  (List.Vector.map₂ (decide <| · ≤ ·) p.leadMon.toVec q.leadMon.toVec).toList.all id

def Polynomial₀.redₗ {𝕜 n cmp} [Mul 𝕜] [Sub 𝕜] [Zero 𝕜] [BEq 𝕜]
    (p q : Polynomial₀ 𝕜 (Monomial n) cmp) : Polynomial 𝕜 (Monomial n) cmp :=
  q.leadCoeff * p.val - p.leadCoeff * ((p.leadMon.ldiv q.leadMon) * q.val)

end Tactic.Polyrith.Groebner

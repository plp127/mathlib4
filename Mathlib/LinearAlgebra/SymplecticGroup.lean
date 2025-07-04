/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Symplectic Group

This file defines the symplectic group and proves elementary properties.

## Main Definitions

* `Matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
* `symplecticGroup`: the group of symplectic matrices

## TODO
* Every symplectic matrix has determinant 1.
* For `n = 1` the symplectic group coincides with the special linear group.
-/


open Matrix

variable {l R : Type*}

namespace Matrix

variable (l) [DecidableEq l] (R) [CommRing R]

section JMatrixLemmas

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 (-1) 1 0

@[simp]
theorem J_transpose : (J l R)ᵀ = -J l R := by
  rw [J, fromBlocks_transpose, ← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l ⊕ l) (l ⊕ l) R),
    fromBlocks_smul, Matrix.transpose_zero, Matrix.transpose_one, transpose_neg]
  simp [fromBlocks]

variable [Fintype l]

theorem J_squared : J l R * J l R = -1 := by
  rw [J, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  rw [← neg_zero, ← Matrix.fromBlocks_neg, ← fromBlocks_one]

theorem J_inv : (J l R)⁻¹ = -J l R := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg, J_squared]
  exact neg_neg 1

theorem J_det_mul_J_det : det (J l R) * det (J l R) = 1 := by
  rw [← det_mul, J_squared, ← one_smul R (-1 : Matrix _ _ R), smul_neg, ← neg_smul, det_smul,
    Fintype.card_sum, det_one, mul_one]
  apply Even.neg_one_pow
  exact Even.add_self _

theorem isUnit_det_J : IsUnit (det (J l R)) :=
  isUnit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩

end JMatrixLemmas

variable [Fintype l]

/-- The group of symplectic matrices over a ring `R`. -/
def symplecticGroup : Submonoid (Matrix (l ⊕ l) (l ⊕ l) R) where
  carrier := { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb]
    exact ha
  one_mem' := by simp

end Matrix

namespace SymplecticGroup

variable [DecidableEq l] [Fintype l] [CommRing R]

open Matrix

theorem mem_iff {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    A ∈ symplecticGroup l R ↔ A * J l R * Aᵀ = J l R := by simp [symplecticGroup]

instance coeMatrix : Coe (symplecticGroup l R) (Matrix (l ⊕ l) (l ⊕ l) R) :=
  ⟨Subtype.val⟩

section SymplecticJ

variable (l) (R)

theorem J_mem : J l R ∈ symplecticGroup l R := by
  rw [mem_iff, J, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_multiply]
  simp

/-- The canonical skew-symmetric matrix as an element in the symplectic group. -/
def symJ : symplecticGroup l R :=
  ⟨J l R, J_mem l R⟩

variable {l} {R}

@[simp]
theorem coe_J : ↑(symJ l R) = J l R := rfl

end SymplecticJ

variable {A : Matrix (l ⊕ l) (l ⊕ l) R}

theorem neg_mem (h : A ∈ symplecticGroup l R) : -A ∈ symplecticGroup l R := by
  rw [mem_iff] at h ⊢
  simp [h]

theorem symplectic_det (hA : A ∈ symplecticGroup l R) : IsUnit <| det A := by
  rw [isUnit_iff_exists_inv]
  use A.det
  refine (isUnit_det_J l R).mul_left_cancel ?_
  rw [mul_one]
  rw [mem_iff] at hA
  apply_fun det at hA
  simp only [det_mul, det_transpose] at hA
  rw [mul_comm A.det, mul_assoc] at hA
  exact hA

theorem transpose_mem (hA : A ∈ symplecticGroup l R) : Aᵀ ∈ symplecticGroup l R := by
  rw [mem_iff] at hA ⊢
  rw [transpose_transpose]
  have huA := symplectic_det hA
  have huAT : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact huA
  calc
    Aᵀ * J l R * A = (-Aᵀ) * (J l R)⁻¹ * A := by
      rw [J_inv]
      simp
    _ = (-Aᵀ) * (A * J l R * Aᵀ)⁻¹ * A := by rw [hA]
    _ = -(Aᵀ * (Aᵀ⁻¹ * (J l R)⁻¹)) * A⁻¹ * A := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.neg_mul]
    _ = -(J l R)⁻¹ := by
      rw [mul_nonsing_inv_cancel_left _ _ huAT, nonsing_inv_mul_cancel_right _ _ huA]
    _ = J l R := by simp [J_inv]

@[simp]
theorem transpose_mem_iff : Aᵀ ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩

theorem mem_iff' : A ∈ symplecticGroup l R ↔ Aᵀ * J l R * A = J l R := by
  rw [← transpose_mem_iff, mem_iff, transpose_transpose]

instance hasInv : Inv (symplecticGroup l R) where
  inv A := ⟨(-J l R) * (A : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R,
      mul_mem (mul_mem (neg_mem <| J_mem _ _) <| transpose_mem A.2) <| J_mem _ _⟩

theorem coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Matrix _ _ _) = (-J l R) * (↑A)ᵀ * J l R := rfl

theorem inv_left_mul_aux (hA : A ∈ symplecticGroup l R) : -(J l R * Aᵀ * J l R * A) = 1 :=
  calc
    -(J l R * Aᵀ * J l R * A) = (-J l R) * (Aᵀ * J l R * A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = (-J l R) * J l R := by
      rw [mem_iff'] at hA
      rw [hA]
    _ = (-1 : R) • (J l R * J l R) := by simp only [Matrix.neg_mul, neg_smul, one_smul]
    _ = (-1 : R) • (-1 : Matrix _ _ _) := by rw [J_squared]
    _ = 1 := by simp only [neg_smul_neg, one_smul]

theorem coe_inv' (A : symplecticGroup l R) : (↑A⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R) = (↑A)⁻¹ := by
  refine (coe_inv A).trans (inv_eq_left_inv ?_).symm
  simp [inv_left_mul_aux]

theorem inv_eq_symplectic_inv (A : Matrix (l ⊕ l) (l ⊕ l) R) (hA : A ∈ symplecticGroup l R) :
    A⁻¹ = (-J l R) * Aᵀ * J l R :=
  inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])

instance : Group (symplecticGroup l R) :=
  { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    inv_mul_cancel := fun A => by
      apply Subtype.ext
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      exact inv_left_mul_aux A.2 }

end SymplecticGroup

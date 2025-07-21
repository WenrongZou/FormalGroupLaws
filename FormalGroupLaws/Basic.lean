/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/


import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.PartENat


/-!

## One Dimensional Formal Group
This file defines one dimensional formal group law over a ring `A`, homomorphism and isomorphism between two formal group.

## Adivisor : María Inés de Frutos-Fernández

## Reference:
· Silverman, The Arithmetic of Elliptic Curves (2nd edition) - Chapter 4.
· Lubin--Tate, Formal Complex Multiplication in Local Fields.
· Hazewinkel, Formal Groups and Applications. Start with Chapters 1 and 2. Later you can look at some parts of Chapters 4 and 6.

-/



-- Definition of Formal Group

-- Assume the coeffiecient ring `R` to be commutative ring.
variable {R : Type*} [CommRing R] {σ : Type*} (F : MvPowerSeries (Fin 2) R) (α : PowerSeries R)

noncomputable section

open MvPowerSeries

abbrev X₀ : MvPowerSeries (Fin 2) R := X (0 : Fin 2)

abbrev X₁ : MvPowerSeries (Fin 2) R := X (1 : Fin 2)

abbrev Y₀ : MvPowerSeries (Fin 3) R := X (0 : Fin 3)

abbrev Y₁ : MvPowerSeries (Fin 3) R := X (1 : Fin 3)

abbrev Y₂ : MvPowerSeries (Fin 3) R := X (2 : Fin 3)

abbrev subst_fir_aux : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => Y₀
  | ⟨1, _⟩ => Y₁

abbrev subst_sec_aux : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => Y₁
  | ⟨1, _⟩ => Y₂

instance has_subst_fir_aux : MvPowerSeries.HasSubst subst_fir_aux (S := R):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  by_cases hs0 : s = 0
  · simp [hs0, subst_fir_aux]
  · simp [show s = 1 by omega, subst_fir_aux]

instance has_subst_sec_aux: MvPowerSeries.HasSubst subst_sec_aux (S := R):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  by_cases hs0 : s = 0
  · simp [hs0, subst_sec_aux]
  · simp [show s = 1 by omega, subst_sec_aux]


-- (0 : Fin 2) ↦ F(X, Y), (1 : Fin 2) ↦ Z
abbrev subst_fir : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => subst (subst_fir_aux) F
  | ⟨1, _⟩ => Y₂

-- (0 : Fin 2) ↦ X, (1 : Fin 2) ↦ F (Y, Z)
abbrev subst_sec : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => Y₀
  | ⟨1, _⟩ => subst (subst_sec_aux) F

instance has_subst_fir (hF : constantCoeff _ R F = 0) : MvPowerSeries.HasSubst (subst_fir F):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  by_cases hs0 : s = 0
  · simp [hs0, subst_fir]
    rw [constantCoeff_subst has_subst_fir_aux ]
    simp [subst_fir_aux]
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    by_cases hx : x = 0
    · simp [hx, hF]
    have xneq : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      simp at hc
      have xeq : x = 0 := by
        refine Finsupp.ext ?_
        intro a
        by_cases ha0 : a = 0
        · simp [ha0, hc]
        · simp [show a = 1 by omega, ha0, hc]
      contradiction
    obtain x_or | x_or := xneq
    · simp [zero_pow x_or]
    · simp [zero_pow x_or]
  · simp [show s = 1 by omega, subst_fir]

instance has_subst_sec (hF : constantCoeff _ R F = 0) : MvPowerSeries.HasSubst (subst_sec F):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  by_cases hs0 : s = 0
  · simp [hs0, subst_sec]
  · simp [show s = 1 by omega]
    rw [constantCoeff_subst has_subst_sec_aux ]
    simp [subst_sec_aux]
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    by_cases hx : x = 0
    · simp [hx, hF]
    have xneq : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      simp at hc
      have xeq : x = 0 := by
        refine Finsupp.ext ?_
        intro a
        by_cases ha0 : a = 0
        · simp [ha0, hc]
        · simp [show a = 1 by omega, ha0, hc]
      contradiction
    obtain x_or | x_or := xneq
    · simp [zero_pow x_or]
    · simp [zero_pow x_or]

-- (0 : Fin 2) ↦ Y, (1 : Fin 2) ↦ X
abbrev subst_symm : Fin 2 → MvPowerSeries (Fin 2) R
  | ⟨0, _⟩ => X₁
  | ⟨1, _⟩ => X₀

abbrev subst_X : Fin 2 → MvPowerSeries (Fin 2) R
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩ => 0

abbrev subst_Y : Fin 2 → MvPowerSeries (Fin 2) R
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => X₁


variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`-/
structure FormalGroup  where
  toFun : MvPowerSeries (Fin 2) R
  zero_coeff : constantCoeff (Fin 2) R toFun = 0
  lin_coeff_X : subst subst_X toFun = X₀ (R := R)
  lin_coeff_Y : subst subst_Y toFun = X₁ (R := R)
  assoc : subst (subst_fir toFun) toFun = subst (subst_sec toFun) toFun
  --  Associativity of the Formal Group : `F (F (X, Y), Z) = F (X, F (Y, Z))`.

variable (R) in
structure CommFormalGroup extends FormalGroup R where
  comm : toFun = MvPowerSeries.subst (subst_symm) toFun
-- Commutativity F (X, Y) = F (Y, X)

-- Definition of homomorphism between Formal Group Law


-- a (F (X, Y))

-- G (a (X), a (Y))
abbrev subst_hom (a : PowerSeries  R):
  Fin 2 → MvPowerSeries (Fin 2) R
  | ⟨0, _⟩ => PowerSeries.subst  X₀ a
  | ⟨1, _⟩ => PowerSeries.subst  X₁ a

/-- Let `G₁, G₂` be two formal group laws over `CommRing A`. A homomorphism (over `A`)
  `F (X, Y) → G (X, Y)` is a power series `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` with coefficients
  in `A` without constant term such that `α(F (X, Y)) = G (α (X), α (Y))`. -/
structure FormalGroupHom  (G₁ G₂ : FormalGroup R) where
  toFun : PowerSeries R
  zero_constantCoeff : PowerSeries.constantCoeff R toFun = 0
  hom : PowerSeries.subst (G₁.toFun) toFun = subst (R := R) (subst_hom toFun) G₂.toFun

end

section FormalGroupIso

open PowerSeries

-- create a section

/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if there exists a
  homomorphism `β(X) : G (X, Y) → F (X, Y)` such that `α ∘ β = id,  β ∘ α = id`. -/
structure FormalGroupIso (G₁ G₂ : FormalGroup R) where
  toHom : FormalGroupHom G₁ G₂
  invHom : FormalGroupHom G₂ G₁
  left_inv : (PowerSeries.subst toHom.toFun) ∘ (PowerSeries.subst invHom.toFun) = id
  right_inv : (PowerSeries.subst invHom.toFun) ∘ (PowerSeries.subst toHom.toFun) = id

/-- An isomorphism `α(X) : F (X, Y) → G (X, Y)`, `α(X) = a₁ * X + a₂ * X ^ 2 + ⋯`
  is called strict isomorphism if `a₁ = 1`.-/
structure FormalGroupStrictIso (G₁ G₂ : FormalGroup R) extends FormalGroupIso G₁ G₂ where
  one_coeff_one : coeff R 1 toHom.toFun = 1

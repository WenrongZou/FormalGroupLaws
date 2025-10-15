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
import FormalGroupLaws.SubstInv
import Mathlib.Algebra.BigOperators.Finprod


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


/-- This is a map from `Fin 2` to `MvPowerSeries (Fin 3) R`,
  `0 ↦ Y₀`, `1 ↦ Y₁` -/
abbrev subst_fir_aux : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => Y₀
  | ⟨1, _⟩ => Y₁


/-- This is a map from `Fin 2` to `MvPowerSeries (Fin 3) R`,
  `0 ↦ Y₁`, `1 ↦ Y₂`-/
abbrev subst_sec_aux : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => Y₁
  | ⟨1, _⟩ => Y₂

lemma has_subst_fir_aux : MvPowerSeries.HasSubst subst_fir_aux (S := R):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  by_cases hs0 : s = 0
  · simp [hs0, subst_fir_aux]
  · simp [show s = 1 by omega, subst_fir_aux]

lemma has_subst_sec_aux: MvPowerSeries.HasSubst subst_sec_aux (S := R):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  by_cases hs0 : s = 0
  · simp [hs0, subst_sec_aux]
  · simp [show s = 1 by omega, subst_sec_aux]


/-- this is a map from `Fin 2` to `MvPowerSeries (Fin 3) R`,
  `(0 : Fin 2) ↦ F(X, Y), (1 : Fin 2) ↦ Z`. -/
abbrev subst_fir : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => subst (subst_fir_aux) F
  | ⟨1, _⟩ => Y₂

/-- this is a map from `Fin 2` to `MvPowerSeries (Fin 3) R`,
  (0 : Fin 2) ↦ X, (1 : Fin 2) ↦ F (Y, Z) -/
abbrev subst_sec : Fin 2 → MvPowerSeries (Fin 3) R
  | ⟨0, _⟩ => Y₀
  | ⟨1, _⟩ => subst (subst_sec_aux) F

lemma has_subst_fir (hF : constantCoeff _ R F = 0) : MvPowerSeries.HasSubst (subst_fir F):= by
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
        · simp [show a = 1 by omega, hc]
      contradiction
    obtain x_or | x_or := xneq
    · simp [zero_pow x_or]
    · simp [zero_pow x_or]
  · simp [show s = 1 by omega, subst_fir]

lemma has_subst_sec (hF : constantCoeff _ R F = 0) : MvPowerSeries.HasSubst (subst_sec F):= by
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
        · simp [show a = 1 by omega, hc]
      contradiction
    obtain x_or | x_or := xneq
    · simp [zero_pow x_or]
    · simp [zero_pow x_or]

/-- A map from `Fin 2` to `MvPowerSeries (Fin 2) R`, `0 → X₁` `1 → X₀`-/
abbrev subst_symm : Fin 2 → MvPowerSeries (Fin 2) R
  | ⟨0, _⟩ => X₁
  | ⟨1, _⟩ => X₀

lemma HasSubst_subst_symm : HasSubst (subst_symm (R := R)):= by
  apply hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  all_goals simp [subst_symm]

/-- A map from `Fin 2` to `PowerSeries R`, `0 → X` `1 → 0`-/
abbrev subst_X₀ : Fin 2 → PowerSeries R
  | ⟨0, _⟩ => PowerSeries.X
  | ⟨1, _⟩ => 0

/--  A map from `Fin 2` to `PowerSeries R`, `0 → 0` `1 → X`-/
abbrev subst_X₁ : Fin 2 → PowerSeries R
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => PowerSeries.X

/--
Given a power series p(X) ∈ R⟦X⟧ and an index i, we may view it as a
multivariate power series p(X_i) ∈ R⟦X_1, ..., X_n⟧.
-/
abbrev PowerSeries.toMvPowerSeries (f : PowerSeries R) (i : σ) : MvPowerSeries σ R :=
  PowerSeries.subst (MvPowerSeries.X i) f

lemma has_subst_toMvPowerSeries [Finite σ] {f : PowerSeries R}
  (hf : PowerSeries.constantCoeff R f = 0) :
  HasSubst (f.toMvPowerSeries (σ := σ)) (S := R) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro x
  rw [PowerSeries.toMvPowerSeries, ←coeff_zero_eq_constantCoeff, PowerSeries.coeff_subst
    (PowerSeries.HasSubst.X x)]
  simp
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd₀ : d = 0
  · simp [hd₀, hf]
  · simp [zero_pow hd₀]

/-- This is a map from `Fin 2` to `ℕ` mapping `0` to `i` and `1` to `j`, which can be used
  to compute degree of `X^i*X^j`.  -/
abbrev coeff_two (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j


variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`-/
@[ext]
structure FormalGroup where
  toFun : MvPowerSeries (Fin 2) R
  zero_constantCoeff : constantCoeff (Fin 2) R toFun = 0
  lin_coeff_X : coeff R (Finsupp.single 0 1) toFun = 1
  lin_coeff_Y : coeff R (Finsupp.single 1 1) toFun = 1
  assoc : subst (subst_fir toFun) toFun = subst (subst_sec toFun) toFun
  --  Associativity of the Formal Group : `F (F (X, Y), Z) = F (X, F (Y, Z))`.

variable (R) in
@[ext]
structure CommFormalGroup extends FormalGroup R where
  comm : toFun = MvPowerSeries.subst (subst_symm) toFun
-- Commutativity F (X, Y) = F (Y, X)

/-- Given a formal group `F`, `F.comm` is a proposition that `F(X,Y) = F(Y,X)`-/
def FormalGroup.comm (F : FormalGroup R) : Prop :=
  F.toFun = MvPowerSeries.subst subst_symm F.toFun

/-- A commutative formal group law is a formal group law.-/
instance : Coe (CommFormalGroup R) (FormalGroup R) where
  coe := CommFormalGroup.toFormalGroup

/-- Additive formal group law `Gₐ(X,Y) = X + Y`-/
def Gₐ : CommFormalGroup R where
  toFun := X₀ + X₁
  zero_constantCoeff := by simp only [map_add, constantCoeff_X, add_zero]
  lin_coeff_X := by
    simp [coeff_X]
    intro h
    have aux : Finsupp.single (0 : Fin 2) 1 0 = Finsupp.single (1 : Fin 2) 1 0 := by
      simp [h]
    simp at aux
  lin_coeff_Y := by
    simp [coeff_X]
    intro h
    have aux : Finsupp.single (0 : Fin 2) 1 0 = Finsupp.single (1 : Fin 2) 1 0 := by
      simp [h]
    simp at aux
  assoc := by
    rw [subst_add (has_subst_fir (X₀ + X₁) (by simp [constantCoeff_X])),
      subst_X (has_subst_fir (X₀ + X₁) (by simp [constantCoeff_X])),
      subst_X (has_subst_fir (X₀ + X₁) (by simp [constantCoeff_X]))]
    simp [subst_fir]
    simp [subst_add has_subst_fir_aux, has_subst_fir_aux, subst_fir_aux]
    rw [subst_add (has_subst_sec (X₀ + X₁) (by simp [constantCoeff_X])),
      subst_X (has_subst_sec (X₀ + X₁) (by simp [constantCoeff_X])),
      subst_X (has_subst_sec (X₀ + X₁) (by simp [constantCoeff_X]))]
    simp [subst_sec]
    simp [subst_add has_subst_sec_aux, has_subst_sec_aux, subst_sec_aux]
    ring
  comm := by
    rw [subst_add HasSubst_subst_symm, subst_X HasSubst_subst_symm,
      subst_X HasSubst_subst_symm]
    simp [subst_symm]
    ring



/-- Multiplicative formal group law `Gₘ(X,Y) = X + Y + XY`-/
def Gₘ : CommFormalGroup R where
  toFun := X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by
    simp only [map_add, constantCoeff_X, add_zero, map_mul, mul_zero]
  lin_coeff_X := by
    simp [coeff_X]
    rw [if_neg]
    simp
    simp [X_def, monomial_mul_monomial]
    rw [coeff_monomial, if_neg]
    simp
    refine Finsupp.ne_iff.mpr (by use 0; simp)
  lin_coeff_Y := by
    simp [coeff_X]
    rw [if_neg]
    simp
    simp [X_def, monomial_mul_monomial]
    rw [coeff_monomial, if_neg]
    simp
    refine Finsupp.ne_iff.mpr (by use 0; simp)
  assoc := by
    obtain has_subst₁ := has_subst_fir (X₀ + X₁ + X₀ * X₁ (R := R)) (by simp)
    obtain has_subst₂ := has_subst_sec (X₀ + X₁ + X₀ * X₁ (R := R)) (by simp)
    rw [subst_add has_subst₁, subst_add has_subst₁, subst_mul has_subst₁, subst_X has_subst₁,
      subst_X has_subst₁]
    simp [subst_fir]
    rw [subst_add has_subst_fir_aux, subst_add has_subst_fir_aux, subst_mul has_subst_fir_aux,
      subst_X has_subst_fir_aux, subst_X has_subst_fir_aux]
    simp [subst_fir_aux]
    rw [subst_add has_subst₂, subst_add has_subst₂, subst_mul has_subst₂, subst_X has_subst₂,
      subst_X has_subst₂]
    simp [subst_sec]
    rw [subst_add has_subst_sec_aux, subst_add has_subst_sec_aux, subst_mul has_subst_sec_aux,
      subst_X has_subst_sec_aux, subst_X has_subst_sec_aux]
    simp [subst_sec_aux]
    ring
  comm := by
    rw [subst_add HasSubst_subst_symm, subst_add HasSubst_subst_symm, subst_mul HasSubst_subst_symm,
      subst_X HasSubst_subst_symm, subst_X HasSubst_subst_symm]
    simp [subst_symm]; ring

def FormalGroup.map {R' : Type*} [CommRing R'] (f : R →+* R') (F : FormalGroup R):
  FormalGroup R' where
    toFun := MvPowerSeries.map _ f F.toFun
    zero_constantCoeff := by
      simp only [constantCoeff_map, F.zero_constantCoeff, map_zero]
    lin_coeff_X := by
      simp [F.lin_coeff_X]
    lin_coeff_Y := by
      simp [F.lin_coeff_Y]
    assoc := by
      have constant_zero : constantCoeff _ _ ((MvPowerSeries.map (Fin 2) f) F.toFun) = 0 := by
        simp [F.zero_constantCoeff]
      have aux₁ : subst (subst_fir ((MvPowerSeries.map (Fin 2) f) F.toFun))
        ((MvPowerSeries.map (Fin 2) f) F.toFun) =
        (MvPowerSeries.map (Fin 3) f) (subst (subst_fir F.toFun) F.toFun) := by
        ext n
        simp
        rw [coeff_subst (has_subst_fir F.toFun F.zero_constantCoeff), coeff_subst
          (has_subst_fir ((MvPowerSeries.map (Fin 2) f) F.toFun) constant_zero)]
        simp
        have aux₁ : subst_fir ((MvPowerSeries.map (Fin 2) f) F.toFun) 0 =
          (MvPowerSeries.map (Fin 3) f) (subst_fir F.toFun 0) := by
          simp [subst_fir]
          ext m
          simp
          rw [coeff_subst has_subst_fir_aux, coeff_subst has_subst_fir_aux]
          simp [subst_fir_aux]
          have aux' : ∀ (d : Fin 2 →₀ ℕ), (coeff R' m) (Y₀ ^ d 0 * Y₁ ^ d 1) =
            f ((coeff R m) (Y₀ ^ d 0 * Y₁ ^ d 1)) := by
            intro d

            sorry
          simp_rw [aux', ←map_mul]
          sorry
        have aux₂ : subst_fir ((MvPowerSeries.map (Fin 2) f) F.toFun) 1 =
          (MvPowerSeries.map (Fin 3) f) (subst_fir F.toFun 1) := by
          simp [subst_fir]
        simp_rw [aux₁, aux₂]



        sorry
      have aux₂ : subst (subst_sec ((MvPowerSeries.map (Fin 2) f) F.toFun))
        ((MvPowerSeries.map (Fin 2) f) F.toFun) =
        (MvPowerSeries.map (Fin 3) f) (subst (subst_sec F.toFun) F.toFun) := by
        rw [←substAlgHom_apply (has_subst_sec _ constant_zero)]
        rw [←substAlgHom_apply (has_subst_sec _ F.zero_constantCoeff)]

        sorry
      rw [←substAlgHom_apply (has_subst_fir _ constant_zero),
        ←substAlgHom_apply (has_subst_sec _ constant_zero)]



      sorry
      -- rw [aux₁, aux₂, F.assoc]

      -- rw [←substAlgHom_apply (has_subst_fir _ constant_zero),
      --   ←substAlgHom_apply (has_subst_sec _ constant_zero)]


variable {F : FormalGroup R} {f : PowerSeries R}

@[simp]
lemma PowerSeries.coeff_coe  (n : ℕ) : MvPowerSeries.coeff R (Finsupp.single () n) f
  = PowerSeries.coeff R n f := rfl

@[simp]
lemma PowerSeries.constantCoeff_coe : MvPowerSeries.constantCoeff Unit R f =
  PowerSeries.constantCoeff R f := rfl

lemma has_subst_X₀ : HasSubst (subst_X₀ (R := R)) := by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s
  all_goals simp [subst_X₀]

lemma has_subst_X₁ : HasSubst (subst_X₁ (R := R)) := by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s
  all_goals simp [subst_X₁]


/-- The first coefficient of `F(X, 0)` is `1`. -/
lemma FormalGroup.coeff_of_X₀_of_subst_X₀ :
  PowerSeries.coeff R 1 (subst subst_X₀ F.toFun) = 1 := by
  simp [PowerSeries.coeff, coeff_subst has_subst_X₀]
  have eq_aux : ∀ (d : Fin 2 →₀ ℕ), d ≠ (Finsupp.single 0 1) → (coeff R d) F.toFun *
    (PowerSeries.coeff R 1) (subst_X₀ 0 ^ d 0 * subst_X₀ 1 ^ d 1) = 0 := by
    intro d hd_neq
    by_cases hd : d 1 = 0
    · -- the case `d 1 = 0`
      by_cases hd' : d 0 = 0
      · -- the case `d 0 = 0`
        have d_is_zero : d = 0 := by
          refine (Finsupp.ext ?_)
          intro n
          fin_cases n
          all_goals simp [hd, hd']
        simp [d_is_zero, zero_constantCoeff]
      · -- the case `d 0 ≠ 0`
        simp [show subst_X₀ 0 = PowerSeries.X by rfl, hd, PowerSeries.coeff_X_pow]
        by_cases hd₀ : d 0 = 1
        · -- the cases `d 0 = 1`
          -- contradiction to the assumption
          have d_eq : d = (Finsupp.single 0 1) := by
            refine (Finsupp.ext ?_)
            intro x
            by_cases hx₀ : x = 0
            · simp [hx₀, hd₀]
            · have aux : x = 1 := by omega
              simp [aux, hd]
          contradiction
        have aux (f : PowerSeries R): PowerSeries.coeff R 1 f =
          coeff R (Finsupp.single () 1) f := by
          exact rfl
        intro hc
        by_contra
        exact hd₀ (Eq.symm hc)
    · -- the case `d 1 ≠ 0`
      simp [show subst_X₀ 1 = 0 by rfl, zero_pow hd]
  rw [finsum_eq_single _ _ eq_aux]
  simp [lin_coeff_X, show subst_X₀ 0 = PowerSeries.X by rfl, PowerSeries.coeff_X]


/-- The first coefficient of `F(0, X)` is `1`. -/
lemma FormalGroup.coeff_of_X₁_of_subst_X₁ :
  PowerSeries.coeff R 1 (subst subst_X₁ F.toFun) = 1 := by
  simp [PowerSeries.coeff, coeff_subst has_subst_X₁]
  have eq_aux : ∀ (d : Fin 2 →₀ ℕ), d ≠ (Finsupp.single 1 1) → (coeff R d) F.toFun *
    (PowerSeries.coeff R 1) (subst_X₁ 0 ^ d 0 * subst_X₁ 1 ^ d 1) = 0 := by
    intro d hd_neq
    by_cases hd : d 0 = 0
    · -- the case `d 0 = 0`
      by_cases hd' : d 1 = 0
      · -- the case d 1 = 0
        have d_is_zero : d = 0 := by
          refine (Finsupp.ext ?_)
          intro n
          fin_cases n
          all_goals simp [hd, hd']
        simp [d_is_zero, F.zero_constantCoeff]
      · -- the case d 1 ≠ 0
        simp [show subst_X₁ 1 = PowerSeries.X by rfl, hd, PowerSeries.coeff_X_pow]
        by_cases hd₁ : d 1 = 1
        · -- the case d 1 = 1
          have d_eq : d = (Finsupp.single 1 1) := by
            refine (Finsupp.ext ?_)
            intro x
            fin_cases x
            all_goals simp [hd, hd₁]
          contradiction
        intro h
        by_contra _
        exact hd₁ (Eq.symm h)
    · -- the case `d 0 ≠ 0`
      simp [subst_X₁, zero_pow hd]
  rw [finsum_eq_single _ _ eq_aux]
  simp [lin_coeff_Y, show subst_X₁ 1 = PowerSeries.X by rfl, PowerSeries.coeff_X]


/-- The constant coefficient of `F(X, 0)` is `0`. -/
lemma FormalGroup.constantCoeff_of_subst_X₀ :
  PowerSeries.constantCoeff R (subst subst_X₀ F.toFun) = 0 := by
  rw [PowerSeries.constantCoeff, constantCoeff_subst has_subst_X₀]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  simp
  by_cases hd : d 1 = 0
  · -- the case `d 1 = 0`
    by_cases hd' : d 0 = 0
    · -- the case `d 0 = 0`
      have d_is_zero : d = 0 := by
        refine (Finsupp.ext ?_)
        intro n
        fin_cases n
        all_goals simp [hd, hd']
      simp [d_is_zero, zero_constantCoeff]
    · -- the case `d 0 ≠ 0`
      simp [show subst_X₀ 0 = PowerSeries.X by rfl, hd, zero_pow hd']
  · -- the case `d 1 ≠ 0`
    simp [show subst_X₀ 1 = 0 by rfl, zero_pow hd]


/-- The constant coefficient of `F(0, X)` is `0`. -/
lemma FormalGroup.constantCoeff_of_subst_X₁ :
  PowerSeries.constantCoeff R (subst subst_X₁ F.toFun) = 0 := by
  rw [PowerSeries.constantCoeff, constantCoeff_subst has_subst_X₁]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  simp
  by_cases hd : d 0 = 0
  · -- the case `d 0 = 0`
    by_cases hd' : d 1 = 0
    · -- the case `d 1 = 0`
      have d_is_zero : d = 0 := by
        refine (Finsupp.ext ?_)
        intro n
        fin_cases n
        all_goals simp [hd, hd']
      simp [d_is_zero, zero_constantCoeff]
    · -- the case `d 1 ≠ 0`
      simp [show subst_X₀ 0 = PowerSeries.X by rfl, hd, zero_pow hd']
  · -- the case `d 0 ≠ 0`
    simp [show subst_X₁ 0 = 0 by rfl, zero_pow hd]

/-- Given a MvPowerSeries `f'` and two map `g h : σ → MvPowerSeries τ R`, if `g = h`,
  then `subst g f' = subst h f'`-/
lemma subst_congr {τ : Type*} {f' : MvPowerSeries σ R} {g h : σ → MvPowerSeries τ R} (h_gh : g = h) :
  subst g f' = subst h f' := by
  rw [h_gh]

/-- Given a PowerSeries `f'` and two MvPowerSeries `f₁, f₂`, if `f₁ = f₂`,
  then `PowerSeries.subst f₁ f' = PowerSeries.subst f₂ f'`. -/
lemma PowerSeries.subst_congr {f' : PowerSeries R} {f₁ f₂ : MvPowerSeries σ R}
  (h_eq : f₁ = f₂):
  PowerSeries.subst f₁ f' = PowerSeries.subst f₂ f' := by
  rw [h_eq]

-- theorem PowerSeries.map_eq_iff_subst_X_eq (map₁ : PowerSeries R →+ PowerSeries R) :



/-- By the associativity of Formal Group Law,
  `F (F(X, 0), 0) = F (X, 0)`. -/
lemma self_comp_aux :
  (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) ∘
  (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) =
  (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) := by
  let map_aux : Fin 3 → PowerSeries R
    | ⟨0, _⟩ => PowerSeries.X
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 0
  obtain assoc_eq := F.assoc
  have has_subst_aux : PowerSeries.HasSubst (subst subst_X₀ F.toFun (S := R)) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
    rw [constantCoeff_subst has_subst_X₀]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d = 0
    · simp [hd₀, F.zero_constantCoeff]
    · simp [subst_X₀]
      have dneq : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
        by_contra hc
        simp at hc
        have deq : d = 0 := by
          refine (Finsupp.ext ?_)
          intro n
          fin_cases n
          all_goals simp [hc]
        contradiction
      obtain hd₁ | hd₁ := dneq
      · simp [zero_pow hd₁]
      · simp [zero_pow hd₁]
  have has_subst_map_aux : HasSubst map_aux := by
    refine hasSubst_of_constantCoeff_zero ?_
    intro s
    fin_cases s
    all_goals simp [map_aux]
  /- prove that F(F(X,0),0) = F(X, F(0, 0)). -/
  have eq_aux₁ : subst map_aux (subst (subst_fir F.toFun) F.toFun) =
    subst map_aux (subst (subst_sec F.toFun) F.toFun) := by
    rw [assoc_eq]

  have left_eq : subst map_aux (subst (subst_fir F.toFun) F.toFun) =
    ((PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) ∘
    (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R))) PowerSeries.X := by
    simp
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_fir F.toFun F.zero_constantCoeff) has_subst_map_aux]
    rw [PowerSeries.subst, subst_comp_subst_apply (has_subst_X₀) (PowerSeries.HasSubst.const has_subst_aux)]
    apply subst_congr
    funext s
    fin_cases s
    · -- the cases s = 0
      simp [subst_X₀,subst_fir]
      rw [PowerSeries.X, subst_X (PowerSeries.HasSubst.const has_subst_aux), subst_comp_subst_apply
        has_subst_fir_aux has_subst_map_aux]
      apply subst_congr
      funext t
      fin_cases t
      all_goals simp [map_aux, subst_fir_aux, subst_X₀, subst_X has_subst_map_aux]
    · -- the cases s = 1
      simp [subst_X₀, subst_fir]
      rw [subst_X has_subst_map_aux]
      simp [map_aux, ←coe_substAlgHom (PowerSeries.HasSubst.const has_subst_aux), map_zero]
  have right_eq : subst map_aux (subst (subst_sec F.toFun) F.toFun) =
    (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) PowerSeries.X := by
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_sec F.toFun (F.zero_constantCoeff)) has_subst_map_aux]
    apply subst_congr
    funext s
    fin_cases s
    · -- the cases s = 0
      simp [subst_X₀, subst_sec, subst_X has_subst_map_aux, map_aux]
    · -- the cases s = 1
      simp [subst_X₀, subst_sec]
      rw [subst_comp_subst_apply has_subst_sec_aux has_subst_map_aux]
      have eq_aux₃ :  subst (0 : Fin 2 → PowerSeries R) F.toFun = 0 := by
        have aux : HasSubst (0 : Fin 2 → PowerSeries R) := by
          exact hasSubst_of_constantCoeff_zero (congrFun rfl)
        ext n
        rw [PowerSeries.coeff, coeff_subst aux]
        simp
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        by_cases hd₀ : d = 0
        · simp [hd₀, F.zero_constantCoeff]
        · -- the case d ≠ 0
          have dneq : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
            by_contra hc
            simp at hc
            have deq : d = 0 := by
              refine (Finsupp.ext ?_)
              intro n
              fin_cases n
              all_goals simp [hc]
            contradiction
          obtain hd₁ | hd₁ := dneq
          · simp [zero_pow hd₁]
          · simp [zero_pow hd₁]
      rw [←eq_aux₃]
      apply subst_congr
      funext t
      fin_cases t
      ·
        simp [map_aux, subst_sec_aux]
        rw [subst_X has_subst_map_aux]
      · -- the case t = 1
        simp [map_aux, subst_sec_aux]
        rw [subst_X has_subst_map_aux]
  rw [left_eq, right_eq] at eq_aux₁
  funext g
  have eq_aux₂ : g = PowerSeries.subst PowerSeries.X g := by
    simp [←PowerSeries.map_algebraMap_eq_subst_X]
  nth_rw 2 [eq_aux₂]
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X') has_subst_aux, ←right_eq,
    ←assoc_eq, left_eq]
  simp
  rw [PowerSeries.subst_X has_subst_aux, PowerSeries.subst_comp_subst_apply has_subst_aux has_subst_aux]


/-- By the associativity of Formal Group Law,
  `F (0, F(0, X)) = F (0, X)`. -/
lemma self_comp_aux' :
  (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) ∘
  (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) =
  (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) := by
  /- this map is Fin 3 → PowerSeries R where 0 → 0, 1 → 0, 2 → PowerSeries.X, and
    subst this map to the associativity equality will get the require equality-/
  let map_aux : Fin 3 → PowerSeries R
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => PowerSeries.X
  obtain assoc_eq := F.assoc
  have has_subst_aux : PowerSeries.HasSubst (subst subst_X₁ F.toFun (S := R)) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
    rw [constantCoeff_subst has_subst_X₁]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d = 0
    · simp [hd₀, F.zero_constantCoeff]
    · simp [subst_X₁]
      have dneq : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
        by_contra hc
        simp at hc
        have deq : d = 0 := by
          refine (Finsupp.ext ?_)
          intro n
          fin_cases n
          all_goals simp [hc]
        contradiction
      obtain hd₁ | hd₁ := dneq
      · simp [zero_pow hd₁]
      · simp [zero_pow hd₁]
  have has_subst_map_aux : HasSubst map_aux := by
    refine hasSubst_of_constantCoeff_zero ?_
    intro s
    fin_cases s
    all_goals simp [map_aux]
  /- prove that F(F(X,0),0) = F(X, F(0, 0)). -/
  have eq_aux₁ : subst map_aux (subst (subst_sec F.toFun) F.toFun) =
    subst map_aux (subst (subst_fir F.toFun) F.toFun) := by
    rw [assoc_eq]
  have left_eq : subst map_aux (subst (subst_sec F.toFun) F.toFun) =
    ((PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) ∘
    (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R))) PowerSeries.X := by
    simp
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_sec F.toFun F.zero_constantCoeff) has_subst_map_aux]
    rw [PowerSeries.subst, subst_comp_subst_apply (has_subst_X₁) (PowerSeries.HasSubst.const has_subst_aux)]
    apply subst_congr
    funext s
    fin_cases s
    · -- the cases s = 0
      simp [subst_X₁, subst_sec]
      rw [subst_X has_subst_map_aux]
      simp [map_aux, ←coe_substAlgHom (PowerSeries.HasSubst.const has_subst_aux), map_zero]
    · -- the cases s = 1
      simp [subst_X₁,subst_sec]
      rw [PowerSeries.X, subst_X (PowerSeries.HasSubst.const has_subst_aux), subst_comp_subst_apply
        has_subst_sec_aux has_subst_map_aux]
      apply subst_congr
      funext t
      fin_cases t
      all_goals simp [map_aux, subst_X has_subst_map_aux]
  have right_eq : subst map_aux (subst (subst_fir F.toFun) F.toFun) =
    (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) PowerSeries.X := by
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_fir F.toFun (F.zero_constantCoeff)) has_subst_map_aux]
    apply subst_congr
    funext s
    fin_cases s
    · -- the cases s = 0
      simp [subst_X₁, subst_fir]
      rw [subst_comp_subst_apply has_subst_fir_aux has_subst_map_aux]
      have eq_aux₃ :  subst (0 : Fin 2 → PowerSeries R) F.toFun = 0 := by
        have aux : HasSubst (0 : Fin 2 → PowerSeries R) := by
          exact hasSubst_of_constantCoeff_zero (congrFun rfl)
        ext n
        rw [PowerSeries.coeff, coeff_subst aux]
        simp
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        by_cases hd₀ : d = 0
        · simp [hd₀, F.zero_constantCoeff]
        · -- the case d ≠ 0
          have dneq : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
            by_contra hc
            simp at hc
            have deq : d = 0 := by
              refine (Finsupp.ext ?_)
              intro n
              fin_cases n
              all_goals simp [hc]
            contradiction
          obtain hd₁ | hd₁ := dneq
          · simp [zero_pow hd₁]
          · simp [zero_pow hd₁]
      rw [←eq_aux₃]
      apply subst_congr
      funext t
      fin_cases t
      · simp [map_aux]
        rw [subst_X has_subst_map_aux]
      · -- the case t = 1
        simp [map_aux]
        rw [subst_X has_subst_map_aux]
    · -- the cases s = 1
      simp [subst_X has_subst_map_aux, map_aux]
  rw [left_eq, right_eq] at eq_aux₁
  funext g
  have eq_aux₂ : g = PowerSeries.subst PowerSeries.X g := by
    simp [←PowerSeries.map_algebraMap_eq_subst_X]
  nth_rw 2 [eq_aux₂]
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X') has_subst_aux, ←right_eq,
    assoc_eq, left_eq]
  simp
  rw [PowerSeries.subst_X has_subst_aux, PowerSeries.subst_comp_subst_apply has_subst_aux has_subst_aux]



/-- Given a power series `f`, if substition `f` into any power series is identity, then `f = X`-/
lemma PowerSeries.subst_eq_id_iff_eq_X (f : PowerSeries R) (hf : HasSubst f) :
  PowerSeries.subst f = id ↔ f = PowerSeries.X := by
  constructor
  · intro h
    rw [←subst_X hf (R := R), h, id_eq]
  · intro h
    rw [h]
    funext g
    simp [←map_algebraMap_eq_subst_X]


/--
  Given a formal group law F, F(X,0) = X.
 -/
theorem FormalGroup.subst_X_eq_X  :
  subst subst_X₀ F.toFun = PowerSeries.X (R := R) := by
  have h₀ : IsUnit (PowerSeries.coeff R 1 (subst subst_X₀ F.toFun)) := by
    simp [coeff_of_X₀_of_subst_X₀]
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := PowerSeries.exist_subst_inv _  h₀ constantCoeff_of_subst_X₀
  have eq_aux :
    (PowerSeries.subst g) ∘ (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) ∘
    (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) =
    (PowerSeries.subst g) ∘
    (PowerSeries.subst (subst subst_X₀ F.toFun : PowerSeries R) (R := R)) := by
    rw [self_comp_aux]
  simp [←Function.comp_assoc, hg₂] at eq_aux
  exact (PowerSeries.subst_eq_id_iff_eq_X (subst subst_X₀ F.toFun)
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_of_subst_X₀))).mp eq_aux


/-- Given a formal group law F, F(0, X) = X. -/
theorem FormalGroup.subst_X₁_eq_X₁ :
  subst subst_X₁ F.toFun = PowerSeries.X (R := R) := by
  have h₀ : IsUnit (PowerSeries.coeff R 1 (subst subst_X₁ F.toFun)) := by
    simp [coeff_of_X₁_of_subst_X₁]
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := PowerSeries.exist_subst_inv _  h₀ constantCoeff_of_subst_X₁
  have eq_aux :
    (PowerSeries.subst g) ∘ (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) ∘
    (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) =
    (PowerSeries.subst g) ∘
    (PowerSeries.subst (subst subst_X₁ F.toFun : PowerSeries R) (R := R)) := by
    rw [self_comp_aux']
  simp [←Function.comp_assoc, hg₂] at eq_aux
  exact (PowerSeries.subst_eq_id_iff_eq_X (subst subst_X₁ F.toFun)
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_of_subst_X₁))).mp eq_aux


/-- Let `G₁, G₂` be two formal group laws over `CommRing A`. A homomorphism (over `A`)
  `F (X, Y) → G (X, Y)` is a power series `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` with coefficients
  in `A` without constant term such that `α(F (X, Y)) = G (α (X), α (Y))`. -/
@[ext]
structure FormalGroupHom  (G₁ G₂ : FormalGroup R) where
  toFun : PowerSeries R
  zero_constantCoeff : PowerSeries.constantCoeff R toFun = 0
  hom : PowerSeries.subst (G₁.toFun) toFun = subst (R := R) toFun.toMvPowerSeries G₂.toFun

end

section FormalGroupIso

open PowerSeries

-- create a section

/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if there exists a
  homomorphism `β(X) : G (X, Y) → F (X, Y)` such that `α ∘ β = id,  β ∘ α = id`. -/
@[ext]
structure FormalGroupIso (G₁ G₂ : FormalGroup R) where
  toHom : FormalGroupHom G₁ G₂
  invHom : FormalGroupHom G₂ G₁
  left_inv : (PowerSeries.subst toHom.toFun) ∘ (PowerSeries.subst invHom.toFun) = id
  right_inv : (PowerSeries.subst invHom.toFun) ∘ (PowerSeries.subst toHom.toFun) = id

/-- An isomorphism `α(X) : F (X, Y) → G (X, Y)`, `α(X) = a₁ * X + a₂ * X ^ 2 + ⋯`
  is called strict isomorphism if `a₁ = 1`.-/
@[ext]
structure FormalGroupStrictIso (G₁ G₂ : FormalGroup R) extends FormalGroupIso G₁ G₂ where
  one_coeff_one : coeff R 1 toHom.toFun = 1

theorem FormalGroupStrictIso.ext_iff' (G₁ G₂ : FormalGroup R) (α β : FormalGroupStrictIso G₁ G₂) :
  α = β ↔  α.toHom = β.toHom := by
  constructor
  · intro h
    rw [h]
  · intro h
    refine FormalGroupStrictIso.ext h ?_
    have eq_aux₁ : (PowerSeries.subst α.toHom.toFun) ∘ (PowerSeries.subst α.invHom.toFun) = id := by
      exact α.left_inv
    rw [h] at eq_aux₁
    have eq_aux₂ : (PowerSeries.subst β.toHom.toFun) ∘ (PowerSeries.subst β.invHom.toFun) = id := by
      exact β.left_inv
    have eq_aux₃ : α.invHom.toFun = β.invHom.toFun := by
      obtain ⟨g, h₁, h₂⟩ := exist_unique_subst_inv_left _ (by simp [β.one_coeff_one])
        β.toHom.zero_constantCoeff
      simp at h₂
      rw [h₂ _ eq_aux₁ α.invHom.zero_constantCoeff, h₂ _ eq_aux₂ β.invHom.zero_constantCoeff]
    exact FormalGroupHom.ext eq_aux₃

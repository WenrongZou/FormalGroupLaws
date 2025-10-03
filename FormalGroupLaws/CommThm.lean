import FormalGroupLaws.Basic
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Nilpotent.Lemmas

open Submodule MvPowerSeries

noncomputable section

/- Main Result : In this file, we prove that for any one dimensional formal group law `F(X, Y)`
  over coefficient ring `R`, `F(X, Y)` is commutative formal group law if and
  only if `R` doest contain a nonzero element which is both torsion and nilpotent.-/

variable {R : Type*} [CommRing R] (F : FormalGroup R)

namespace FormalGroup

abbrev coeff_two (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

lemma HasSubst_subst_symm : HasSubst (subst_symm (R := R)):= by
  apply hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  all_goals simp [subst_symm]


/-- For any formal group law `F(X,Y)`, `F(X,Y) = F(Y,X)` if and only if
  for any `i, j ∈ ℕ`, `a_ij = a_ji`, where `a_ij` is coefficient of `X^i Y^j`. -/
theorem comm_iff_coeff_symm :
  F.comm ↔ ∀ (i j : ℕ), coeff _ (coeff_two i j) F.toFun = coeff _ (coeff_two j i) F.toFun := by
  constructor
  -- forward direction
  · intro h i j
    obtain h' := MvPowerSeries.ext_iff.mp h (coeff_two i j)
    rw [h', coeff_subst HasSubst_subst_symm]
    simp [subst_symm]
    have aux : (coeff R (coeff_two i j)) (X₁ ^ j * X₀ ^ i) = 1 := by
      have aux' : (X₁ (R := R)) ^ j * (X₀ (R := R)) ^ i = monomial R (coeff_two i j) 1 := by
        simp [coeff_two, X_pow_eq, monomial_mul_monomial]
        simp [monomial_def, add_comm]
      rw [aux', coeff_monomial, if_pos (by simp)]
    rw [finsum_eq_single _ (coeff_two j i)]
    · simp [aux]
    · intro n hn
      have aux₁ : (coeff R (coeff_two i j)) (X₁ ^ n 0 * X₀ ^ n 1) = 0 := by
        have eq_aux : ((X₁ (R := R)) ^ n 0 * (X₀ (R := R)) ^ n 1) = monomial R (Finsupp.single 0 (n 1)
          + Finsupp.single 1 (n 0)) 1 := by
          simp [X_pow_eq, monomial_mul_monomial]
          simp [monomial_def, add_comm]
        rw [eq_aux, coeff_monomial, if_neg]
        obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hn
        refine Finsupp.ne_iff.mpr ?_
        fin_cases a
        · simp at ha
          use 1
          simp [Ne.symm ha]
        · simp at ha
          use 0
          simp [Ne.symm ha]
      simp [aux₁]
  · sorry

/--  Over a coefficient ring `R` of characteristic zero,
if `R` contains no nonzero element that is both torsion and nilpotent,
then any one-dimensional formal group law over `R` is commutative. -/
theorem comm_of_char_zero_and_no_torsion_nilpotent (h : ringChar R = 0) :
  ¬ ∃ r : R, r ≠ 0 ∧ IsNilpotent r ∧ addOrderOf r ≠ 0 → F.comm := by
  sorry

/-- Given a formal group law `F(X,Y)`, assume that `F(X,Y)` is not commutative, then
  there exist a nonzero formal group homomorphism from `F(X,Y)` to additive formal
  group law `Gₐ` or multiplicative formal group law `Gₘ`.-/
theorem exists_nonzero_hom_to_Ga_or_Gm_of_not_comm (h : ¬ F.comm) :
  (∃ (α : FormalGroupHom F (Gₐ (R := R))), α.toFun ≠ 0) ∨
  (∃ (α : FormalGroupHom F (Gₘ (R := R))), α.toFun ≠ 0) := sorry


/-- Assume that `R` is an integral domain, `F(X,Y)` and `F'(X,Y)` are one dimensional
  formal group law over `R`, if `F'(X,Y)` is commutative and there exist a nonzero
  homomorphism from `F(X,Y)` to `F'(X,Y)`, then `F(X,Y)` is commutative.-/
theorem comm_of_exists_nonzero_hom_to_comm (F' : FormalGroup R) [IsDomain R]
  (h : ∃ (α : FormalGroupHom F F'), α.toFun ≠ 0) :
  F'.comm → F.comm :=
  sorry

/-- Assume that `R` is an integral domain, any one dimensional formal group law is
  commutative. -/
theorem comm_of_isDomain [IsDomain R] : F.comm := by
  by_contra hc
  obtain h | h := exists_nonzero_hom_to_Ga_or_Gm_of_not_comm F hc
  · exact hc ((comm_of_exists_nonzero_hom_to_comm _ _ h ) Gₐ.comm)
  · exact hc ((comm_of_exists_nonzero_hom_to_comm _ _ h ) Gₘ.comm)


theorem no_nonzero_torsion_nilpotent_of_comm :
  F.comm →  ¬ (∃ r : R, IsNilpotent r ∧ addOrderOf r ≠ 0 ∧ r ≠ 0) := by
  rintro h_comm ⟨r, rNil, rTor, rneq⟩
  obtain ⟨m, hm⟩ := rNil
  have addOrder_ge_two : addOrderOf r ≥ 2 := by
    have addOrder_neq : addOrderOf r ≠ 1 := by
      by_contra hc; simp at hc; contradiction
    omega

  sorry

#check nilpotent_iff_mem_prime

/-- for any one dimensional formal group law `F(X, Y)`
  over coefficient ring `R`, `F(X, Y)` is commutative formal group law if and
  only if `R` does not contain a nonzero element which is both torsion and nilpotent.-/
theorem comm_iff_no_nonzero_torsion_nilpotent :
  F.comm ↔ ¬ (∃ r : R,  IsNilpotent r ∧ addOrderOf r ≠ 0 ∧ r ≠ 0) := by
  constructor
  · exact fun a ↦ no_nonzero_torsion_nilpotent_of_comm F a
  · intro hr
    simp at hr

    sorry

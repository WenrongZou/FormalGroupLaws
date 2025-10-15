import FormalGroupLaws.Basic
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.GroupTheory.OrderOfElement

open Submodule MvPowerSeries TensorProduct LinearMap

noncomputable section

/- Main Result : In this file, we prove that for any one dimensional formal group law `F(X, Y)`
  over coefficient ring `R`, `F(X, Y)` is commutative formal group law if and
  only if `R` doest contain a nonzero element which is both torsion and nilpotent.-/

variable {R : Type*} [CommRing R] (F : FormalGroup R)

namespace FormalGroup


/-- For any formal group law `F(X,Y)`, `F(X,Y) = F(Y,X)` if and only if
  for any `i, j ∈ ℕ`, `a_ij = a_ji`, where `a_ij` is coefficient of `X^i Y^j`. -/
theorem comm_iff_coeff_symm :
  F.comm ↔ ∀ (i j : ℕ), coeff (coeff_two i j) F.toFun = coeff (coeff_two j i) F.toFun := by
  constructor
  -- forward direction
  · intro h i j
    obtain h' := MvPowerSeries.ext_iff.mp h (coeff_two i j)
    rw [h', coeff_subst HasSubst_subst_symm]
    simp [subst_symm]
    have aux : (coeff (coeff_two i j)) ((X₁ (R := R)) ^ j * X₀ ^ i)  = 1 := by
      simp [coeff_two, X_pow_eq, monomial_mul_monomial]
      rw [coeff_monomial, if_pos (by rw [add_comm])]
    rw [finsum_eq_single _ (coeff_two j i)]
    · simp [aux]
    · intro n hn
      have aux₁ : (coeff (coeff_two i j)) ((X₁ (R := R)) ^ n 0 * X₀ ^ n 1) = 0 := by
        simp [X_pow_eq, monomial_mul_monomial]
        rw [coeff_monomial, if_neg]
        obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hn
        refine Finsupp.ne_iff.mpr ?_
        fin_cases a
        · simp at ha; use 1; simp [Ne.symm ha]
        · simp at ha; use 0; simp [Ne.symm ha]
      simp [aux₁]
  -- backward direction
  · intro h; ext n
    have n_eq : n = coeff_two (n 0) (n 1) := by
      refine Finsupp.ext ?_
      intro a; fin_cases a; all_goals simp [coeff_two]
    nth_rw 1 [n_eq]
    rw [h, coeff_subst HasSubst_subst_symm, finsum_eq_single _  (coeff_two (n 1) (n 0))]
    · simp [subst_symm]
      have aux : (coeff n) ((X₁ (R := R)) ^ n 1 * X₀ ^ n 0) = 1 := by
        simp [X_pow_eq, monomial_mul_monomial]
        rw [coeff_monomial, if_pos]
        refine Finsupp.ext ?_
        intro a; fin_cases a; all_goals simp
      simp [aux]
    · intro d hd; simp [subst_symm]
      have aux : (coeff n) ((X₁ (R := R)) ^ d 0 * X₀ ^ d 1) = 0 := by
        simp [X_pow_eq, monomial_mul_monomial]
        rw [coeff_monomial, if_neg]
        obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hd
        refine Finsupp.ne_iff.mpr ?_
        fin_cases a
        · simp at ha; use 1; simp [Ne.symm ha]
        · simp at ha; use 0; simp [Ne.symm ha]
      simp [aux]

/-- For any formal group law `F(X,Y)`, `F(X,Y) = F(Y,X)` if and only if
  for any `i, j ∈ ℕ`, `a_ij - a_ji = 0`, where `a_ij` is coefficient of `X^i Y^j`. -/
theorem comm_iff_coeff_symm' :
  F.comm ↔ ∀ (i j : ℕ), coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun = 0 := by
  constructor
  · intro hF
    simp_rw [(comm_iff_coeff_symm F).mp hF]
    exact fun i j => by ring
  · intro h
    apply ((comm_iff_coeff_symm F).mpr)
    intro i j
    conv => rhs; rw [←add_zero ((coeff (coeff_two j i)) F.toFun), ←h i j]
    ring

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
  (∃ (α : FormalGroupHom F (Gₘ (R := R))), α.toFun ≠ 0) := by
  sorry


/-- Assume that `R` is an integral domain, `F(X,Y)` and `F'(X,Y)` are one dimensional
  formal group law over `R`, if `F'(X,Y)` is commutative and there exist a nonzero
  homomorphism from `F(X,Y)` to `F'(X,Y)`, then `F(X,Y)` is commutative.-/
theorem comm_of_exists_nonzero_hom_to_comm (F' : FormalGroup R) [IsDomain R]
  (h : ∃ (α : FormalGroupHom F F'), α.toFun ≠ 0) :
  F'.comm → F.comm := by
  sorry

/-- Assume that `R` is an integral domain, any one dimensional formal group law is
  commutative. -/
theorem comm_of_isDomain [IsDomain R] : F.comm := by
  by_contra hc
  obtain h | h := exists_nonzero_hom_to_Ga_or_Gm_of_not_comm F hc
  · exact hc ((comm_of_exists_nonzero_hom_to_comm _ _ h ) Gₐ.comm)
  · exact hc ((comm_of_exists_nonzero_hom_to_comm _ _ h ) Gₘ.comm)



def counter_example_F (r : R) (rNil : IsNilpotent r) (rTor : IsOfFinAddOrder r)
  (rNeq : r ≠ 0) :
  FormalGroup R where
  toFun := by
    let n := addOrderOf r
    have ngtone : n ≠ 1 := by
      by_contra hn; simp [n] at hn; contradiction
    obtain p := Nat.minFac n
    let b := (n / p) • r
    have bNil : IsNilpotent b := by sorry
    let m := nilpotencyClass b
    let c := b ^ (m - 1)
    exact X₀ + X₁ + (C c) * X₀ * X₁ ^ p
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp
    rw [coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp))]
    rw [X₀, X, X_pow_eq, mul_assoc, monomial_mul_monomial]
    simp
    have aux' : ((addOrderOf r / (addOrderOf r).minFac) : MvPowerSeries (Fin 2) R) =
      C (addOrderOf r / (addOrderOf r).minFac) (R := R) := by
      exact rfl
    have aux : (((addOrderOf r / (addOrderOf r).minFac) : MvPowerSeries (Fin 2) R) * C r) ^
      (nilpotencyClass (↑(addOrderOf r / (addOrderOf r).minFac) * r) - 1) =
      C ((((addOrderOf r / (addOrderOf r).minFac) : R) * r) ^
      (nilpotencyClass (↑(addOrderOf r / (addOrderOf r).minFac) * r) - 1))  := by
      rw [aux']
      have aux'' : (C (addOrderOf r / (addOrderOf r).minFac : R) * C r)
        = C (((addOrderOf r / (addOrderOf r).minFac : R) * r)) (R := R) (σ := Fin 2) := by
        simp
      rw [aux'', map_pow]
    rw [aux, coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    simp
    have addOrderNeq : (addOrderOf r) ≠ 1 := by
      simp [rNeq]
    refine Nat.ne_zero_iff_zero_lt.mpr (Nat.minFac_pos _)
  lin_coeff_Y := sorry
  assoc := sorry


theorem no_nonzero_torsion_nilpotent_of_comm :
  (∀ (F : FormalGroup R), F.comm) →  ¬ (∃ r : R, IsNilpotent r ∧ addOrderOf r ≠ 0 ∧ r ≠ 0) := by
  contrapose
  intro h
  simp at h
  obtain ⟨r, rNil, rTor, rNeq⟩ := h
  simp
  use (counter_example_F r rNil rTor rNeq)
  -- rintro h_comm ⟨r, rNil, rTor, rneq⟩
  -- obtain ⟨m, hm⟩ := rNil
  -- have addOrder_ge_two : addOrderOf r ≥ 2 := by
  --   have addOrder_neq : addOrderOf r ≠ 1 := by
  --     by_contra hc; simp at hc; contradiction
  --   omega

  sorry


variable (R) in
/--
The canonical `ℤ`-linear map from a ring `R` to `R ⊗[ℤ] ℚ`
that sends an element `r` to `r ⊗ 1`.
-/
def canonicalMapToTensorRat : R →ₗ[ℤ] (R ⊗[ℤ] ℚ) :=
  {
      toFun := fun r => r ⊗ₜ[ℤ] (1 : ℚ)
      map_add' := by
        intros x y
        simp [TensorProduct.add_tmul]
      map_smul' := by
        intros n x
        simp [TensorProduct.smul_tmul']
    }

/--
The kernel of the canonical map `r ↦ r ⊗ 1` from a ring `R` to `R ⊗[ℤ] ℚ`
is precisely the `ℤ`-torsion submodule of `R`.
-/
theorem kernel_canonicalMapToTensorRat_eq_torsion :
  ker (canonicalMapToTensorRat R) = torsion ℤ R := by
  refine Submodule.ext ?_
  intro x
  constructor
  · intro hx
    refine (mem_torsion_iff x).mpr ?_
    have aux : (canonicalMapToTensorRat R) x = 0 := by
      exact hx
    simp [canonicalMapToTensorRat] at aux

    sorry
  · intro hx
    simp [canonicalMapToTensorRat]
    obtain ⟨a, ha⟩ := (mem_torsion_iff x).mp hx
    calc
      _ = (a • x) ⊗ₜ (1 / (a : ℚ)) := by
        rw [smul_tmul]
        have aux : (a • (1 / (a : ℚ))) = 1 := by
          calc
            _ = a * (a : ℚ)⁻¹ := by
              aesop
            _ = 1 := by
              simp
        rw [aux]
      _ = 0 := by
        simp only [ha, one_div, zero_tmul]


lemma lem2 :
  ∀ x, x ∈ torsion ℤ R ↔ addOrderOf x ≠ 0 := by
  intro x
  constructor
  ·
    intro hx
    simp at hx
    obtain ⟨a, ha₁, ha₂⟩ := hx

    sorry
  · sorry

lemma lem1 : ringChar (Localization.Away (0 : R)) = 0 := by
  refine (CharP.ringChar_zero_iff_CharZero (Localization.Away 0)).mpr ?_
  refine charZero_of_inj_zero ?_
  intro n hn
  sorry


/-- for any one dimensional formal group law `F(X, Y)`
  over coefficient ring `R`, `F(X, Y)` is commutative formal group law if and
  only if `R` does not contain a nonzero element which is both torsion and nilpotent.-/
theorem comm_iff_no_nonzero_torsion_nilpotent :
  (∀ (F : FormalGroup R), F.comm) ↔ ¬ (∃ r : R,  IsNilpotent r ∧ addOrderOf r ≠ 0 ∧ r ≠ 0) := by
  constructor
  ·  exact fun a ↦ no_nonzero_torsion_nilpotent_of_comm a
  · intro hr F
    simp at hr
    have mem_ideal : ∀ (i j : ℕ), ∀ (I : Ideal R), I.IsPrime →
      (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun) ∈ I := by
      intro i j I hI
      let f := Ideal.Quotient.mk I
      let f_F := F.map f
      obtain h₁ := comm_of_isDomain f_F
      exact (Quotient.mk_eq_zero I).mp ((comm_iff_coeff_symm' f_F).mp h₁ i j)
    have mem_nilpotent : ∀ (i j : ℕ),
      IsNilpotent (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun) :=
      fun i j => nilpotent_iff_mem_prime.mpr (mem_ideal i j)
    have mem_torsion : ∀ (i j : ℕ),
      IsOfFinAddOrder (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun)  := by
      intro i j

      sorry
    have mem_zero : ∀ (i j : ℕ),
      (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun) = 0 :=
      fun i j => hr _ (mem_nilpotent i j) (mem_torsion i j)
    exact (comm_iff_coeff_symm' F).mpr mem_zero

import FormalGroupLaws.Basic
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.TensorProduct.Basic
import FormalGroupLaws.AddInverse

noncomputable section

/- Main Result : In this file, we prove that for any one dimensional formal group law `F(X, Y)`
  over coefficient ring `R`, `F(X, Y)` is commutative formal group law if and
  only if `R` doest contain a nonzero element which is both torsion and nilpotent.-/

variable {R : Type*} [CommRing R] (F : FormalGroup R) [Nontrivial R]

namespace FormalGroup

open Submodule MvPowerSeries TensorProduct LinearMap

omit [Nontrivial R] in
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

omit [Nontrivial R] in
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


/-- This is a counter example that given `r` is a nonzero nilpotent and `ℤ-torsion`,
  there is a non-commutative formal group law. -/
def counter_example_F (r : R) (rNil : IsNilpotent r) (rTor : IsOfFinAddOrder r)
  (rNeq : r ≠ 0) :
  FormalGroup R :=
  let n := addOrderOf r
  have ngtone : n ≠ 1 := by
    by_contra hn; simp [n] at hn; contradiction
  let p := Nat.minFac n
  let b := (n / p) • r
  have bNil : IsNilpotent b := IsNilpotent.smul rNil (n / p)
  let m := nilpotencyClass b
  let c := b ^ (m - 1)
  have bneq₀ : b ≠ 0 := by
    have pos_aux : n / p > 0 := Nat.div_pos_iff.mpr
      ⟨Nat.minFac_pos n, Nat.minFac_le (IsOfFinAddOrder.addOrderOf_pos rTor)⟩
    obtain neq := Nat.ne_zero_of_lt pos_aux
    refine nsmul_ne_zero_of_lt_addOrderOf neq (Nat.div_lt_self
      (IsOfFinAddOrder.addOrderOf_pos rTor) ?_)
    exact Nat.Prime.one_lt (Nat.minFac_prime_iff.mpr ngtone)
  {
  toFun := by
    let n := addOrderOf r
    have ngtone : n ≠ 1 := by
      by_contra hn; simp [n] at hn; contradiction
    obtain p := Nat.minFac n
    let b := (n / p) • r
    have bNil : IsNilpotent b := IsNilpotent.smul rNil (n / p)
    let m := nilpotencyClass b
    let c := b ^ (m - 1)
    exact X₀ + X₁ + (C c) * X₀ * X₁ ^ p
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp
    rw [coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp)),
      X₀, X, X_pow_eq, mul_assoc, monomial_mul_monomial]
    simp
    have aux' : ((addOrderOf r / (addOrderOf r).minFac) : MvPowerSeries (Fin 2) R) =
      C (addOrderOf r / (addOrderOf r).minFac) (R := R) := by
      exact rfl
    have aux'' : (C (addOrderOf r / (addOrderOf r).minFac : R) * C r)
      = C (((addOrderOf r / (addOrderOf r).minFac : R) * r)) (R := R) (σ := Fin 2) := by
      simp
    rw [aux', aux'', ←map_pow, coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    simp
    refine Nat.ne_zero_iff_zero_lt.mpr (Nat.minFac_pos _)
  lin_coeff_Y := by
    simp
    rw [coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp)),
      X₀, X, X_pow_eq, mul_assoc, monomial_mul_monomial]
    simp
    have aux' : ((addOrderOf r / (addOrderOf r).minFac) : MvPowerSeries (Fin 2) R) =
      C (addOrderOf r / (addOrderOf r).minFac) (R := R) := by
      exact rfl
    have aux'' : (C (addOrderOf r / (addOrderOf r).minFac : R) * C r)
      = C (((addOrderOf r / (addOrderOf r).minFac : R) * r)) (R := R) (σ := Fin 2) := by
      simp
    rw [aux', aux'', ←map_pow, coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    refine Finsupp.ne_iff.mpr ?_
    use 1
    simp
    by_contra hc
    obtain hc' := Nat.minFac_eq_one_iff.mp (Eq.symm hc)
    simp at hc'
    contradiction
  assoc := by
    simp only
    rw [show addOrderOf r = n by rfl, show (n / p) • r = b by rfl, show nilpotencyClass b = m by rfl,
      show n.minFac = p by rfl, show b ^ (m - 1) = c by rfl]
    obtain has_subst₁ := has_subst_fir (X₀ + X₁ + c • X₀ * X₁ ^ p) (R := R) (by simp)
    obtain has_subst₂ := has_subst_sec (X₀ + X₁ + c • (X₀ * X₁ ^ p)) (R := R)  (by simp)
    rw [←smul_eq_C_mul, subst_add has_subst₁, subst_add has_subst₁, subst_mul has_subst₁, subst_X has_subst₁,
      subst_X has_subst₁, subst_smul has_subst₁, subst_X has_subst₁,
      subst_pow has_subst₁, subst_X has_subst₁]
    simp [subst_fir]
    simp_rw [subst_add has_subst_fir_aux, subst_smul has_subst_fir_aux, subst_mul has_subst_fir_aux,
      subst_pow has_subst_fir_aux, subst_X has_subst_fir_aux, subst_fir_aux]
    simp_rw [subst_add has_subst₂, subst_smul has_subst₂, subst_mul has_subst₂,
      subst_pow has_subst₂, subst_X has_subst₂, subst_sec, subst_add has_subst_sec_aux,
      subst_smul has_subst_sec_aux, subst_mul has_subst_sec_aux, subst_pow has_subst_sec_aux,
      subst_X has_subst_sec_aux, subst_sec_aux]
    have pPrime : p.Prime := Nat.minFac_prime_iff.mpr ngtone
    have mgetwo : m ≥ 2 := by
      obtain mneq₀ := pos_nilpotencyClass_iff.mpr bNil
      have mneq₁ : m ≠ 1 := by
        by_contra hc
        obtain hc' := nilpotencyClass_eq_one.mp hc
        contradiction
      omega
    have cpow_aux : c ^ 2 = 0 := by
      rw [show c = b ^ (m - 1) by rfl, ←pow_mul]
      have bNil' : b ^ m = 0 := pow_nilpotencyClass bNil
      have le_aux : m ≤ (m - 1) * 2 := by omega
      exact pow_eq_zero_of_le le_aux bNil'
    have aux : (C c (σ := Fin 3)) ^ 2  = 0 := by
      simp [←map_pow, cpow_aux]
    have cpow_zero : c ^ p = 0 := by
      exact pow_eq_zero_of_le (Nat.Prime.two_le pPrime) cpow_aux
    have cTor : p * c = 0 := by
      have aux' : p * b = 0 := by
        simp [show b = (n / p) • r by rfl, ←mul_assoc]
        have : (p : R) * ↑(n / p) = n := by
          norm_cast
          congr
          exact Nat.mul_div_cancel' (Nat.minFac_dvd n)
        obtain h₁ := addOrderOf_nsmul_eq_zero r
        simp at h₁
        rw [this, h₁]
      have add_aux : m - 1 = 1 + (m - 2) := by
        omega
      rw [show c = b ^ (m - 1) by rfl, add_aux, pow_add]
      ring_nf
      simp [aux']
    have eq_aux₁ : c • ((Y₀ + Y₁ + c • (Y₀ * Y₁ ^ p)) * Y₂ ^ p) =
      c • Y₀ * (Y₂ (R := R)) ^ p + c • Y₁ * Y₂ ^ p := by
      simp [smul_eq_C_mul]
      ring_nf
      simp [aux]
    have eq_aux₂ : c • (Y₀ * (Y₁ + Y₂ + c • (Y₁ * Y₂ ^ p)) ^ p) =
      c • Y₀ * (Y₁ (R := R)) ^ p + c • Y₀ * Y₂ ^ p := by
      simp [smul_eq_C_mul]
      ring_nf
      have C_mul_p_aux : C c * (p : MvPowerSeries (Fin 3) R) =
        C (p * c) := by
        simp [mul_comm]
      have eq_aux : (C c * (Y₁ (R := R)) * Y₂ ^ p + Y₁ + Y₂) ^ p =
        ∑ m ∈ Finset.range (p + 1), Y₁ ^ m * Y₂ ^ (p - m)
        * (p.choose m : MvPowerSeries (Fin 3) R) := by
        rw [add_pow, Finset.sum_congr rfl]
        intro i hi
        simp at hi
        by_cases hi_zero : i = 0
        · simp [hi_zero]
        by_cases hip : i = p
        · simp [hip]
          rw [add_pow, Finset.sum_eq_single 0]
          · simp
          · intro j hj₁ hj₂
            by_cases hjp : j = p
            · simp [hjp]
              rw [mul_pow, mul_pow, ←map_pow]
              simp [cpow_zero]
            simp at hj₁
            have pdvd : p ∣ p.choose j := Nat.Prime.dvd_choose_self pPrime (by omega) (by omega)
            obtain ⟨t, ht⟩ := pdvd
            rw [ht, show j = 1 + (j - 1) by omega, pow_add]
            simp
            calc
              _ = Y₁ * Y₂ ^ p * (C c * Y₁ * Y₂ ^ p) ^ (j - 1)
                * Y₁ ^ (p - (1 + (j - 1))) * (C c * ↑p * ↑t) := by
                ring
              _ = 0 := by
                simp [C_mul_p_aux, cTor]
          simp
        have pdvd : p ∣ p.choose i := Nat.Prime.dvd_choose_self pPrime hi_zero (by omega)
        obtain ⟨j, hj⟩ := pdvd
        rw [add_pow, Finset.sum_mul, Finset.sum_mul, Finset.sum_eq_single 0]
        · simp
        · intro b hb₁ hb₂
          nth_rw 1 [show b = b - 1 + 1 by omega]
          rw [hj, pow_add]
          calc
            _ = (C c * Y₁ * Y₂ ^ p) ^ (b - 1) * (Y₁ * Y₂ ^ p) * Y₁ ^ (i - b)
              * ↑(i.choose b) * Y₂ ^ (p - i) * ↑(C c * p * j) := by
              simp
              ring
            _ = 0 := by
              simp [C_mul_p_aux, cTor]
        · simp
      have pneq₀ : 0 ≠ p :=
          Ne.symm (Nat.Prime.ne_zero (Nat.minFac_prime_iff.mpr ngtone))

      rw [eq_aux, Finset.mul_sum, Finset.sum_eq_add_of_mem 0 p (by simp) (by simp) pneq₀]
      · simp
        ring
      · intro i hi₁ ⟨hi₂, hi₃⟩
        simp at hi₁
        have pdvd : p ∣ p.choose i := Nat.Prime.dvd_choose_self pPrime (by omega) (by omega)
        obtain ⟨t, ht⟩ := pdvd
        rw [ht]
        calc
          _ = (Y₀ (R := R)) * (Y₁ ^ i * Y₂ ^ (p - i) *
            ((C c (R := R)) * (p : MvPowerSeries (Fin 3) R))) * ↑t := by
            simp
            ring
          _ = 0 := by
            simp [C_mul_p_aux, cTor]
    simp_rw [eq_aux₁, eq_aux₂, smul_eq_C_mul]
    ring_nf
  }


/-- Given a coefficient ring `R`, if for any formal group law `F` over `R` is commutative,
  then this ring does not have a nonzero element is nilpotent and `ℤ`-torsion at the same time. -/
theorem no_nonzero_torsion_nilpotent_of_comm :
  (∀ (F : FormalGroup R), F.comm) →  ¬ (∃ r : R, IsNilpotent r ∧ addOrderOf r ≠ 0 ∧ r ≠ 0) := by
  contrapose
  intro h
  simp at h
  obtain ⟨r, rNil, rTor, rNeq⟩ := h
  simp
  use (counter_example_F r rNil rTor rNeq)
  intro hc
  let n := addOrderOf r
  have ngtone : n ≠ 1 := by
    by_contra hn; simp [n] at hn; contradiction
  let p := Nat.minFac n
  let b := (n / p) • r
  have bNil : IsNilpotent b := IsNilpotent.smul rNil (n / p)
  let m := nilpotencyClass b
  let c := b ^ (m - 1)
  have coeff_neq : (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
    (counter_example_F r rNil rTor rNeq).toFun ≠ (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
    (subst subst_symm (counter_example_F r rNil rTor rNeq).toFun) := by
    simp [counter_example_F, show addOrderOf r = n by rfl, show (n / p) • r = b by rfl, show nilpotencyClass b = m by rfl,
      show n.minFac = p by rfl, show b ^ (m - 1) = c by rfl]
    have eq_aux : subst subst_symm (X₀ + X₁ + C c * X₀ * X₁ ^ p) =
      (X₁) + X₀ + C c * X₁ * X₀ ^ p := by
      simp_rw [subst_add HasSubst_subst_symm, ←smul_eq_C_mul, subst_mul HasSubst_subst_symm,
        subst_smul HasSubst_subst_symm, subst_pow HasSubst_subst_symm, subst_X HasSubst_subst_symm]
    rw [eq_aux, coeff_X, if_neg, coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp))]
    simp
    rw [coeff_X, coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp)), if_neg ]
    simp [mul_assoc]
    have eq_aux₁ : (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
      ((X₀ (R := R)) * X₁ ^ p) = 1 := by
      simp [X_pow_eq, coeff_add_mul_monomial, coeff_X]
    have eq_aux₂ : (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
      ((X₁ (R := R)) * X₀ ^ p) = 0 := by
      rw [X_pow_eq, X₁, X, monomial_mul_monomial, coeff_monomial, if_neg]
      refine Finsupp.ne_iff.mpr ?_
      use 1
      simp
      exact Nat.Prime.ne_one (Nat.minFac_prime_iff.mpr ngtone)
    simp [eq_aux₁, eq_aux₂]
    exact pow_pred_nilpotencyClass bNil
    · simp
      exact (Nat.Prime.ne_zero (Nat.minFac_prime_iff.mpr ngtone))
    · refine Finsupp.ne_iff.mpr ?_
      use 1
      simp
      refine Nat.ne_zero_iff_zero_lt.mpr (Nat.minFac_pos (addOrderOf r))
  obtain hc' := MvPowerSeries.ext_iff.mp hc (Finsupp.single 0 1 + Finsupp.single 1 p)
  contradiction



variable (R) in
/--
The canonical `ℤ`-linear map from a ring `R` to `R ⊗[ℤ] ℚ`
that sends an element `r` to `r ⊗ 1`.
-/
def canonicalMapToTensorRat : R →ₐ[ℤ] (R ⊗[ℤ] ℚ) :=
  Algebra.TensorProduct.includeLeft

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


/-- Given a coefficient ring `R`, for any one dimensional formal group law `F(X, Y)`
  over `R`, `F(X, Y)` is commutative formal group law if and
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

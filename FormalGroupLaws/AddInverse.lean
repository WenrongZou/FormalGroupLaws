import FormalGroupLaws.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators

noncomputable section

variable {R : Type*} [CommRing R] [Nontrivial R] (f g : PowerSeries R) (F : FormalGroup R) {σ : Type*}
  (φ : MvPowerSeries (Fin 2) R) (n : ℕ)


open PowerSeries FormalGroup Finset

-- abbrev addInv_map : Fin 2 → PowerSeries R
--   | ⟨0, _⟩ => PowerSeries.X
--   | ⟨1, _⟩ => f

-- abbrev addInv_aux (F : FormalGroup R) : ℕ → R × (PowerSeries R)
--   | 0 => (0, 0)
--   | 1 => (-1, -PowerSeries.X)
--   | n + 1 => (- (PowerSeries.coeff (n + 1 : ℕ) (MvPowerSeries.subst
--     (addInv_map ((addInv_aux F n).2)) F.toFun)), (addInv_aux F n ).2 + PowerSeries.C
--     (- (PowerSeries.coeff (n + 1 : ℕ) (subst (addInv_map (addInv_aux F n).2) F.toFun)))
--     * (PowerSeries.X ^ (n + 1)))

abbrev addInv_aux (F : FormalGroup R): ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1 : ℕ) (MvPowerSeries.subst
    (subst_map₂ X (∑ i : Fin (n + 1), C (addInv_aux F i.1) * X ^ i.1)) F.toFun))

/-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `ι`,
  such that `F(X, ι(X)) = 0`. -/
def addInv_X := mk (fun n => (addInv_aux F n))

lemma Finset.sum_fin_eq_sum_range' {β : Type*} [AddCommMonoid β] {n : ℕ}  (f : ℕ → β):
  ∑ i : Fin n, f i.1 = ∑ i ∈ range n, f i := by
  rw [sum_fin_eq_sum_range, sum_congr rfl]
  intro i hi
  simp at hi
  rw [dif_pos hi]

omit [Nontrivial R] in
lemma HasSubst.addInv_aux : MvPowerSeries.HasSubst (subst_map₂ X (addInv_X F)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro x; fin_cases x
  · simp [subst_map₂]
  · simp [subst_map₂, addInv_X]; rfl

omit [Nontrivial R] in
lemma addInv_trunc_aux :
  trunc (n + 1) (addInv_X F) = ∑ i : Fin (n + 1), Polynomial.C (addInv_aux F i.1)
  * Polynomial.X ^ i.1
  := by
  induction n with
  | zero => simp [addInv_X]
  | succ k ih =>
    rw [trunc] at ⊢ ih
    simp_all
    rw [Finset.sum_range_add, ih]
    simp [sum_fin_eq_sum_range' (fun i => (Polynomial.C (R := R)) (addInv_aux F i)
      * Polynomial.X ^ i)] at ⊢ ih
    rw [sum_range_add _ (k + 1) 1]
    simp [Polynomial.X_pow_eq_monomial, addInv_X]


omit [Nontrivial R] in
lemma coeff_subst_map₂_eq_subst_subst_map₂_trunc :
  coeff n (MvPowerSeries.subst (subst_map₂ f g) φ) =
  coeff n (MvPowerSeries.subst (subst_map₂ (trunc (n + 1) f) (trunc (n + 1) g)) φ) := by

  sorry
omit [Nontrivial R] in
lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
  coeff n (MvPowerSeries.subst (subst_map₂ X (addInv_X F)) F.toFun) =
  coeff n (MvPowerSeries.subst (subst_map₂ X (trunc (n + 1) (addInv_X F))) F.toFun) := by
  have trunc_X_aux : trunc (n + 1) X = Polynomial.X (R := R):= by
    refine trunc_X_of ?_
    omega
  simp [coeff_subst_map₂_eq_subst_subst_map₂_trunc, trunc_X_aux]


-- lemma FormalGroup.coeff_X₀_pow {k : ℕ} (hk : k ≥ 2) :
--   MvPowerSeries.coeff (Finsupp.single 0 k) F.toFun = 0 := by
--   sorry



-- lemma FormalGroup.coeff_X₁_pow {k : ℕ} (hk : k ≥ 2) :
--   MvPowerSeries.coeff (Finsupp.single 1 k) F.toFun = 0 := by
--   sorry



lemma coeff_n_aux (n : ℕ):
  coeff n (MvPowerSeries.subst (subst_map₂ X (∑ i : Fin (n + 1),
  C (addInv_aux F i.1) * X ^ i.1)) F.toFun) = 0 := by
  rw [sum_fin_eq_sum_range' (fun i => (C (addInv_aux F i) * X ^ i))]
  induction n with
  | zero =>
    simp
    rw [constantCoeff, MvPowerSeries.constantCoeff_subst, show (addInv_aux F 0) = 0 by rfl]
    simp [subst_map₂]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d 0 ≠ 0
    · simp [hd₀]
    by_cases hd₁ : d 1 ≠ 0
    · simp [hd₁]
    have d_eq_zero : d = 0 := by ext x; fin_cases x <;> simp_all
    simp [d_eq_zero, F.zero_constantCoeff]
    · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      intro x
      fin_cases x
      all_goals simp [subst_map₂, show (addInv_aux F 0) = 0 by rfl]
  | succ k ih =>
    by_cases hk₀ : k = 0
    ·
      simp [hk₀, show range 2 = {0, 1} by rfl]

      rw [coeff, MvPowerSeries.coeff_subst]
      unfold addInv_aux
      simp [subst_map₂]
      have supp_eq : (Function.support (fun d => (MvPowerSeries.coeff d) F.toFun
        * (coeff 1) (X ^ d 0 * (-X) ^ d 1))) = {Finsupp.single (0 : Fin 2) 1,
        Finsupp.single (1 : Fin 2) 1}
        := by
        refine Function.support_eq_iff.mpr ?_
        constructor
        · intro x hx
          simp at hx
          obtain hx | hx := hx
          · simp [hx, F.lin_coeff_X]
          · simp [hx, F.lin_coeff_Y]
        intro  x hx
        simp at hx
        obtain ⟨neq₁, neq₂⟩ := hx
        by_cases hx₀ : x 0 = 0
        · by_cases hx₁ : x 1 = 0
          · have x_zero : x = 0 := by
              ext i; fin_cases i <;> simp [hx₀, hx₁]
            simp [x_zero, F.zero_constantCoeff]
          have xge₁ : x 1 ≥ 2 := by
            by_contra hc
            have xeq : x 1 = 1 := by omega
            have xeq' : x = Finsupp.single 1 1 := by
              ext i; fin_cases i <;> simp [hx₀, xeq]
            contradiction
          simp [hx₀, neg_pow X _]
          rw [coeff_mul_X_pow', if_neg (by linarith)]
          simp
        rw [coeff_X_pow_mul']
        by_cases hx₁ : x 0 = 1
        · rw [if_pos (by linarith)]
          by_cases hx₂ : x 1 = 0
          · have xeq : x = Finsupp.single 0 1 := by
              ext i; fin_cases i <;> simp [hx₂, hx₁]
            contradiction
          simp [hx₁, zero_pow hx₂]
        have xgt : ¬ x 0 ≤ 1 := by omega
        simp [if_neg xgt]
      have supp_fin : (Function.support (fun d => (MvPowerSeries.coeff d) F.toFun
        * (coeff 1) (X ^ d 0 * (-X) ^ d 1))).Finite := by
        simp [supp_eq]
      rw [finsum_eq_sum _ supp_fin]
      simp_all
      rw [sum_pair (Finsupp.ne_iff.mpr (by use 0; simp))]
      simp [F.lin_coeff_X, F.lin_coeff_Y]
      · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
        intro s; fin_cases s
        · rw [addInv_aux, subst_map₂]; simp
        · unfold addInv_aux subst_map₂
          simp
    have has_subst₁ (m : ℕ) : MvPowerSeries.HasSubst (subst_map₂ X (∑ i ∈ range (m + 1),
      C (addInv_aux F i) * X ^ i)) := by
      refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      intro x; fin_cases x
      · simp [subst_map₂]
      · simp [subst_map₂]
        refine sum_eq_zero ?_
        intro i hi
        by_cases hi₀ : i ≠ 0
        · simp [zero_pow hi₀]
        · simp_all
          rfl
    rw [coeff, MvPowerSeries.coeff_subst (has_subst₁ (k + 1))]
    simp_rw [PowerSeries.coeff_coe]
    simp [subst_map₂]
    generalize hB : ∑ i ∈ range (k + 1), C (addInv_aux F i) * X ^ i = B
    simp [sum_range_add, hB]
    have constantCoeff_of_B : constantCoeff B = 0 := by
      rw [←hB, map_sum]
      apply sum_eq_zero
      intro x hx
      rw [←smul_eq_C_mul, constantCoeff_smul, map_pow, constantCoeff_X, smul_eq_mul]
      by_cases hx' : x = 0
      · simp [hx', show addInv_aux F 0 = 0 by rfl]
      · simp [zero_pow hx']
    obtain has_subst' := has_subst₁ k
    rw [hB] at has_subst'
    have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) (X ^ d 0 *
      (B + C (addInv_aux F (k + 1)) * X ^ (k + 1)) ^ d 1) = (coeff (k + 1)) (X ^ d 0 * B ^ d 1)
      + if d = Finsupp.single 1 1 then (addInv_aux F (k + 1)) else 0 := by
      split_ifs with hd
      · simp [hd, ←hB, coeff_X_pow]
      rw [coeff_X_pow_mul', coeff_X_pow_mul']
      split_ifs with hd₁
      ·
        by_cases hd₂ : d 0 = 0
        ·
          simp [hd₂]
          rw [add_pow, map_sum, sum_eq_single (d 1)]
          simp
          · intro i hi₀ hi₁
            simp at hi₀
            rw [mul_pow, ←pow_mul, ←map_pow]
            calc
              _ = (coeff (k + 1)) (B ^ i * (C ((addInv_aux F (k + 1)) ^ (d 1 - i)) * X ^ ((k + 1)
                * (d 1 - i))) * (C ((d 1).choose i : R))) := by
                rfl
              _ = (coeff (k + 1)) (C ((addInv_aux F (k + 1)) ^ (d 1 - i))
                * (C ((d 1).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 1 - i))) := by
                ring_nf
              _ = _ := by
                rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow']
                by_cases hi' : i = d 1 - 1
                · have d_minus : d 1 - i = 1 := by omega
                  have ine_zero : i ≠ 0 := by
                    by_contra hc
                    have deq : d = Finsupp.single 1 1 := by
                      ext s; fin_cases s <;> simp [hd₂]; omega
                    contradiction
                  simp [d_minus, constantCoeff_of_B, zero_pow ine_zero]
                have d_minus_ge : d 1 - i ≥ 2 := by
                  omega
                have gt_aux : ¬ (k + 1) * (d 1 - i) ≤ k + 1 := by
                  simp
                  omega
                rw [if_neg gt_aux]
                simp
          simp
        -- have lt_aux : (k + 1 - d 0) < k + 1 := by omega
        rw [add_pow, map_sum, sum_eq_single (d 1)]
        · simp
        · intro i hi₀ hi₁
          simp at hi₀
          rw [mul_pow, ←pow_mul, ←map_pow]
          calc
            _ = (coeff (k + 1 - d 0)) (B ^ i * (C ((addInv_aux F (k + 1)) ^ (d 1 - i)) * X ^ ((k + 1)
              * (d 1 - i))) * (C ((d 1).choose i : R))) := by
              rfl
            _ = (coeff (k + 1 - d 0)) (C ((addInv_aux F (k + 1)) ^ (d 1 - i))
              * (C ((d 1).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 1 - i))) := by
              ring_nf
            _ = _ := by
              rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow', if_neg]
              · simp
              · simp
                calc
                  _ < k + 1 := by omega
                  _ ≤ _ := by
                    have le_aux : d 1 - i ≥ 1 := by omega
                    exact Nat.le_mul_of_pos_right (k + 1) le_aux
        · simp
      simp
    simp_rw [eq_aux, mul_add]
    rw [finsum_add_distrib]
    nth_rw 2 [finsum_eq_single _ (Finsupp.single 1 1)]
    rw [if_pos (by simp), F.lin_coeff_Y, addInv_aux,
      sum_fin_eq_sum_range' (fun i => (C (addInv_aux F i) * X ^ i)), hB, coeff, MvPowerSeries.coeff_subst has_subst']
    simp
    · simp [hk₀]
    · intro d hd
      simp [if_neg hd]
    · obtain h := MvPowerSeries.coeff_subst_finite (has_subst₁ k) F.toFun
      simp [hB, subst_map₂] at h
      exact h (Finsupp.single () (k + 1))
    · have aux : (Function.support fun d ↦
        (MvPowerSeries.coeff d) F.toFun * if d = Finsupp.single 1 1 then addInv_aux F (k + 1) else 0)
        ⊆ {Finsupp.single 1 1} := by
        refine Function.support_subset_iff'.mpr ?_
        intro d hd
        simp at hd
        simp [if_neg hd]
      exact Set.Finite.subset (Set.finite_singleton (Finsupp.single 1 1)) aux


/- Given a formal group law `F` over coefficient ring `R`, there exist a power series
  `addInv F`, such that `F(X, (addInv F)) = 0`. -/
theorem subst_addInv_eq_zero : MvPowerSeries.subst (subst_map₂ X (addInv_X F)) F.toFun = 0 := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
    rw [constantCoeff, MvPowerSeries.constantCoeff_subst (HasSubst.addInv_aux _)]
    simp
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d 0 ≠ 0
    · have eq_aux : constantCoeff (subst_map₂ X (addInv_X F) 0) = 0 := by
        simp [subst_map₂]
      simp [eq_aux, zero_pow hd₀]
    by_cases hd₁ : d 1 ≠ 0
    · have eq_aux : constantCoeff (subst_map₂ X (addInv_X F) 1) = 0 := by
        simp [subst_map₂, addInv_X]; rfl
      simp [eq_aux, zero_pow hd₁]
    simp_all
    have d_eq_zero : d = 0 := by
      ext x
      fin_cases x; all_goals simp [hd₀, hd₁]
    simp [d_eq_zero, F.zero_constantCoeff]
  simp
  rw [←(coeff_n_aux F n), coeff_subst_addInv_trunc _ _ hn]
  congr! 3
  unfold trunc
  simp_rw [←Polynomial.coe_C, ←Polynomial.coe_X]
  rw [sum_fin_eq_sum_range' (fun i => (Polynomial.C (addInv_aux F i) : PowerSeries R)
    * (Polynomial.X).toPowerSeries ^ i), Nat.Ico_zero_eq_range,
    ←Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_finset_sum, ←Polynomial.eval₂_C_X_eq_coe,
    sum_congr rfl]
  intro i hi
  rw [Polynomial.eval₂_C_X_eq_coe]
  simp [X_pow_eq, addInv_X]
  rw [←monomial_zero_eq_C_apply, monomial_mul_monomial]
  simp

-- /-- `-[F] f` means `FormalGroup.addInv F f`. -/
-- scoped[FormalGroup] notation:65 " -[" F:0 "] " f:66 =>
--   subst f addInv F

def addInv (F : FormalGroup R) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  subst f (addInv_X F)


/-- Given any formal group law `F`, `X + [F] addInv (X) = 0`. -/
theorem FormalGroup.X_add_addInv_X_eq_zero : X +[F] addInv_X (F) = 0 := by
  simp [add, subst_addInv_eq_zero]

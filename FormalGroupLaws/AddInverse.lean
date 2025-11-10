import FormalGroupLaws.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators

noncomputable section

variable {R : Type*} [CommRing R] [Nontrivial R] (f g : PowerSeries R) (F : FormalGroup R) {σ : Type*}
  (φ : MvPowerSeries (Fin 2) R) (n : ℕ)


open PowerSeries FormalGroup Finset


abbrev FormalGroup.addInv_aux (F : FormalGroup R): ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1 : ℕ) (MvPowerSeries.subst
    ![X, (∑ i : Fin (n + 1), C (addInv_aux F i.1) * X ^ i.1)] F.toFun))

abbrev FormalGroup.addInv_aux' (F : FormalGroup R): ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1 : ℕ) (MvPowerSeries.subst
    ![(∑ i : Fin (n + 1), C (addInv_aux' F i.1) * X ^ i.1), X] F.toFun))

/-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `ι`,
  such that `F(X, ι(X)) = 0`. -/
def FormalGroup.addInv_X := PowerSeries.mk (fun n => (FormalGroup.addInv_aux F n))

/-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `ι`,
  such that `F(ι(X), X) = 0`. -/
def FormalGroup.addInv_X_left := PowerSeries.mk (fun n => (FormalGroup.addInv_aux' F n))

lemma Finset.sum_fin_eq_sum_range' {β : Type*} [AddCommMonoid β] {n : ℕ}  (f : ℕ → β):
  ∑ i : Fin n, f i.1 = ∑ i ∈ range n, f i := by
  rw [sum_fin_eq_sum_range, sum_congr rfl]
  intro i hi
  simp at hi
  rw [dif_pos hi]

omit [Nontrivial R] in
lemma HasSubst.addInv_aux : MvPowerSeries.HasSubst ![X, (addInv_X F)] := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro x; fin_cases x
  · simp
  · simp [addInv_X]; rfl


omit [Nontrivial R] in
lemma HasSubst.addInv_aux' : MvPowerSeries.HasSubst ![(addInv_X_left F), X] := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro x; fin_cases x
  · simp [addInv_X_left]; rfl
  · simp


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

-- omit [Nontrivial R] in
-- lemma HasSubst.has_subst_map₂ (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
--   MvPowerSeries.HasSubst (subst_map₂ f g) := by
--   refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--   intro s; fin_cases s <;> simp [hf, hg]


omit [Nontrivial R] in
lemma coeff_subst_map₂_eq_subst_subst_map₂_trunc (hf : constantCoeff f = 0)
  (hg : constantCoeff g = 0) :
  coeff n (MvPowerSeries.subst ![f, g] φ) =
  coeff n (MvPowerSeries.subst ![(trunc (n + 1) f), (trunc (n + 1) g)] φ) := by
  rw [coeff, MvPowerSeries.coeff_subst (HasSubst.FinPairing  hf hg),
    MvPowerSeries.coeff_subst (HasSubst.FinPairing  (by simp [coeff_trunc, hf])
    (by simp [coeff_trunc, hg]))]
  simp; apply finsum_congr
  intro d
  congr! 1
  rw [coeff_mul, coeff_mul, sum_congr rfl]
  intro x hx
  simp at hx
  congr! 1
  · rw [coeff_pow, coeff_pow, sum_congr rfl]
    simp
    intro l hl₁ hl₂
    rw [prod_congr rfl]
    intro s hs
    have aux : l s < n + 1 := by
      calc
        _ ≤ (range (d 0)).sum ⇑l := by
          exact Finset.single_le_sum_of_canonicallyOrdered hs
        _ < n + 1 := by
          linarith
    rw [coeff_trunc, if_pos aux]
  · rw [coeff_pow, coeff_pow, sum_congr rfl]
    simp
    intro l hl₁ hl₂
    rw [prod_congr rfl]
    intro s hs
    have aux : l s < n + 1 := by
      calc
        _ ≤ (range (d 1)).sum ⇑l := by
          exact Finset.single_le_sum_of_canonicallyOrdered hs
        _ < n + 1 := by
          linarith
    rw [coeff_trunc, if_pos aux]




omit [Nontrivial R] in
lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
  coeff n (MvPowerSeries.subst ![X, (addInv_X F)] F.toFun) =
  coeff n (MvPowerSeries.subst ![X, (trunc (n + 1) (addInv_X F))] F.toFun) := by
  have trunc_X_aux : trunc (n + 1) X = Polynomial.X (R := R):= by
    refine trunc_X_of ?_
    omega
  have constant_aux : constantCoeff (addInv_X F) = 0 := by
    simp [addInv_X]
    rfl
  rw [coeff_subst_map₂_eq_subst_subst_map₂_trunc _ _ _ _ constantCoeff_X constant_aux]
  simp [ trunc_X_aux]

omit [Nontrivial R] in
lemma coeff_subst_addInv_left_trunc (hn : n ≠ 0) :
  coeff n (MvPowerSeries.subst ![(addInv_X_left F), X] F.toFun) =
  coeff n (MvPowerSeries.subst ![(trunc (n + 1) (addInv_X_left F)), X] F.toFun) := by
  have trunc_X_aux : trunc (n + 1) X = Polynomial.X (R := R):= by
    refine trunc_X_of ?_
    omega
  have constant_aux : constantCoeff (addInv_X_left F) = 0 := by
    simp [addInv_X_left]
    rfl
  rw [coeff_subst_map₂_eq_subst_subst_map₂_trunc _ _ _ _ constant_aux constantCoeff_X]
  simp [ trunc_X_aux]


-- lemma FormalGroup.coeff_X₀_pow {k : ℕ} (hk : k ≥ 2) :
--   MvPowerSeries.coeff (Finsupp.single 0 k) F.toFun = 0 := by
--   sorry



-- lemma FormalGroup.coeff_X₁_pow {k : ℕ} (hk : k ≥ 2) :
--   MvPowerSeries.coeff (Finsupp.single 1 k) F.toFun = 0 := by
--   sorry



lemma coeff_n_aux (n : ℕ):
  coeff n (MvPowerSeries.subst ![X, (∑ i : Fin (n + 1),
  C (addInv_aux F i.1) * X ^ i.1)] F.toFun) = 0 := by
  rw [sum_fin_eq_sum_range' (fun i => (C (addInv_aux F i) * X ^ i))]
  induction n with
  | zero =>
    simp
    rw [constantCoeff, MvPowerSeries.constantCoeff_subst, show (addInv_aux F 0) = 0 by rfl]
    simp
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
      all_goals simp [show (addInv_aux F 0) = 0 by rfl]
  | succ k ih =>
    by_cases hk₀ : k = 0
    · simp [hk₀, show range 2 = {0, 1} by rfl]
      rw [coeff, MvPowerSeries.coeff_subst]
      unfold addInv_aux
      simp
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
        · rw [addInv_aux]; simp
        · unfold addInv_aux
          simp
    have has_subst₁ (m : ℕ) : MvPowerSeries.HasSubst ![X, (∑ i ∈ range (m + 1),
      C (addInv_aux F i) * X ^ i)] := by
      refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      intro x; fin_cases x
      · simp
      · simp
        refine sum_eq_zero ?_
        intro i hi
        by_cases hi₀ : i ≠ 0
        · simp [zero_pow hi₀]
        · simp_all
          rfl
    rw [coeff, MvPowerSeries.coeff_subst (has_subst₁ (k + 1))]
    simp_rw [PowerSeries.coeff_coe]
    simp
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
      simp [hB] at h
      exact h (Finsupp.single () (k + 1))
    · have aux : (Function.support fun d ↦
        (MvPowerSeries.coeff d) F.toFun * if d = Finsupp.single 1 1 then addInv_aux F (k + 1) else 0)
        ⊆ {Finsupp.single 1 1} := by
        refine Function.support_subset_iff'.mpr ?_
        intro d hd
        simp at hd
        simp [if_neg hd]
      exact Set.Finite.subset (Set.finite_singleton (Finsupp.single 1 1)) aux

/-- this is use to construct the left inverse of `X` under the sense of formal group. -/
lemma coeff_n_aux' (n : ℕ):
  coeff n (MvPowerSeries.subst ![(∑ i : Fin (n + 1),
  C (addInv_aux' F i.1) * X ^ i.1), X] F.toFun) = 0 := by
  rw [sum_fin_eq_sum_range' (fun i => (C (addInv_aux' F i) * X ^ i))]
  induction n with
  | zero =>
    simp
    rw [constantCoeff, MvPowerSeries.constantCoeff_subst, show (addInv_aux' F 0) = 0 by rfl]
    simp
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
      all_goals simp [show (addInv_aux' F 0) = 0 by rfl]
  | succ k ih =>
    by_cases hk₀ : k = 0
    · simp [hk₀, show range 2 = {0, 1} by rfl]
      rw [coeff, MvPowerSeries.coeff_subst]
      unfold addInv_aux'
      simp
      have supp_eq : (Function.support (fun d => (MvPowerSeries.coeff d) F.toFun
        * (coeff 1) ((-X) ^ d 0 * X ^ d 1))) = {Finsupp.single (0 : Fin 2) 1,
        Finsupp.single (1 : Fin 2) 1} := by
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
        by_cases hx₀ : x 1 = 0
        · by_cases hx₁ : x 0 = 0
          · have x_zero : x = 0 := by
              ext i; fin_cases i <;> simp [hx₀, hx₁]
            simp [x_zero, F.zero_constantCoeff]
          have xge₁ : x 0 ≥ 2 := by
            by_contra hc
            have xeq : x 0 = 1 := by omega
            have xeq' : x = Finsupp.single 0 1 := by
              ext i; fin_cases i <;> simp [hx₀, xeq]
            contradiction
          simp [hx₀, neg_pow X _]
          rw [coeff_mul_X_pow', if_neg (by linarith)]
          simp
        rw [coeff_mul_X_pow']
        by_cases hx₁ : x 1 = 1
        · rw [if_pos (by linarith)]
          by_cases hx₂ : x 0 = 0
          · have xeq : x = Finsupp.single 1 1 := by
              ext i; fin_cases i <;> simp [hx₂, hx₁]
            contradiction
          simp [hx₁, zero_pow hx₂]
        have xgt : ¬ x 1 ≤ 1 := by omega
        simp [if_neg xgt]
      have supp_fin : (Function.support (fun d => (MvPowerSeries.coeff d) F.toFun
        * (coeff 1) ((-X) ^ d 0 * (X) ^ d 1))).Finite := by
        simp [supp_eq]
      rw [finsum_eq_sum _ supp_fin]
      simp_all
      rw [sum_pair (Finsupp.ne_iff.mpr (by use 0; simp))]
      simp [F.lin_coeff_X, F.lin_coeff_Y]
      · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
        intro s; fin_cases s
        · simp; rfl
        · simp
    have has_subst₁ (m : ℕ) : MvPowerSeries.HasSubst ![(∑ i ∈ range (m + 1),
      C (addInv_aux' F i) * X ^ i), X] := by
      refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      intro x; fin_cases x
      · simp
        refine sum_eq_zero ?_
        intro i hi
        by_cases hi₀ : i ≠ 0
        · simp [zero_pow hi₀]
        · simp at hi₀
          simp [hi₀]
          rfl
      · simp
    rw [coeff, MvPowerSeries.coeff_subst (has_subst₁ (k + 1))]
    simp_rw [PowerSeries.coeff_coe]
    simp
    generalize hB : ∑ i ∈ range (k + 1), C (addInv_aux' F i) * X ^ i = B
    simp [sum_range_add, hB]
    have constantCoeff_of_B : constantCoeff B = 0 := by
      rw [←hB, map_sum]
      apply sum_eq_zero
      intro x hx
      rw [←smul_eq_C_mul, constantCoeff_smul, map_pow, constantCoeff_X, smul_eq_mul]
      by_cases hx' : x = 0
      · simp [hx', show addInv_aux' F 0 = 0 by rfl]
      · simp [zero_pow hx']
    obtain has_subst' := has_subst₁ k
    rw [hB] at has_subst'
    have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) ( (B + C (addInv_aux' F (k + 1))
      * X ^ (k + 1)) ^ d 0 * X ^ d 1) = (coeff (k + 1)) (B ^ d 0 * X ^ d 1)
      + if d = Finsupp.single 0 1 then (addInv_aux' F (k + 1)) else 0 := by
      split_ifs with hd
      · simp [hd, ←hB, coeff_X_pow]
      rw [coeff_mul_X_pow', coeff_mul_X_pow']
      split_ifs with hd₁
      · by_cases hd₂ : d 1 = 0
        · simp [hd₂]
          rw [add_pow, map_sum, sum_eq_single (d 0)]
          simp
          · intro i hi₀ hi₁
            simp at hi₀
            rw [mul_pow, ←pow_mul, ←map_pow]
            calc
              _ = (coeff (k + 1)) (B ^ i * (C ((addInv_aux' F (k + 1)) ^ (d 0 - i)) * X ^ ((k + 1)
                * (d 0 - i))) * (C ((d 0).choose i : R))) := by
                rfl
              _ = (coeff (k + 1)) (C ((addInv_aux' F (k + 1)) ^ (d 0 - i))
                * (C ((d 0).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 0 - i))) := by
                ring_nf
              _ = _ := by
                rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow']
                by_cases hi' : i = d 0 - 1
                · have d_minus : d 0 - i = 1 := by omega
                  have ine_zero : i ≠ 0 := by
                    by_contra hc
                    have deq : d = Finsupp.single 0 1 := by
                      ext s; fin_cases s <;> simp [hd₂]; omega
                    contradiction
                  simp [d_minus, constantCoeff_of_B, zero_pow ine_zero]
                have d_minus_ge : d 0 - i ≥ 2 := by
                  omega
                have gt_aux : ¬ (k + 1) * (d 0 - i) ≤ k + 1 := by
                  simp
                  omega
                rw [if_neg gt_aux]
                simp
          simp
        -- have lt_aux : (k + 1 - d 0) < k + 1 := by omega
        rw [add_pow, map_sum, sum_eq_single (d 0)]
        · simp
        · intro i hi₀ hi₁
          simp at hi₀
          rw [mul_pow, ←pow_mul, ←map_pow]
          calc
            _ = (coeff (k + 1 - d 1)) (B ^ i * (C ((addInv_aux' F (k + 1)) ^ (d 0 - i)) * X ^ ((k + 1)
              * (d 0 - i))) * (C ((d 0).choose i : R))) := by
              rfl
            _ = (coeff (k + 1 - d 1)) (C ((addInv_aux' F (k + 1)) ^ (d 0 - i))
              * (C ((d 0).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 0 - i))) := by
              ring_nf
            _ = _ := by
              rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow', if_neg]
              · simp
              · simp
                calc
                  _ < k + 1 := by omega
                  _ ≤ _ := by
                    have le_aux : d 0 - i ≥ 1 := by omega
                    exact Nat.le_mul_of_pos_right (k + 1) le_aux
        · simp
      simp
    simp_rw [eq_aux, mul_add]
    rw [finsum_add_distrib]
    nth_rw 2 [finsum_eq_single _ (Finsupp.single 0 1)]
    rw [if_pos (by simp), F.lin_coeff_X, addInv_aux',
      sum_fin_eq_sum_range' (fun i => (C (addInv_aux' F i) * X ^ i)), hB, coeff, MvPowerSeries.coeff_subst has_subst']
    simp
    · simp [hk₀]
    · intro d hd
      simp [if_neg hd]
    · obtain h := MvPowerSeries.coeff_subst_finite (has_subst₁ k) F.toFun
      simp [hB] at h
      exact h (Finsupp.single () (k + 1))
    · have aux : (Function.support fun d ↦
        (MvPowerSeries.coeff d) F.toFun * if d = Finsupp.single 0 1 then addInv_aux' F (k + 1) else 0)
        ⊆ {Finsupp.single 0 1} := by
        refine Function.support_subset_iff'.mpr ?_
        intro d hd
        simp at hd
        simp [if_neg hd]
      exact Set.Finite.subset (Set.finite_singleton (Finsupp.single 0 1)) aux


/- Given a formal group law `F` over coefficient ring `R`, there exist a power series
  `addInv F`, such that `F(X, (addInv_X F)) = 0`. -/
theorem subst_addInv_eq_zero : MvPowerSeries.subst ![X, (addInv_X F)] F.toFun = 0 := by
  ext n
  by_cases hn : n = 0
  · simp [hn, constantCoeff, MvPowerSeries.constantCoeff_subst (HasSubst.addInv_aux _)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d 0 ≠ 0
    · simp [zero_pow hd₀]
    by_cases hd₁ : d 1 ≠ 0
    · have eq_aux : constantCoeff F.addInv_X = 0 := by
        simp [addInv_X]; rfl
      simp [eq_aux, zero_pow hd₁]
    simp_all
    have d_eq_zero : d = 0 := by
      ext x
      fin_cases x <;> simp [hd₀, hd₁]
    simp [d_eq_zero, F.zero_constantCoeff]
  simp [←(coeff_n_aux F n), coeff_subst_addInv_trunc _ _ hn]
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


/- Given a formal group law `F` over coefficient ring `R`, there exist a power series
  `addInv F`, such that `F(X, (addInv_X F)) = 0`. -/
theorem subst_addInv_eq_zero_left : MvPowerSeries.subst ![(addInv_X_left F), X] F.toFun = 0 := by
  ext n
  by_cases hn : n = 0
  · simp [hn, constantCoeff, MvPowerSeries.constantCoeff_subst (HasSubst.addInv_aux' _)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d 1 ≠ 0
    · simp [zero_pow hd₀]
    by_cases hd₁ : d 0 ≠ 0
    · have eq_aux : constantCoeff F.addInv_X_left = 0 := by
        simp [addInv_X_left]; rfl
      simp [eq_aux, zero_pow hd₁]
    simp_all
    have d_eq_zero : d = 0 := by
      ext x
      fin_cases x <;> simp [hd₀, hd₁]
    simp [d_eq_zero, F.zero_constantCoeff]
  simp
  rw [←(coeff_n_aux' F n), coeff_subst_addInv_left_trunc _ _ hn]
  congr! 3
  unfold trunc
  simp_rw [←Polynomial.coe_C, ←Polynomial.coe_X]
  rw [sum_fin_eq_sum_range' (fun i => (Polynomial.C (addInv_aux' F i) : PowerSeries R)
    * (Polynomial.X).toPowerSeries ^ i), Nat.Ico_zero_eq_range,
    ←Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_finset_sum, ←Polynomial.eval₂_C_X_eq_coe,
    sum_congr rfl]
  intro i hi
  rw [Polynomial.eval₂_C_X_eq_coe]
  simp [X_pow_eq, addInv_X_left]
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


omit [Nontrivial R] in
variable {F} in
lemma constantCoeff_addInvF_X : MvPowerSeries.constantCoeff (addInv F X) = 0 := by
  simp [addInv]
  rw [subst, X, constantCoeff, constantCoeff_subst_zero (by simp) rfl]


omit [Nontrivial R] in
variable {F} in
lemma constantCoeff_addInvF_X₀ : MvPowerSeries.constantCoeff (addInv F X₀) = 0 := by
  simp [addInv]
  rw [PowerSeries.subst, constantCoeff_subst_zero (by simp) rfl]


omit [Nontrivial R] in
variable {F} in
lemma constantCoeff_addInvF_X₁ : MvPowerSeries.constantCoeff (addInv F X₁) = 0 := by
  simp [addInv]
  rw [PowerSeries.subst, constantCoeff_subst_zero (by simp) rfl]


/- Let `addInv_X` be the right inverse of `X` w.r.t. formal group `F`,
  `addInv_X_left` be the left inverse of `X` w.r.t. formal group `F`, then
  this two power series is the same.-/
lemma left_addInv_eq_right_addInv : addInv_X_left F = addInv_X F := by
  calc
    _ = addInv_X_left F +[F] 0 := Eq.symm <| zero_add_eq_self' rfl
    _ = (addInv_X_left F +[F] X) +[F] addInv_X F := by
      rw [←X_add_addInv_X_eq_zero (F := F), FormalGroup.add_assoc rfl (constantCoeff_X) rfl]
    _ = _ := by
      simp [subst_addInv_eq_zero_left]
      rw [zero_add_eq_self rfl]


/-- For any MvPowerSeries `f` with zero constant coefficient, then
  `f +[F] addInv F f = 0`. -/
lemma add_addInv_eq_zero {f : MvPowerSeries σ R} (h : MvPowerSeries.constantCoeff f = 0) :
  f +[F] addInv F f = 0 := calc
  _ = subst f (MvPowerSeries.subst ![ PowerSeries.X, addInv_X F] F.toFun) := by
    rw [subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.addInv_aux F)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s ↦ h)]
    apply subst_congr
    funext s; fin_cases s
    · simp; rw [← subst, subst_X
      <| HasSubst.of_constantCoeff_zero h]
    · simp; rfl
  _ = _ := by
    rw [subst_addInv_eq_zero]; ext n
    simp [coeff_subst <| HasSubst.of_constantCoeff_zero h]

/-- For any MvPowerSeries `f` with zero constant coefficient, then
  `addInv F f +[F] f = 0`. -/
lemma add_addInv_eq_zero' {f : MvPowerSeries σ R} (h : MvPowerSeries.constantCoeff f = 0):
  addInv F f +[F] f = 0 := calc
  _ = PowerSeries.subst f (MvPowerSeries.subst ![(addInv_X_left F), PowerSeries.X] F.toFun) := by
    rw [subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.addInv_aux' F)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s ↦ h)]
    apply subst_congr
    funext s; fin_cases s
    · simp [left_addInv_eq_right_addInv]; rfl
    · simp; rw [← subst, subst_X
      <| HasSubst.of_constantCoeff_zero h]
  _ = _ := by
    rw [subst_addInv_eq_zero_left]; ext n
    simp [coeff_subst <| HasSubst.of_constantCoeff_zero h]


open MvPowerSeries in
/-- For any MvPowerSeries `f` with zero constant coefficient, then there exist unique
  MvPowerSeries `g`, such that `f +[F] g = 0 ∧ constantCoeff g = 0`-/
lemma uniqueness_of_addInv {f : MvPowerSeries σ R} (h : constantCoeff f = 0) :
  ∃! (g : MvPowerSeries σ R), f +[F] g = 0 ∧ constantCoeff g = 0 := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · use addInv F f
    constructor
    · exact add_addInv_eq_zero F h
    · rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [h]) rfl]
  · intro y z ⟨hy₁, hy₂⟩ ⟨hz₁, hz₂⟩
    have coeff_aux : MvPowerSeries.constantCoeff (addInv F f) = 0 := by
      rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [h]) rfl]
    calc
      _ = addInv F f := by
        rw [←zero_add_eq_self hy₂ (F := F), ←add_addInv_eq_zero' F h, FormalGroup.add_assoc
          coeff_aux h hy₂, hy₁, zero_add_eq_self' coeff_aux]
      _ = _ := by
        rw [←zero_add_eq_self hz₂ (F := F), ←add_addInv_eq_zero' F h, FormalGroup.add_assoc
          coeff_aux h hz₂, hz₁, zero_add_eq_self' coeff_aux]


open MvPowerSeries in
/-- For any two MvPowerSeries `f, g` with constant coefficient are zero, then
  `addInv F (f +[F] g) = addInv F g +[F] addInv F f`. -/
lemma addInv_of_add_eq {f g : MvPowerSeries σ R} (hf : constantCoeff f = 0)
  (hg : constantCoeff g = 0) : addInv F (f +[F] g) = addInv F g +[F] addInv F f := by
  have coeff_aux₀ : constantCoeff (f +[F] g) = 0 :=
    constantCoeff_subst_zero (by simp [hf, hg]) F.zero_constantCoeff
  have coeff_aux₁ : constantCoeff (addInv F (f +[F] g)) = 0 := by
    rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [coeff_aux₀]) rfl]
  have coeff_aux_f : constantCoeff (addInv F f) = 0 := by
    rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [hf]) rfl]
  have coeff_aux_g : constantCoeff (addInv F g) = 0 := by
    rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [hg]) rfl]
  have coeff_aux₃ : constantCoeff (addInv F (f +[F] g) +[F] f) = 0 := by
    rw [constantCoeff_subst_zero (by simp [coeff_aux₁, hf]) F.zero_constantCoeff]
  obtain eq_aux := add_addInv_eq_zero' F coeff_aux₀
  have eq_aux₁ : addInv F (f +[F] g) +[F] f = addInv F g := by
    rw [←zero_add_eq_self' (F := F) coeff_aux₃, ←add_addInv_eq_zero F hg,
      ←FormalGroup.add_assoc coeff_aux₃ hg coeff_aux_g, FormalGroup.add_assoc (Z₁ := f) coeff_aux₁ hf hg,
      eq_aux, zero_add_eq_self coeff_aux_g]
  rw [←zero_add_eq_self' (F := F) coeff_aux₁, ←add_addInv_eq_zero F hf,
    ←FormalGroup.add_assoc coeff_aux₁ hf coeff_aux_f,
    eq_aux₁]

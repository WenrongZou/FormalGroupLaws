import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution


namespace PowerSeries

open PowerSeries Finset

variable {R : Type*} [CommRing R] (n : ℕ)


noncomputable def truncFun (f : PowerSeries R) : Polynomial R :=
  ∑ m ∈ Finset.Iio n, Polynomial.monomial m (coeff m f)


theorem coeff_truncFun (m : ℕ) (f : PowerSeries R) :
    (truncFun n f).coeff m = if m < n then coeff m f else 0 := by
  classical
  unfold truncFun
  by_cases hm : m < n
  simp [hm]
  have sum_single : ∑ b ∈ Finset.Iio n, ((Polynomial.monomial b)
    ((coeff b) f)).coeff m = ((Polynomial.monomial m) ((coeff m) f)).coeff m := by
    apply Finset.sum_eq_single_of_mem
    simp [hm]
    intro b hb hb'
    exact (Polynomial.coeff_monomial_of_ne _ (Ne.symm hb'))
  rw [sum_single]
  simp
  simp [hm]
  refine (Finset.sum_eq_zero ?_)
  intro b hb
  simp at hm
  simp at hb
  apply Polynomial.coeff_monomial_of_ne
  linarith

noncomputable def truncFun' (f : PowerSeries R) : Polynomial R :=
  ∑ m ∈ Finset.Iic n, Polynomial.monomial m (PowerSeries.coeff m f)

theorem coeff_truncFun' (m : ℕ) (f : PowerSeries R) :
    (truncFun' n f).coeff m = if m ≤ n then coeff m f else 0 := by
  classical
  unfold truncFun'
  by_cases hm : m ≤ n
  simp [hm]
  have sum_single : ∑ b ∈ Finset.Iic n, ((Polynomial.monomial b)
    ((coeff b) f)).coeff m = ((Polynomial.monomial m) ((coeff m) f)).coeff m := by
    apply Finset.sum_eq_single_of_mem
    simp [hm]
    intro b hb hb'
    exact (Polynomial.coeff_monomial_of_ne _ (Ne.symm hb'))
  rw [sum_single]
  simp
  simp [hm]
  refine (Finset.sum_eq_zero ?_)
  intro b hb
  simp at hm
  simp at hb
  apply Polynomial.coeff_monomial_of_ne
  linarith


-- noncomputable def trunc : PowerSeries A →+ Polynomial A where
--   toFun := truncFun n
--   map_zero' := by
--     classical
--     ext x
--     simp [coeff_truncFun]
--   map_add' := by
--     classical
--     intros x y
--     ext m
--     simp only [coeff_truncFun, Polynomial.coeff_add, ite_add_ite, ← map_add, add_zero]

noncomputable def trunc' : PowerSeries R →+ Polynomial R where
  toFun := truncFun' n
  map_zero' := by
    classical
    ext x
    simp [coeff_truncFun']
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun', Polynomial.coeff_add, ite_add_ite, ← map_add, add_zero]

-- theorem coeff_trunc m (φ : PowerSeries A) :
--     (trunc n φ).coeff m = if m < n then coeff A m φ else 0 := by
--   classical simp [trunc, coeff_truncFun]



theorem eq_of_forall_trunc_eq (f g: PowerSeries R)
  (h : ∀ (n : ℕ), trunc n f = trunc n g) : f = g := by
  ext n
  obtain hn := h (n + 1)
  have eq_aux : trunc (n + 1) f = trunc (n + 1) g := by
    unfold trunc at hn
    exact hn
  calc
    _ = (trunc (n + 1) f).coeff n := by
      simp [coeff_trunc]
    _ = (trunc (n + 1) g).coeff n := by
      rw [eq_aux]
    _ = _ := by
      simp [coeff_trunc]

theorem eq_of_forall_trunc'_eq (f g: PowerSeries R)
  (h : ∀ (n : ℕ), trunc' n f = trunc' n g) : f = g := by
  ext n
  obtain hn := h n
  have eq_aux : truncFun' n f = truncFun' n g := by
    unfold trunc' at hn
    simp at hn
    exact hn
  calc
    _ = (truncFun' n f).coeff n := by
      simp [coeff_truncFun']
    _ = (truncFun' n g).coeff n := by
      rw [eq_aux]
    _ = _ := by
      simp [coeff_truncFun']



theorem trunc_of_subst (f g: PowerSeries R)(hg : constantCoeff g = 0)
  : trunc n (subst g f) = trunc n (subst (trunc n g) f) := by
  ext m
  by_cases hm : m < n
  -- first cast m < n
  · have subst_aux : HasSubst g := HasSubst.of_constantCoeff_zero hg
    have subst_aux' : HasSubst ((trunc n g) : PowerSeries R):= by
      apply HasSubst.of_constantCoeff_zero
      rw [←MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      have aux : Polynomial.coeff (truncFun n g) 0 = 0 := by
        rw [coeff_truncFun]
        simp [show n > 0 by linarith, hg]
      exact aux
    simp [coeff_trunc]
    simp [if_pos hm, coeff_subst' subst_aux, coeff_subst' subst_aux']
    congr
    funext d
    -- prove that (coeff R m) (g ^ d) = (coeff R m) (↑(trunc n g) ^ d)
    rw [coeff_pow, coeff_pow, sum_congr rfl]
    · intro l hl
      rw [prod_congr rfl]
      -- prove that : `∀ x ∈ range d, (coeff R (l x)) g = (coeff R (l x)) ↑(trunc n g)`
      intro i hi
      have le_aux : l i ≤ m := by
        simp at hl
        obtain ⟨h1, h2⟩ := hl
        have : ∀ j, (j ∈ (Finset.range d)) → l j ≥ 0 := by
          intro j hj
          norm_num
        by_contra hc
        simp at hc
        by_cases hi : i ∈ Finset.range d
        rw [←Finset.sum_erase_add _ _ hi] at h1
        have ge_aux : ∑ x ∈ (Finset.range d).erase i, l x ≥ 0 := by
          apply Finset.sum_nonneg
          intro j hj
          simp at hj
          exact this j (by simp [hj.2])
        have ge_aux2 : m ≥ l i := by
          simp only [← h1, ge_iff_le, le_add_iff_nonneg_left, zero_le]
        linarith
        simp at hi
        have li_eq_zero : l i = 0 := by
          by_contra hi'
          have supp_l : i ∈ l.support := by
            simp [hi']
          have aux : i ∈ Finset.range d := by
            exact h2 supp_l
          simp at aux
          linarith
        rw [li_eq_zero] at hc
        linarith
      have le_aux' : l i < n := by
        linarith
      rw [Polynomial.coeff_coe, coeff_trunc _ _ g, if_pos le_aux']
  -- second case that ¬ m < n
  · simp [coeff_trunc]
    rw [if_neg hm, if_neg hm]

lemma trunc'_eq_trunc_succ (f : PowerSeries R) :
  trunc' n f = trunc (n + 1) f := by
  unfold trunc' truncFun' trunc
  simp
  have aux : Iic n = range (n + 1) := by
    refine Finset.ext_iff.mpr ?_
    simp
    omega
  rw [aux]



theorem trunc'_of_subst (f g: PowerSeries R)
  (hg : PowerSeries.constantCoeff g = 0)
  : trunc' n (subst g f) = trunc' n (subst (trunc' n g) f) := by
  rw [trunc'_eq_trunc_succ, trunc'_eq_trunc_succ, trunc'_eq_trunc_succ, trunc_of_subst _ _ _ hg]

theorem trunc'_of_succ (f: PowerSeries R) (n : ℕ) :
  trunc' (n + 1) f = trunc' n f + Polynomial.monomial (n + 1) (coeff (n + 1) f) := by
  unfold trunc'
  simp
  unfold truncFun'
  have finset_aux : Iic (n + 1) = insert (n + 1) (Iic (n)) := by
    refine (erase_eq_iff_eq_insert ?_ ?_).mp ?_
    all_goals simp
    exact rfl
  rw [finset_aux]
  simp [sum_insert]
  conv =>
    lhs
    rw [add_comm]

lemma trunc'_of_succ_mk (f : ℕ → R) (n : ℕ) :
  trunc' (n + 1) (mk f) = trunc'
  n (mk f) + (Polynomial.C (f (n + 1))) * (Polynomial.X) ^ (n + 1) := by
  unfold trunc' truncFun'
  have finset_aux : Finset.Iic (n + 1) = insert (n + 1) (Finset.Iic (n)) := by
    refine (Finset.erase_eq_iff_eq_insert ?_ ?_).mp ?_
    all_goals simp
    exact rfl
  simp [finset_aux, sum_insert, Polynomial.C_mul_X_pow_eq_monomial, add_comm]

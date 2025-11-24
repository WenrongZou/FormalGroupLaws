import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution
import FormalGroupLaws.Trunc

namespace PowerSeries

noncomputable section

open PowerSeries Finset

variable {R : Type*} [CommRing R] (f : PowerSeries R) (h : IsUnit (coeff 1 f)) (hc : constantCoeff f = 0)


theorem subst_comp_eq_id_iff {g : PowerSeries R} (hf : HasSubst f)
  (hg : HasSubst g) : subst f ∘ subst g = id ↔
  subst f g = X := by
  constructor
  · intro h
    rw [subst_comp_subst hg hf] at h
    rw [←subst_X hg (R := R), subst_comp_subst_apply hg hf, h]
    simp
  · intro h
    rw [subst_comp_subst hg hf, h]
    funext x
    simp [←map_algebraMap_eq_subst_X]

-- Define the inverse function by induction.
def invFun_aux
  (h : IsUnit (coeff 1 f)) (hc : constantCoeff f = 0):
  -- b₁ := a₁⁻¹
  ℕ → R × (PowerSeries R)
  | 0 => (0, 0)
  | 1 => ( (h.unit⁻¹ : Units R), C ((h.unit⁻¹ : Units R) : R) * X (R := R))
  | n + 1 =>  (- (h.unit⁻¹) * coeff (n + 1) (subst ((invFun_aux  h hc n).2) f),
  (invFun_aux h hc n).2 + C (- (h.unit⁻¹) *
  coeff (n + 1) (subst ((invFun_aux h hc n).2) f)) * (X) ^ (n + 1))


lemma coeff_invFun_zero : invFun_aux f h hc 0 = (0, 0) := by
  rfl

lemma coeff_invFun_one : invFun_aux f h hc 1 =
  (((h.unit⁻¹ : Units R) : R), C ((h.unit⁻¹ : Units R) : R) * X (R := R))
  := by
  rfl

lemma coeff_invFun {n : ℕ } (hn : n ≠ 0): invFun_aux f h hc (n + 1) =
  (- (h.unit⁻¹) * coeff (n + 1) (subst ((invFun_aux f h hc n).2) f),
  (invFun_aux f h hc n).2 + C (- (h.unit⁻¹) *
  coeff (n + 1) (subst ((invFun_aux f h hc n).2) f)) * (X) ^ (n + 1))
  := by
  conv =>
    lhs
    unfold invFun_aux
  simp


theorem trunc'_of_invFun_aux {n : ℕ} :
  let g : PowerSeries R := mk (fun n => (invFun_aux f h hc n).1)
  trunc' n g = ((invFun_aux f h hc n).2) := by
  induction n with
| zero =>
  simp [coeff_invFun_zero, trunc']
  ext d
  simp [coeff_truncFun']
  intro hd
  rw [hd, coeff_invFun_zero]
| succ k ih =>
  by_cases hk : k = 0
  -- the case k = 0
  · rw [hk]
    simp
    rw [coeff_invFun_one]
    simp [trunc']
    ext d
    simp [coeff_truncFun']
    by_cases hd : d = 0
    simp [hd, coeff_invFun_zero]
    by_cases hd1 : d = 1
    simp [hd1, coeff_invFun_one]
    have hd2 : ¬ d ≤ 1 := by
      omega
    simp [hd2, coeff_X, if_neg hd1]
  -- the case for k ≠ 0
  · rw [coeff_invFun f h hc hk]
    simp
    rw [trunc'_of_succ_mk]
    nth_rw 1 [← ih]
    norm_num
    rw [coeff_invFun f h hc hk]
    simp


-- the constant coefficient of the n-th invFun equal zero, namely `(constantCoeff A) (invFun_aux f h hc k).2 = 0`
lemma constCoeff_invFunAux_eq_zero {n : ℕ} :
  constantCoeff (invFun_aux f h hc n).2 = 0 := by
  rw [←trunc'_of_invFun_aux]
  induction n with
  | zero =>
    simp [trunc', truncFun', show Finset.Iic 0 = {0} by rfl, coeff_invFun_zero]
  | succ k ih =>
    simp [trunc'_of_succ_mk, ih]

-- this lemma only use once, could remove maybe
lemma HasSubst_aux₀ : HasSubst (C (↑h.unit⁻¹ : R) * X) := by
  refine HasSubst.of_constantCoeff_zero ?_
  simp [X]

lemma coeff_of_subst_of_add_pow (g h: PowerSeries R) (n : ℕ)
  (hn₀ : n ≠ 0) (a : R) (hg : constantCoeff g = 0):
  coeff n (subst (g + C a * X ^ n) h)
    = coeff n (subst g h) + (coeff 1) h * a := by
  -- prove two power series has substitution.
  have HasSubst_aux₁ : HasSubst g := HasSubst.of_constantCoeff_zero hg
  have HasSubst_aux₂ : HasSubst (g + C a * X ^ n) := by
    refine HasSubst.of_constantCoeff_zero ?_
    simpa [X, constantCoeff_X, zero_pow hn₀, hg]
  rw [coeff_subst' HasSubst_aux₁, coeff_subst' HasSubst_aux₂]
  have aux : ∑ᶠ (d : ℕ), (coeff d) h • (coeff n) ((g + C a * X ^ n) ^ d) -
  ∑ᶠ (d : ℕ), (coeff d) h • (coeff n) (g ^ d) = (coeff 1) h * a := by
    rw [←finsum_sub_distrib, finsum_eq_single _ 1]
    simp; ring
    intro m hm
    have eq_aux : (coeff n) ((g + C a * X ^ n) ^ m) =
      (coeff n) (g ^ m) := by
      by_cases hm₀ : m = 0
      rw [hm₀]
      simp
      have hm₂ : m ≥ 2 := by omega
      rw [coeff_pow, coeff_pow]
      have coeff_aux : ∀ l ∈ (range m).finsuppAntidiag n,
        ∏ i ∈ range m, (coeff (l i)) (g + C a
        * X ^ n) =  ∏ i ∈ range m, (coeff (l i)) g := by
        intro l hl
        by_cases hi : ∃ i₀ ∈ range m, l i₀ = n
        obtain ⟨i₀, hi₀, hi₁⟩ := hi
        have ljzero : ∃ j ∈ (range m), l j = 0 := by
          by_contra hc
          simp at hc
          have geone : ∀ x < m, l x ≥ 1 := by
            intro x hx
            obtain hc' := hc x hx
            omega
          simp at hl
          obtain ⟨hl₁, hl₂⟩ := hl
          have set_eq : (range m) = insert i₀ ((range m).erase i₀) := by
            exact Eq.symm (insert_erase hi₀)
          rw [set_eq, sum_insert, hi₁] at hl₁
          have sum_ge_one : ∑ x ∈ (range m).erase i₀, l x ≥ 1 := by
            calc
              _ ≥ ∑ x ∈ (range m).erase i₀, 1 := by
                refine sum_le_sum ?_
                intro i hi
                simp at hi
                obtain ⟨hineq, hile⟩ := hi
                exact geone i hile
              _ = m - 1 := by
                simp
                have meq : m = (range m).card := by simp
                nth_rw 2 [meq]
                exact card_erase_of_mem hi₀
              _ ≥ 1 := by omega
          linarith
          simp
        obtain ⟨j, hj₀, hj⟩ := ljzero
        have zero_aux₁ : (coeff (l j)) (g + C a * X ^ n) = 0 := by
          rw [hj]
          simp [hg, zero_pow hn₀]
        have zero_aux₂ : (coeff (l j)) (g) = 0 := by
          rw [hj]
          simp [hg]
        rw [prod_eq_zero hj₀ zero_aux₁, prod_eq_zero hj₀ zero_aux₂]
        have hi' : ∀ i ∈ (range m), l i < n := by
          simp at hi
          have hile : ∀ i < m, l i ≤ n := by
            by_contra hc
            simp at hc
            obtain ⟨x, xle, hx⟩ := hc
            simp at hl
            obtain ⟨hl₁, hl₂⟩ := hl
            have lt_aux : (range m).sum ⇑l > n := by
              calc
                _ ≥ l x := by
                  refine single_le_sum ?_ ?_
                  intro i hi_in
                  linarith
                  simp [xle]
                _ > n := hx
            linarith
          intro i hi_in
          simp at hi_in
          exact lt_of_le_of_ne (hile i hi_in) (hi i hi_in)
        apply prod_congr rfl
        simp [map_add]
        intro i hile
        rw [coeff_X_pow, if_neg]
        simp
        linarith [hi' i (by simp [hile])]
      exact sum_congr (by simp) coeff_aux
    rw [eq_aux]; ring
    · refine coeff_subst_finite (HasSubst.of_constantCoeff_zero ?_) h (Finsupp.single () n)
      unfold constantCoeff at hg
      simp [X, hg, zero_pow hn₀]
    · exact coeff_subst_finite (HasSubst.of_constantCoeff_zero
        (by rw [←hg, constantCoeff])) h (Finsupp.single () n)
  rw [← aux]; ring

-- prove that trunc' of subst of invFun into f is equal to trunc' of X.
theorem subst_inv_aux₁ {n : ℕ} :
  (trunc' n) (subst (invFun_aux f h hc n).2 f) = (trunc' n) X := by
  induction n with
  | zero =>
    rw [coeff_invFun_zero]
    have HasSubst_aux : HasSubst (0 : PowerSeries R) := by
      simp [HasSubst.of_constantCoeff_zero]
    have subst_zero : (subst (0 : PowerSeries R) f) = 0 := by
      refine ext ?_
      intro n
      simp [coeff_subst' HasSubst_aux]
      apply finsum_eq_zero_of_forall_eq_zero
      intro d
      by_cases hd : d = 0
      · simp [hd, hc]
      · simp [zero_pow hd]
    simp [subst_zero, trunc']
    ext d
    simp [coeff_truncFun']
    intro hd
    rw [hd, coeff_X, if_neg (by simp)]
  | succ k ih =>
    -- prove first for the case k = 0, which the right hand side equals to X.
    by_cases hk : k = 0
    · simp [hk, coeff_invFun_one, trunc']
      ext d
      simp [coeff_truncFun']
      by_cases hd0 : d = 0
      · rw [if_pos (by linarith), if_pos (by linarith), coeff_subst' (HasSubst_aux₀ f h)]
        simp [hd0]
        apply finsum_eq_zero_of_forall_eq_zero
        intro x
        by_cases hx : x = 0
        · simp [hx, hc]
        · simp [zero_pow hx]
      by_cases hd1 : d = 1
      simp [hd1]
      rw [coeff_subst' (HasSubst_aux₀ f h), finsum_eq_single _ 1]
      simp
      intro m hm
      -- to prove (coeff R m) f • (coeff R 1) (((C R) ↑h.unit⁻¹ * X) ^ m) = 0
      have coeff_zero : (coeff 1) ((C (↑h.unit⁻¹ : R) * X) ^ m) = 0 := by
        rw [mul_pow, ←map_pow, coeff_C_mul_X_pow, if_neg (Ne.symm hm)]
      simp [coeff_zero]
      have dgetwo : ¬ d ≤ 1 := by
        omega
      rw [if_neg dgetwo, if_neg dgetwo]
    simp [invFun_aux]
    have aux : (trunc' k) (-(C (↑h.unit⁻¹ : R) *
      C ((coeff (k + 1)) (subst (invFun_aux f h hc k).2 f)) *
      X ^ (k + 1))) = 0 := by
      simp [trunc']
      ext d
      by_cases hd : d ≤ k
      have eq_aux : (C (↑h.unit⁻¹ : R) *
        C ((coeff (k + 1)) (subst (invFun_aux f h hc k).2 f)) *
        X ^ (k + 1)) = C ((↑h.unit⁻¹ : R) * ((coeff (k + 1)) (subst (invFun_aux f h hc k).2 f)))
        * X ^ (k + 1) := by
        simp
      · simp [coeff_truncFun', eq_aux, coeff_X_pow, if_neg (show d ≠ k + 1 by linarith), mul_zero]
      · simp [PowerSeries.coeff_truncFun', if_neg hd]
    rw [trunc'_of_succ, trunc'_of_subst k _ _ (by simp [constCoeff_invFunAux_eq_zero f h hc]), map_add, aux, add_zero, ←trunc'_of_subst k _ _ (constCoeff_invFunAux_eq_zero f h hc), ih]
    have zero_aux : (Polynomial.monomial (k + 1))
      ((coeff (k + 1)) (subst ((invFun_aux f h hc k).2 + -(C (↑h.unit⁻¹ : R) *
      C ((coeff (k + 1)) (subst (invFun_aux f h hc k).2 f)) *
        X ^ (k + 1))) f)) = 0 := by
      simp
      have eq_aux : -(C (↑h.unit⁻¹ : R) *
        C ((coeff (k + 1)) (subst (invFun_aux f h hc k).2 f)) *
        X ^ (k + 1)) = C (-(↑h.unit⁻¹ : R) *
        ((coeff (k + 1)) (subst (invFun_aux f h hc k).2 f))) * X ^ (k + 1) := by
        simp
      rw [eq_aux, coeff_of_subst_of_add_pow _ _ _ _ _ (constCoeff_invFunAux_eq_zero f h hc)]
      simp [←mul_assoc]
      linarith
    rw [zero_aux, add_zero, trunc'_of_succ, coeff_X, if_neg (show ¬ k + 1 = 1 by omega)]
    simp


def subst_inv : PowerSeries R := mk (fun n => (invFun_aux f h hc n).1)

theorem subst_inv_eq : subst (subst_inv f h hc) f = X := by
  let g : PowerSeries R := mk (fun n => (invFun_aux f h hc n).1)
  have substDomain_g : HasSubst g := by
    apply HasSubst.of_constantCoeff_zero
    have zero_coeff : (constantCoeff) g = 0 := by
      simp [g, invFun_aux]
    unfold constantCoeff at zero_coeff
    simp [zero_coeff]
  rw [show (f.subst_inv h hc) = g by rfl]
  apply eq_of_forall_trunc'_eq
  intro n
  rw [trunc'_of_subst, trunc'_of_invFun_aux, subst_inv_aux₁]
  simp [g, invFun_aux]



theorem subst_inv_aux
  (h : IsUnit (coeff 1 f)) (hc : constantCoeff f = 0)
   : ∃ (g : PowerSeries R), subst g f = X
    ∧ constantCoeff g = 0 ∧ IsUnit (coeff 1 g) := by
  let g : PowerSeries R := mk (fun n => (invFun_aux f h hc n).1)
  use g
  have substDomain_g : HasSubst g := by
    apply HasSubst.of_constantCoeff_zero
    have zero_coeff : (constantCoeff) g = 0 := by
      simp [g, invFun_aux]
    unfold constantCoeff at zero_coeff
    simp [zero_coeff]
  constructor
  · apply eq_of_forall_trunc'_eq
    intro n
    rw [trunc'_of_subst, trunc'_of_invFun_aux, subst_inv_aux₁]
    simp [g, invFun_aux]
  constructor
  · simp [g, invFun_aux]
  simp [g, invFun_aux]

theorem exist_subst_inv_aux {g : PowerSeries R}
  (hg₃ : IsUnit (coeff 1 g)) (hg₂ : constantCoeff g = 0) :
  subst g f = X → subst f g = X := by
  intro hg₁
  obtain ⟨g', hg₁', hg₂', hg₃'⟩ := subst_inv_aux g hg₃ hg₂
  -- use this g to constructor g', then g' = f
  have eq_aux : f = g' := by
    have subst_aux₁ : subst g' (subst g f) = g' := by
      rw [hg₁, PowerSeries.subst_X]
      apply HasSubst.of_constantCoeff_zero
      unfold constantCoeff at hg₂'
      rw [hg₂']
    have subst_aux₂ : subst g' (subst g f) =
      subst (subst g' g) f := by
      rw [←subst_comp_subst]
      simp
      apply HasSubst.of_constantCoeff_zero
      unfold constantCoeff at hg₂
      rw [hg₂]
      apply HasSubst.of_constantCoeff_zero
      unfold constantCoeff at hg₂'
      simp [hg₂']
    rw [←subst_aux₁, subst_aux₂, hg₁']
    simp [←map_algebraMap_eq_subst_X f]
  rw [eq_aux]
  exact hg₁'


/-- For every power series `f ∈ A⟦X⟧` with zero constant coefficient,
  and if `f(X) = u * X + ⋯` where `u ∈ Aˣ`, then there is `g ∈ A ⟦X⟧`,
  such that `f ∘ g = id` and `g ∘ f = id`. -/
theorem exist_subst_inv
  (h : IsUnit (coeff 1 f)) (hc : constantCoeff f = 0):
  ∃ (g : PowerSeries R), (subst f ∘ subst g = id ∧ subst g ∘ subst f = id
  ∧ constantCoeff g = 0) := by
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := subst_inv_aux f h hc
  refine ⟨g, ?_, (subst_comp_eq_id_iff _ (HasSubst.of_constantCoeff_zero hg₂)
    (HasSubst.of_constantCoeff_zero hc)).mpr hg₁, hg₂⟩
  refine (subst_comp_eq_id_iff f ?_ ?_).mpr ?_
  · exact HasSubst.of_constantCoeff_zero' hc
  · exact HasSubst.of_constantCoeff_zero' hg₂
  · exact exist_subst_inv_aux f hg₃ hg₂ hg₁


theorem exist_unique_subst_inv_aux
  (h : IsUnit (coeff 1 f)) (hc : constantCoeff f = 0):
  ∃! (g : PowerSeries R), subst f ∘ subst g = id ∧ subst g ∘ subst f = id
  ∧ constantCoeff g = 0 := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨g, h₁, h₂, h₃⟩ := exist_subst_inv _ h hc
    exact ⟨g, h₁, h₂, h₃⟩
  · intro g₁ g₂ hg₁ hg₂
    obtain ⟨hg₁, hg₁', hg₁''⟩ := hg₁
    have eq_aux : subst g₁ ∘ subst f ∘ subst g₂ = id ∘ subst g₂ (R := R) := by
      rw [←hg₁', Function.comp_assoc]
    rw [hg₂.1] at eq_aux
    simp at eq_aux
    have eq_aux' : subst g₁ PowerSeries.X (R := R) = subst g₂ PowerSeries.X (R := R) := by
      rw [eq_aux]
    rw [subst_X (HasSubst.of_constantCoeff_zero' hg₂.2.2), subst_X
      (HasSubst.of_constantCoeff_zero' hg₁'')] at eq_aux'
    exact eq_aux'

theorem exist_unique_subst_inv_left (h : IsUnit (coeff 1 f)) (hc : constantCoeff f = 0):
  ∃! (g : PowerSeries R), subst f ∘ subst g = id ∧ constantCoeff g = 0 := by
  obtain ⟨g, h₁, h₂⟩ := exist_unique_subst_inv_aux _ h hc
  use g
  simp
  constructor
  · exact ⟨h₁.1, h₁.2.2⟩
  · intro y h_subst h_const
    have aux : subst g ∘ subst f ∘ subst y = subst g (R := R) := by
      simp [h_subst]
    have aux' : subst y = subst g (R := R) := by
      simp [←Function.comp_assoc, h₁.2.1] at aux
      exact aux
    rw [←subst_X (a := y) (R := R) (HasSubst.of_constantCoeff_zero' h_const),
      ←subst_X (a := g) (R := R) (HasSubst.of_constantCoeff_zero' h₁.2.2), aux']


theorem exist_unique_subst_inv_right (h : IsUnit (coeff 1 f)) (hc : constantCoeff f = 0):
  ∃! (g : PowerSeries R), subst g ∘ subst f = id ∧ constantCoeff g = 0 := by
  obtain ⟨g, h₁, h₂⟩ := exist_unique_subst_inv_aux _ h hc
  use g
  simp
  constructor
  · exact ⟨h₁.2.1, h₁.2.2⟩
  · intro y h_subst h_const
    have aux : subst y ∘ subst f ∘ subst g = subst g (R := R) := by
      simp [←Function.comp_assoc, h_subst]
    have aux' : subst y = subst g (R := R) := by
      simp [h₁.1] at aux
      exact aux
    rw [←subst_X (a := y) (R := R) (HasSubst.of_constantCoeff_zero' h_const),
      ←subst_X (a := g) (R := R) (HasSubst.of_constantCoeff_zero' h₁.2.2), aux']


end
end PowerSeries

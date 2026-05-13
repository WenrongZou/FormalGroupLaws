module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Substitution
public import FormalGroupLaws.Basic

@[expose] public section

namespace MvPowerSeries

variable {R S σ τ : Type*} [CommRing R] [CommRing S]

section

variable {n m : ℕ} (p : MvPowerSeries σ R) [Finite σ] {x : σ →₀ ℕ}

open Finset

theorem coeff_truncTotal_eq_ite :
    (truncTotal n p).coeff x = if x.degree < n then p.coeff x else 0 := by
  by_cases h : x.degree < n
  · rw [if_pos h, coeff_truncTotal _ h]
  · rw [if_neg h, coeff_truncTotal_eq_zero _ (not_lt.mp h)]

theorem constantCoeff_truncTotal_eq_ite :
    (truncTotal n p).constantCoeff = if 0 < n then p.constantCoeff else 0 := by
  simp [MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite]

lemma coeff_truncTotal_pow (h : x.degree < n) :
    ((p.truncTotal n ^ m)).coeff x = (p ^ m).coeff x := by
  classical
  induction m using Nat.caseStrongRecOn generalizing x with
  | zero => grind [coeff_one, MvPolynomial.coeff_one]
  | ind k ih =>
    simp_rw [Nat.succ_eq_add_one, pow_add, pow_one, MvPolynomial.coeff_mul, coeff_mul]
    congr! 2 with _ _
    · exact ih _ k.le_refl (by grind [mem_antidiagonal])
    · exact coeff_truncTotal _ (by grind [mem_antidiagonal])

lemma truncTotal_pow_eq_truncTotal_truncTotal_pow :
    (p ^ m).truncTotal n = ((p.truncTotal n).toMvPowerSeries ^ m).truncTotal n := by
  ext d
  by_cases hd : d.degree < n
  · simp_rw [coeff_truncTotal _ hd]
    exact_mod_cast (coeff_truncTotal_pow _ hd).symm
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

theorem truncTotal_zero {f : MvPowerSeries σ R} : f.truncTotal 0 = 0 := by
  ext n
  simp [coeff_truncTotal_eq_ite]

lemma truncTotal_degree_one : p.truncTotal 1 = MvPolynomial.C p.constantCoeff := by
  classical
  ext n
  simp [coeff_truncTotal_eq_ite]
  by_cases! h : n = 0
  · simp [h]
  have : n.degree ≠ 0 := by
    by_contra! hc
    exact h (n.degree_eq_zero_iff.mp hc)
  rw [if_neg this, if_neg h.symm]

theorem truncTotal_eq_sum :
    p.truncTotal n = ∑ i ∈ range n, p.homogeneousComponent i := by
  ext d
  simp [coeff_homogeneousComponent, coeff_truncTotal_eq_ite]

theorem truncTotal_succ_eq : p.truncTotal n.succ =
    p.truncTotal n + p.homogeneousComponent n := by
  rw [truncTotal_eq_sum, sum_range_succ, ← truncTotal_eq_sum]

lemma truncTotal_homogeneous_same : (p.homogeneousComponent n).truncTotal n = 0 := by
  ext d
  simp [coeff_truncTotal_eq_ite, coeff_homogeneousComponent]
  grind


lemma eq_of_forall_truncTotal_eq {f g : MvPowerSeries σ R} :
    f = g ↔ ∀ k, f.truncTotal k = g.truncTotal k := sorry

end

lemma HasSubst.truncTotal {a : σ → MvPowerSeries τ S} {x : σ → ℕ} [Finite τ] (ha : HasSubst a) :
    HasSubst (fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries) where
  const_coeff i := by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, constantCoeff_truncTotal_eq_ite]
    split_ifs <;> simp [ha.const_coeff i]
  coeff_zero d :=
    (ha.coeff_zero d).subset fun i => by contrapose; simp +contextual [coeff_truncTotal_eq_ite]

section truncTotal

open Finset

variable {f : MvPowerSeries σ R} [Finite τ] {x : σ → ℕ} {k : ℕ} {a : σ → MvPowerSeries τ S}
  [Algebra R S]

theorem truncTotal_subst_eq_truncTotal_right_of_le (ha : HasSubst a) (hx : ∀ i, k ≤ x i) :
    (f.subst a).truncTotal k = (f.subst
      fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries).truncTotal k := by
  classical
  ext d
  by_cases hd : d.degree < k
  · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, coeff_subst ha, coeff_subst, finsum_congr]
    · intro n
      congr! 1
      rw [Finsupp.prod, Finsupp.prod, coeff_prod, coeff_prod]
      congr! 2 with l hl i hi
      obtain ⟨hl₁, hl₂⟩ := mem_finsuppAntidiag.mp hl
      have : (l i).degree ≤ d.degree := by
        rw [← hl₁, (n.support.sum l).degree_apply, Finsupp.degree_apply]
        refine .trans (sum_le_sum_of_subset ?_) (sum_le_sum ?_)
        · intro t ht
          have := DFunLike.congr_fun hl₁ t
          by_contra hc
          simp only [Finsupp.coe_finsetSum, sum_apply] at this
          simp_all
        · intro t ht
          rw [sum_apply']
          convert single_le_sum_of_canonicallyOrdered hi (M := ℕ)
          rfl
      exact_mod_cast (coeff_truncTotal_pow _ (by nlinarith [hx i])).symm
    · exact HasSubst.truncTotal ha
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

theorem truncTotal_subst_eq_sum_left  (ha : HasSubst a)
    (ha₁ : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) =
      ((∑ i ∈ range k, (f.homogeneousComponent i)).subst a).truncTotal k := by
  ext d
  by_cases hd : d.degree < k
  · simp_rw [coeff_truncTotal _ hd, coeff_subst ha]
    obtain h1 := coeff_subst_finite ha f d
    obtain h2 := coeff_subst_finite ha (∑ i ∈ range k, (homogeneousComponent i) f) d
    rw [finsum_eq_sum _ h1, finsum_eq_sum _ h2]
    have : Set.Finite.toFinset h2 ⊆ Set.Finite.toFinset h1 := by
      simp +contextual [coeff_homogeneousComponent]
    have aux₀ {n : σ →₀ ℕ} : coeff d (n.prod fun s e ↦ a s ^ e) ≠ 0 → n.degree ≤ d.degree := by
      contrapose!
      intro hc
      rw [Finsupp.prod]
      refine coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.mpr hc)
        (.trans ?_ (le_order_prod _ n.support)))
      exact_mod_cast sum_le_sum fun i hi => le_order_pow_of_constantCoeff_eq_zero _ (ha₁ i)
    rw [← Finset.sum_subset this]
    congr! 2 with n hn
    · simp only [map_sum, coeff_homogeneousComponent, sum_ite_eq, mem_range, left_eq_ite_iff,
        not_lt]
      have : n.degree ≤ d.degree := by
        simp only [map_sum, Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hn
        exact aux₀ (right_ne_zero_of_smul hn)
      intro h
      nlinarith
    simp +contextual [coeff_homogeneousComponent]
    intro x hx
    nlinarith [aux₀ (right_ne_zero_of_smul hx)]
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

theorem truncTotal_subst_eq_sum_left'  (ha : HasSubst a)
    (ha₁ : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a)
      = (∑ i ∈ range k, (f.homogeneousComponent i).subst a).truncTotal k := by
  rw [truncTotal_subst_eq_sum_left ha ha₁, ← substAlgHom_apply ha, map_sum]
  simp

theorem truncTotal_subst_eq_truncTotal_left [Finite σ]
    (ha₁ : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a)
      = ((f.truncTotal k).toMvPowerSeries.subst a).truncTotal k := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha₁
  rw [truncTotal_subst_eq_sum_left ha ha₁, truncTotal_eq_sum]

theorem truncTotal_subst_of_le [Finite σ] (ha : HasSubst a) (h : ∀ i, (a i).constantCoeff = 0)
    (hx : ∀ i, k ≤ x i) :
    truncTotal k (f.subst a) = (∑ i ∈ range k, (f.homogeneousComponent i).subst
      (fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_right_of_le ha hx]
  refine truncTotal_subst_eq_sum_left' (HasSubst.truncTotal ha) ?_
  intro i
  rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    ← MvPolynomial.constantCoeff_eq, constantCoeff_truncTotal_eq_ite, h i, ite_self]

theorem truncTotal_subst [Finite σ] (ha : HasSubst a) (h : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = (∑ i ∈ range k, (f.homogeneousComponent i).subst
      (fun i ↦ ((a i).truncTotal k).toMvPowerSeries)).truncTotal k :=
  truncTotal_subst_of_le ha h fun _ ↦ le_refl k

end truncTotal

end MvPowerSeries

namespace PowerSeries

variable {R S σ τ : Type*} [CommRing R] [CommRing S] {f : PowerSeries R} {a b : MvPowerSeries σ S}
  {n : ℕ} [Algebra R S]


lemma truncTotal_subst [Finite σ] :
    (f.subst a).truncTotal n = (f.subst (a.truncTotal n)).truncTotal n := sorry

lemma constantCoeff_toMvPowerSeries {p : PowerSeries R} (hp : p.constantCoeff = 0) :
    ∀ i : σ, (p.toMvPowerSeries i).constantCoeff = 0 := by

  sorry

lemma homogeneous_subst_add (hf : f.constantCoeff = 0) (ha : a.constantCoeff = 0) :
    (f.subst (a + b.homogeneousComponent n)).homogeneousComponent n =
      (f.subst a).homogeneousComponent n + f.coeff 1 • b.homogeneousComponent n := by
  ext d
  simp [MvPowerSeries.coeff_homogeneousComponent]
  by_cases h : d.degree = n
  · simp_rw [if_pos h]
    rw [coeff_subst]
    sorry
    sorry
  simp [if_neg h]

end PowerSeries

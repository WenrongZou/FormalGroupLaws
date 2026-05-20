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

lemma constantCoeff_eq_of_truncTotal_two_eq {q : MvPowerSeries σ R}
    (h : p.truncTotal 2 = q.truncTotal 2) :
    p.constantCoeff = q.constantCoeff := calc
  _ = (p.truncTotal 2).constantCoeff := by simp [constantCoeff_truncTotal_eq_ite]
  _ = _ := by simp [h, constantCoeff_truncTotal_eq_ite]

lemma truncTotal_two_eq_of_constantCoeff_eq_zero_of_homogeneousComponent_one_eq
    {p q : MvPowerSeries σ R} (hp : p.constantCoeff = 0)
    (hq : q.constantCoeff = 0) (h : p.homogeneousComponent 1 = q.homogeneousComponent 1) :
    p.truncTotal 2 = q.truncTotal 2 := by
  ext d
  by_cases hd : d.degree < 2
  · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd]
    rcases show d.degree = 0 ∨ d.degree = 1 by omega with hd0 | hd1
    · have hd_zero : d = 0 := d.degree_eq_zero_iff.mp hd0
      simp [hd_zero, hp, hq]
    · have hcoeff := congr_fun h d
      change coeff d (homogeneousComponent 1 p) =
        coeff d (homogeneousComponent 1 q) at hcoeff
      rw [coeff_homogeneousComponent, if_pos hd1, coeff_homogeneousComponent,
        if_pos hd1] at hcoeff
      exact hcoeff
  · simp [coeff_truncTotal_eq_ite, hd]

omit [Finite σ] in
lemma homogeneousComponent_one_eq_self_of_constantCoeff_eq_zero_of_coeff_zero_of_one_lt_degree
    {p : MvPowerSeries σ R} (h0 : p.constantCoeff = 0)
    (hgt : ∀ d : σ →₀ ℕ, 1 < d.degree → coeff d p = 0) :
    p.homogeneousComponent 1 = p := by
  ext d
  by_cases hd : d.degree = 1
  · simp [coeff_homogeneousComponent, hd]
  · rw [coeff_homogeneousComponent, if_neg hd]
    rcases Nat.lt_or_gt_of_ne hd with hd0 | hlt
    · have hd_zero : d = 0 := d.degree_eq_zero_iff.mp (by omega)
      simp [hd_zero, h0]
    · exact (hgt d hlt).symm

lemma eq_of_forall_truncTotal_eq {f g : MvPowerSeries σ R} :
    f = g ↔ ∀ k, f.truncTotal k = g.truncTotal k := by
  constructor
  · intro h k
    rw [h]
  · intro h
    ext d
    have hd : d.degree < d.degree + 1 := Nat.lt_succ_self _
    rw [← coeff_truncTotal _ hd, h (d.degree + 1), coeff_truncTotal _ hd]

end

lemma HasSubst.truncTotal_toMvPowerSeries {a : σ → MvPowerSeries τ S} {x : σ → ℕ} [Finite τ] (ha : HasSubst a) :
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
        refine .trans (sum_le_sum_of_subset fun t ht => ?_) (sum_le_sum fun t ht => ?_)
        · have := DFunLike.congr_fun hl₁ t
          by_contra hc
          simp only [Finsupp.coe_finsetSum, sum_apply] at this
          simp_all
        · rw [sum_apply']
          convert single_le_sum_of_canonicallyOrdered hi (M := ℕ)
          rfl
      exact_mod_cast (coeff_truncTotal_pow _ (by nlinarith [hx i])).symm
    · exact ha.truncTotal_toMvPowerSeries
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

theorem truncTotal_subst_eq_subst_sum (ha : HasSubst a) (ha₁ : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) =
      ((∑ i ∈ range k, (f.homogeneousComponent i)).subst a).truncTotal k := by
  ext d
  by_cases hd : d.degree < k
  · simp_rw [coeff_truncTotal _ hd, coeff_subst ha]
    obtain h1 := coeff_subst_finite ha f d
    obtain h2 := coeff_subst_finite ha (∑ i ∈ range k, (homogeneousComponent i) f) d
    rw [finsum_eq_sum _ h1, finsum_eq_sum _ h2]
    have : h2.toFinset ⊆ h1.toFinset := by simp +contextual [coeff_homogeneousComponent]
    have aux {n : σ →₀ ℕ} : coeff d (n.prod fun s e ↦ a s ^ e) ≠ 0 → n.degree ≤ d.degree := by
      contrapose!
      intro hc
      rw [Finsupp.prod]
      refine coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.mpr hc)
        (.trans ?_ (le_order_prod _ n.support)))
      exact_mod_cast sum_le_sum fun i hi => le_order_pow_of_constantCoeff_eq_zero _ (ha₁ i)
    rw [← Finset.sum_subset this]
    · congr! 2 with n hn
      simp only [map_sum, coeff_homogeneousComponent, sum_ite_eq, mem_range, left_eq_ite_iff,
        not_lt]
      have : n.degree ≤ d.degree := by
        simp only [map_sum, Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hn
        exact aux (right_ne_zero_of_smul hn)
      intro h
      nlinarith
    · simp +contextual only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, map_sum,
        coeff_homogeneousComponent, sum_ite_eq, mem_range, ite_smul, zero_smul, ite_eq_right_iff,
        imp_false, not_lt, not_le]
      intro x hx
      nlinarith [aux (right_ne_zero_of_smul hx)]
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

theorem truncTotal_subst_eq_sum_subst (ha : HasSubst a) (ha₁ : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) =
      (∑ i ∈ range k, (f.homogeneousComponent i).subst a).truncTotal k := by
  rw [truncTotal_subst_eq_subst_sum ha ha₁, ← substAlgHom_apply ha, map_sum]
  simp

theorem truncTotal_subst_eq_truncTotal_left [Finite σ] (h : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst a).truncTotal k := by
  rw [truncTotal_subst_eq_subst_sum (hasSubst_of_constantCoeff_zero h) h, truncTotal_eq_sum]

theorem truncTotal_subst_eq_sum_subst_of_le (ha : HasSubst a) (h : ∀ i, (a i).constantCoeff = 0)
    (hx : ∀ i, k ≤ x i) :
    truncTotal k (f.subst a) = (∑ i ∈ range k, (f.homogeneousComponent i).subst
      (fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_right_of_le ha hx]
  exact truncTotal_subst_eq_sum_subst ha.truncTotal_toMvPowerSeries fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, constantCoeff_truncTotal_eq_ite, h i, ite_self]

theorem truncTotal_subst_of_le [Finite σ] (h : ∀ i, (a i).constantCoeff = 0) (hx : ∀ i, k ≤ x i) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst
      (fun i ↦ ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k := by
  rw [truncTotal_subst_eq_sum_subst_of_le (hasSubst_of_constantCoeff_zero h) h hx,
    truncTotal_eq_sum, ← substAlgHom_apply
      (hasSubst_of_constantCoeff_zero h).truncTotal_toMvPowerSeries, map_sum]
  simp

theorem truncTotal_subst [Finite σ] (h : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst
      (fun i ↦ ((a i).truncTotal k).toMvPowerSeries)).truncTotal k :=
  truncTotal_subst_of_le h fun _ ↦ le_refl k

theorem truncTotal_subst_eq_sum (ha : HasSubst a) (h : ∀ i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = (∑ i ∈ range k, (f.homogeneousComponent i).subst
      (fun i ↦ ((a i).truncTotal k).toMvPowerSeries)).truncTotal k :=
  truncTotal_subst_eq_sum_subst_of_le ha h fun _ ↦ le_refl k

end truncTotal

end MvPowerSeries

namespace PowerSeries

variable {R S σ τ : Type*} [CommRing R] [CommRing S] {f : PowerSeries R} {a b : MvPowerSeries σ S}
  {n : ℕ} [Algebra R S]

lemma truncTotal_subst [Finite σ] (ha : PowerSeries.HasSubst a) :
    (f.subst a).truncTotal n = (f.subst (a.truncTotal n)).truncTotal n := by
  rw [subst, MvPowerSeries.truncTotal_subst_eq_truncTotal_right_of_le ha.const fun _ ↦ le_rfl,
    subst]

lemma truncTotal_subst_eq_trunc [Finite σ] (ha : a.constantCoeff = 0) :
    (f.subst a).truncTotal n = ((f.trunc n).toPowerSeries.subst a).truncTotal n := by
  rw [subst, MvPowerSeries.truncTotal_subst_eq_truncTotal_left (fun _ => ha)]
  congr
  ext d
  rw [Polynomial.coeff_coe, coeff_trunc, coeff, MvPolynomial.coeff_coe]
  simp [MvPowerSeries.coeff_truncTotal_eq_ite]

lemma constantCoeff_toMvPowerSeries {p : PowerSeries R} (hp : p.constantCoeff = 0) :
    ∀ i : σ, (p.toMvPowerSeries i).constantCoeff = 0 := by
  intro i
  rw [PowerSeries.toMvPowerSeries_apply,
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hp]

lemma homogeneousComponent_one_toMvPowerSeries (p : PowerSeries R) (i : σ) :
    (p.toMvPowerSeries i).homogeneousComponent 1 = p.coeff 1 • MvPowerSeries.X i := by
  classical
  ext d
  by_cases hdi : d = Finsupp.single i 1
  · simp [MvPowerSeries.coeff_homogeneousComponent, PowerSeries.toMvPowerSeries_apply,
      PowerSeries.coeff_subst_single, hdi]
  · have haux : ¬(d.degree = 1 ∧ d = Finsupp.single i (d i)) := by
      rintro ⟨hd, hd'⟩
      apply hdi
      rw [hd']
      congr
      rw [hd', Finsupp.degree_single] at hd
      exact hd
    by_cases hd1 : d.degree = 1
    · have hd' : ¬ d = Finsupp.single i (d i) := fun hd' => haux ⟨hd1, hd'⟩
      rw [MvPowerSeries.coeff_homogeneousComponent, PowerSeries.toMvPowerSeries_apply,
        PowerSeries.coeff_subst_single, if_pos hd1, if_neg hd']
      simp [MvPowerSeries.coeff_X, hdi]
    · rw [MvPowerSeries.coeff_homogeneousComponent, PowerSeries.toMvPowerSeries_apply,
        PowerSeries.coeff_subst_single, if_neg hd1]
      simp [MvPowerSeries.coeff_X, hdi]

lemma homogeneous_subst_add (hf : f.constantCoeff = 0) (ha : a.constantCoeff = 0)
    (hn : n ≠ 0) :
    (f.subst (a + b.homogeneousComponent n)).homogeneousComponent n =
      (f.subst a).homogeneousComponent n + f.coeff 1 • b.homogeneousComponent n := by
  let H := b.homogeneousComponent n
  have hH0 : H.constantCoeff = 0 := by
    simp +contextual [← MvPowerSeries.coeff_zero_eq_constantCoeff, H,
      MvPowerSeries.coeff_homogeneousComponent, hn.symm]
  have hsubst_add : HasSubst (a + H) := HasSubst.of_constantCoeff_zero (by simp [ha, hH0])
  have hsubst_a : PowerSeries.HasSubst a := HasSubst.of_constantCoeff_zero ha
  have hpow_eq {d : σ →₀ ℕ} (hd : d.degree = n) (k : ℕ) (hk : 2 ≤ k) :
      MvPowerSeries.coeff d ((a + H) ^ k) = MvPowerSeries.coeff d (a ^ k) := by
    let Q : MvPowerSeries σ S :=
      ∑ i ∈ Finset.range k, (a + H) ^ i * a ^ (k - 1 - i)
    have hQ0 : Q.constantCoeff = 0 := by
      simp only [Q, map_sum, map_mul, map_pow]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi_lt : i < k := Finset.mem_range.mp hi
      by_cases hi0 : i = 0
      · have hpos : 0 < k - 1 - i := by
          rw [hi0, tsub_zero]
          exact Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two hk)
        simpa [hi0, ha] using (zero_pow hpos.ne' : (0 : S) ^ (k - 1 - i) = 0)
      · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
        simp [ha, hH0, zero_pow hpos.ne']
    have hH_order : (n : ℕ∞) ≤ H.order := by
      refine MvPowerSeries.nat_le_order fun e he => ?_
      rw [MvPowerSeries.coeff_homogeneousComponent]
      exact if_neg (ne_of_lt he)
    have hQ_order : (1 : ℕ∞) ≤ Q.order :=
      MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hQ0
    have hprod_order : (n + 1 : ℕ∞) ≤ (H * Q).order := by
      calc
        (n + 1 : ℕ∞) = (n : ℕ∞) + (1 : ℕ∞) := by norm_num
        _ ≤ H.order + Q.order := add_le_add hH_order hQ_order
        _ ≤ (H * Q).order := MvPowerSeries.order_mul_ge
    have hdiff : (a + H) ^ k - a ^ k = H * Q := by
      have hgeom := (Commute.all (a + H) a).mul_geom_sum₂ k
      simpa [Q, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgeom.symm
    rw [← sub_eq_zero, ← map_sub, hdiff]
    exact MvPowerSeries.coeff_of_lt_order (by
      rw [hd]
      exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hprod_order)
  ext d
  simp [MvPowerSeries.coeff_homogeneousComponent]
  by_cases h : d.degree = n
  · simp_rw [if_pos h]
    rw [PowerSeries.coeff_subst hsubst_add, PowerSeries.coeff_subst hsubst_a]
    have hterm (k : ℕ) :
        f.coeff k • MvPowerSeries.coeff d ((a + H) ^ k) =
          f.coeff k • MvPowerSeries.coeff d (a ^ k) +
            (if k = 1 then f.coeff 1 • MvPowerSeries.coeff d H else 0) := by
      rcases lt_or_ge k 2 with hk | hk
      · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hk)
        · simp [PowerSeries.coeff_zero_eq_constantCoeff, hf]
        · simp [H]
      · rw [hpow_eq h k hk]
        simp [show k ≠ 1 by exact ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hk)]
    calc
      finsum (fun k : ℕ => f.coeff k • MvPowerSeries.coeff d ((a + H) ^ k))
          = finsum (fun k : ℕ =>
              f.coeff k • MvPowerSeries.coeff d (a ^ k) +
                (if k = 1 then f.coeff 1 • MvPowerSeries.coeff d H else 0)) := by
            exact finsum_congr hterm
      _ = finsum (fun k : ℕ => f.coeff k • MvPowerSeries.coeff d (a ^ k)) +
            finsum (fun k : ℕ => if k = 1 then f.coeff 1 • MvPowerSeries.coeff d H else 0) := by
            rw [finsum_add_distrib]
            · exact PowerSeries.coeff_subst_finite hsubst_a f d
            · rw [Function.HasFiniteSupport]
              refine (Set.finite_singleton 1).subset ?_
              intro k hk
              simp only [Function.mem_support, ne_eq] at hk ⊢
              by_contra hk1
              exact hk (by simp [show k ≠ 1 by simpa using hk1])
      _ = finsum (fun k : ℕ => f.coeff k • MvPowerSeries.coeff d (a ^ k)) +
            f.coeff 1 • MvPowerSeries.coeff d H := by
            congr 1
            rw [finsum_eq_single (a := 1)]
            · simp
            · intro k hk
              simp [hk]
      _ = finsum (fun k : ℕ => f.coeff k • MvPowerSeries.coeff d (a ^ k)) +
            f.coeff 1 • MvPowerSeries.coeff d b := by
            simp [H, MvPowerSeries.coeff_homogeneousComponent, h]
  simp [if_neg h]

end PowerSeries

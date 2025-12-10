import FormalGroupLaws.Basic
import FormalGroupLaws.BasicLem
import Mathlib.RingTheory.PowerSeries.PiTopology
import FormalGroupLaws.MvPowerSeries
import Mathlib.Algebra.CharP.Lemmas

/-!
#Functional Integrality Lemma.

In this file, given a power series with integral coefficient, we construct a formal power series
using a functional equation, and prove some integrality lemmas related to this formal power series.

-/
noncomputable section

open Classical Finset FormalGroup
open scoped MvPowerSeries.WithPiTopology

/- The basic ingredients in this section are `R ⊆ K, σ : K → K, I ⊆ R, p, q, s₁, s₂ ⋯`,
  where `R` is a subring of `K`, `σ` is a ring homomorphism of `K`, which stablize `A`,
  `I` is an ideal of `A`, `p` is a prime number and `q` is a power of `p`, `s_i` are
  elements of `K`. -/

variable {K : Type*} [CommRing K] {R : Subring K} {I : Ideal R}
  {p t q : ℕ} [hp : Fact (Nat.Prime p)] (ht : t ≠ 0) (hq : q = p ^ t)
  (σ : K →+* K)  (hs : ∀ (a : R), σ a ∈ R) (a_congr : ∀ a : R, ⟨σ a, hs a⟩ ≡  (a ^ q) [SMOD I])
  (hp_mem : (p : R) ∈ I) (s : ℕ → K) (hs_i : ∀ i, ∀ a, a ∈ R.subtype '' I → s i * a ∈ R)
  (hs_i' :∀ r, ∀ b, (∀ a, (a ∈ R.subtype '' (I^r : Ideal R)) → b * a ∈ R.subtype '' I)
    → (∀ a, a ∈ R.subtype '' (I^r : Ideal R) → (σ b) * a ∈ R.subtype '' I))

section FunctionalEquation

variable {g : PowerSeries R} (hg : g.constantCoeff = 0) (h_unit : IsUnit (g.coeff 1))

include hq in
lemma q_pow_neZero {x : ℕ} : q ^ x ≠ 0 :=
  pow_ne_zero x (hq ▸ pow_ne_zero t <| (NeZero.ne' p).symm)

include ht hq in
lemma isPrimePow_q : IsPrimePow q := hq ▸ IsPrimePow.pow (Nat.Prime.isPrimePow hp.out) ht

include ht hq in
lemma q_neOne : q ≠ 1 := IsPrimePow.ne_one <| isPrimePow_q ht hq

/-- define the $f_g$ by its coefficient recursively, and then we prove the functional equation
for $f_g$, namely $f_g(X)=g(X)+∑_{i=1}^∞ s_i σ^i f_g(X^{q^i})$.-/
def RecurFunAux (hg : PowerSeries.constantCoeff g = 0) : ℕ → K
  | 0 => 0
  | k + 1 =>
    PowerSeries.coeff (k + 1) g + ∑ j ∈ (Icc 1 (multiplicity q (k + 1))).attach,
      have aux : ((k + 1) / (q ^ (j : ℕ))) < k + 1 := by
        have hj1 : ↑j ≥ (1 : ℕ) := List.left_le_of_mem_range' j.property
        exact Nat.div_lt_self (by linarith) <| Nat.one_lt_pow (by linarith)
          <| hq ▸ Nat.one_lt_pow ht (Nat.Prime.one_lt' p).out
      (s j) * σ^[j] (RecurFunAux hg ((k + 1) / (q ^ (j : ℕ))))

def RecurFun := PowerSeries.mk (RecurFunAux ht hq σ s hg)

/-- constant coefficient of `f_g` is zero-/
lemma constantCoeff_RecurFun :
    PowerSeries.constantCoeff (RecurFun ht hq σ s hg) = 0 := by
  simp [RecurFun, RecurFunAux]

/- First coefficient of `f_g` is equal to `coeff 1 g`. -/
lemma coeff_RecurFun_one : (RecurFun ht hq σ s hg).coeff 1 = g.coeff 1 := by
  simp only [RecurFun, PowerSeries.coeff_mk, RecurFunAux, zero_add, Nat.reduceAdd, add_eq_left]
  have empty_aux : (multiplicity q 1) = 0 :=
    multiplicity_eq_zero.mpr <| Nat.not_dvd_of_pos_of_lt (by linarith)
      <| IsPrimePow.two_le (isPrimePow_q ht hq)
  rw [empty_aux, show Icc 1 0 = ∅ by rfl, attach_empty, sum_empty]

/-- First coefficient of `f_g` is unit-/
lemma coeff_RecurFun_unit (hg_unit : IsUnit ((PowerSeries.coeff 1) g)) :
    IsUnit ((RecurFun ht hq σ s hg).coeff 1) := by
  rw [coeff_RecurFun_one]
  obtain ⟨b, hb₁, hb₂⟩ := isUnit_iff_exists.mp hg_unit
  exact isUnit_iff_exists.mpr ⟨b, by norm_cast⟩

open PowerSeries FiniteMultiplicity in
include ht hq hg in
lemma hasSum_aux [TopologicalSpace K] [Nontrivial K] (hs₀ : s 0 = 0) :
    HasSum (fun i ↦ s i • ((RecurFun ht hq σ s hg).subst ((monomial (q^i)) 1)).map (σ^i))
      (RecurFun ht hq σ s hg - g.map R.subtype) := by
  classical
  let x := fun i ↦ s i • ((RecurFun ht hq σ s hg).subst ((monomial (q^i)) 1)).map (σ^i)
  have eq_aux : (RecurFun ht hq σ s hg - g.map R.subtype) =
    (fun n => ∑ i ∈ Finset.range (n.degree + 1), ((x i).coeff n)) := by
    ext d
    nth_rw 2 [coeff]
    rw [MvPowerSeries.coeff_apply]
    by_cases hd₀ : d = 0
    · simp [hd₀, RecurFun, RecurFunAux, x, hg, hs₀]
    · nth_rw 1 [show d = d - 1 + 1 by omega]
      simp [RecurFun, RecurFunAux, x]
      erw [show d - 1 + 1 = d by omega]
      rw [sum_attach (Icc 1 (multiplicity q d))
        (fun x => s x * (σ)^[x] (RecurFunAux ht hq σ s hg (d / q ^ x)))]
      have subset_aux : Icc 1 (multiplicity q d) ≤ range (d + 1) :=
        subset_range.mpr fun x hx => Order.lt_add_one_iff.mpr <| .trans (Nat.lt_pow_self
          <| IsPrimePow.one_lt <| isPrimePow_q ht hq).le (Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hd₀)
            <| pow_dvd_of_le_multiplicity (mem_Icc.mp hx).2)
      rw [←sum_subset subset_aux _ , sum_congr rfl _]
      · intro x hx
        congr
        rw [coeff_subst' _, finsum_eq_single _ (d / q^x) _, coeff_mk, monomial_pow,
          coeff_monomial, if_pos _, one_pow, smul_eq_mul, mul_one]
        · exact (Nat.div_mul_cancel <| pow_dvd_of_le_multiplicity (mem_Icc.mp hx).2).symm
        · intro y hy
          rw [coeff_mk, monomial_pow, coeff_monomial, if_neg, smul_zero]
          by_contra hc
          rw [hc, mul_div_cancel_right₀ y <| q_pow_neZero hq] at hy
          contradiction
        · exact HasSubst.monomial' (q_pow_neZero hq) 1
      · intro x hx₁ hx₂
        by_cases hx₀ : x = 0
        · simp [hx₀, hs₀]
        have eq_zero : (coeff d) (subst ((monomial (q ^ x)) (1 : K)) (PowerSeries.mk
          (RecurFunAux ht hq σ s hg))) = 0 := by
          rw [coeff_subst' <| HasSubst.monomial' (q_pow_neZero hq) 1, finsum_eq_zero_of_forall_eq_zero]
          · intro y
            rw [coeff_mk, monomial_pow, coeff_monomial, if_neg, smul_zero]
            by_contra hc
            simp only [mem_Icc, not_and] at hx₂
            exact (hx₂ <| Nat.one_le_iff_ne_zero.mpr hx₀) <| le_multiplicity_of_pow_dvd
              (Nat.finiteMultiplicity_iff.mpr ⟨q_neOne ht hq, Nat.zero_lt_of_ne_zero hd₀⟩)
                (hc ▸ Nat.dvd_mul_left _ _ )
        simp [eq_zero]
  rw [eq_aux]
  apply MvPowerSeries.HasSum.increase_order
  intro n
  rw [smul_eq_C_mul, subst_map <| HasSubst.monomial' (q_pow_neZero hq) 1]
  refine .trans (le_add_of_le_right (.trans ?_ (le_order_subst _
    (HasSubst.monomial' (q_pow_neZero hq) 1) _))) (MvPowerSeries.le_order_mul)
  rw [←order_eq_order, order_monomial, if_neg one_ne_zero]
  obtain h := (Nat.lt_pow_self (n := n) (hq ▸ Nat.one_lt_pow ht (Nat.Prime.one_lt' p).out)).le
  refine .trans (ENat.self_le_mul_right ↑n (zero_ne_one' ℕ∞).symm) <| mul_le_mul' (by norm_cast)
    <| ENat.one_le_iff_ne_zero.mpr <| order_ne_zero_iff_constCoeff_eq_zero.mpr ?_
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_RecurFun, map_zero]


open PowerSeries in
include ht hq hg in
lemma summable_aux [TopologicalSpace K] [Nontrivial K] (hs₀ : s 0 = 0) :
    Summable (fun i ↦ s i • ((RecurFun ht hq σ s hg).subst ((monomial (q^i)) 1)).map (σ^i)) := by
  use (RecurFun ht hq σ s hg - g.map R.subtype)
  exact hasSum_aux ht hq σ s hg hs₀





end FunctionalEquation

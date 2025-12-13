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
  (hp_mem : (p : R) ∈ I) (s : ℕ → K) (hs₁ : ∀ i, ∀ a, a ∈ R.subtype '' I → s i * a ∈ R)
  (hs₂ : ∀ r, ∀ b, (∀ a, (a ∈ R.subtype '' (I^r : Ideal R)) → b * a ∈ R.subtype '' I)
    → (∀ a, a ∈ R.subtype '' (I^r : Ideal R) → (σ b) * a ∈ R.subtype '' I))

section FunctionalEquation

variable {g : PowerSeries R} (hg : g.constantCoeff = 0)

include hq in
lemma q_pow_neZero {x : ℕ} : q ^ x ≠ 0 :=
  pow_ne_zero x (hq ▸ pow_ne_zero t <| (NeZero.ne' p).symm)

include ht hq in
lemma isPrimePow_q : IsPrimePow q := hq ▸ IsPrimePow.pow (Nat.Prime.isPrimePow hp.out) ht

include ht hq in
lemma q_neOne : q ≠ 1 := IsPrimePow.ne_one <| isPrimePow_q ht hq

/-- define the $f_g$ by its coefficient recursively, and then we prove the functional equation
for $f_g$, namely $f_g(X)=g(X)+∑_{i=1}^∞ s_i σ^i f_g(X^{q^i})$.-/
def RecurFunAux (hg : g.constantCoeff = 0) : ℕ → K
  | 0 => 0
  | k + 1 =>
    g.coeff (k + 1) + ∑ j ∈ (Icc 1 (multiplicity q (k + 1))).attach,
      have aux : ((k + 1) / (q ^ (j : ℕ))) < k + 1 :=
        Nat.div_lt_self (by linarith) <| Nat.one_lt_pow
          (by nlinarith [List.left_le_of_mem_range' j.property])
            <| hq ▸ Nat.one_lt_pow ht (Nat.Prime.one_lt' p).out
      (s j) * σ^[j] (RecurFunAux hg ((k + 1) / (q ^ (j : ℕ))))

def RecurFun := PowerSeries.mk (RecurFunAux ht hq σ s hg)

/-- constant coefficient of `f_g` is zero-/
lemma constantCoeff_RecurFun : (RecurFun ht hq σ s hg).constantCoeff = 0 := by
  simp [RecurFun, RecurFunAux]

/- First coefficient of `f_g` is equal to `coeff 1 g`. -/
lemma coeff_one_RecurFun: (RecurFun ht hq σ s hg).coeff 1 = g.coeff 1 := by
  simp only [RecurFun, PowerSeries.coeff_mk, RecurFunAux, zero_add, Nat.reduceAdd, add_eq_left]
  have empty_aux : (multiplicity q 1) = 0 :=
    multiplicity_eq_zero.mpr <| Nat.not_dvd_of_pos_of_lt (by linarith)
      <| IsPrimePow.two_le (isPrimePow_q ht hq)
  rw [empty_aux, show Icc 1 0 = ∅ by rfl, attach_empty, sum_empty]

/-- First coefficient of `f_g` is unit-/
lemma coeff_RecurFun_unit (hg_unit : IsUnit (g.coeff 1)) :
    IsUnit ((RecurFun ht hq σ s hg).coeff 1) := by
  rw [coeff_one_RecurFun]
  obtain ⟨b, hb₁, hb₂⟩ := isUnit_iff_exists.mp hg_unit
  exact isUnit_iff_exists.mpr ⟨b, by norm_cast⟩

open PowerSeries FiniteMultiplicity in
include ht hq hg in
lemma hasSum_aux [TopologicalSpace K] (hs₀ : s 0 = 0) :
    HasSum (fun i ↦ s i • ((RecurFun ht hq σ s hg).subst ((monomial (q^i)) 1)).map (σ^i))
      (RecurFun ht hq σ s hg - g.map R.subtype) := by
  classical
  let x := fun i ↦ s i • ((RecurFun ht hq σ s hg).subst ((monomial (q^i)) 1)).map (σ^i)
  have eq_aux : (RecurFun ht hq σ s hg - g.map R.subtype) =
    (fun n => ∑ i ∈ range (n.degree + 1), ((x i).coeff n)) := by
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
          rw [coeff_mk, monomial_pow, coeff_monomial, if_neg _, smul_zero]
          by_contra hc
          rw [hc, mul_div_cancel_right₀ y <| q_pow_neZero hq] at hy
          contradiction
        · exact HasSubst.monomial' (q_pow_neZero hq) 1
      · intro x hx₁ hx₂
        by_cases hx₀ : x = 0
        · simp [hx₀, hs₀]
        have eq_zero : (coeff d) (subst ((monomial (q ^ x)) (1 : K)) (.mk
          (RecurFunAux ht hq σ s hg))) = 0 := by
          rw [coeff_subst' <| HasSubst.monomial' (q_pow_neZero hq) 1,
            finsum_eq_zero_of_forall_eq_zero]
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
  rw [←order_eq_order, order_monomial]
  have neZero : ((PowerSeries.map (σ ^ n)) (RecurFun ht hq σ s hg)).order ≠ 0 :=
    order_ne_zero_iff_constCoeff_eq_zero.mpr <| by simp [constantCoeff_RecurFun ht hq σ s hg]
  split_ifs with h
  · rw [ENat.top_mul neZero]; exact le_top
  obtain h := (Nat.lt_pow_self (n := n) (hq ▸ Nat.one_lt_pow ht (Nat.Prime.one_lt' p).out)).le
  refine .trans (ENat.self_le_mul_right ↑n (zero_ne_one' ℕ∞).symm) <| mul_le_mul' (by norm_cast)
    <| ENat.one_le_iff_ne_zero.mpr neZero

open PowerSeries in
include ht hq hg in
lemma summable_aux [TopologicalSpace K] (hs₀ : s 0 = 0) :
    Summable (fun i ↦ s i • ((RecurFun ht hq σ s hg).subst ((monomial (q^i)) 1)).map (σ^i)) :=
  ⟨(RecurFun ht hq σ s hg - g.map R.subtype), hasSum_aux ht hq σ s hg hs₀ ⟩

open PowerSeries in
/-- this is the function equation that `f_g` satisfies, namely
  $f_g(X) = g(X) + ∑' s_i * σ^i f(X^{q^i})$-/
theorem FunEq_of_RecurFun [TopologicalSpace K] [T2Space K] (hs₀ : s 0 = 0) :
    let f := (RecurFun ht hq σ s hg)
    f = g.map R.subtype + ∑' (i : ℕ), s i • (f.subst ((monomial (q^i)) 1)).map (σ^i) := by
  intro _
  rw [HasSum.tsum_eq <| hasSum_aux ht hq σ s hg hs₀]
  ring

end FunctionalEquation

section technical_lemma

variable {g : PowerSeries R} (hg : g.constantCoeff = 0) (hg_unit : IsUnit (g.coeff 1))

lemma image_of_incl_mem {J : Ideal R} : ∀ x, x ∈ R.subtype '' J → x ∈ R := fun x hx => by
  obtain ⟨y, hy₁, hy₂⟩ := hx
  simp only [← hy₂,Subring.subtype_apply, SetLike.coe_mem]

include hs in
lemma refinement_hs: ∀ (j : ℕ), ∀ (a : R), (σ ^ j) a ∈ R := fun j => by
  induction j with
  | zero => simp
  | succ k ih =>
    intro a
    have eq_aux : (σ ^ (k + 1)) ↑a = σ ((σ^k) a) := by
      simp [Function.iterate_succ_apply']
    exact eq_aux ▸ hs ⟨_, ih _⟩

include hs₂ in
lemma refinement_hs₂ : ∀ (i r : ℕ), ∀ b, (∀ a, (a ∈ R.subtype '' ↑(I^r))
    → b * a ∈ R.subtype '' I) → (∀ a, a ∈ R.subtype '' ↑(I^r)
    → ((σ)^[i] b) * a ∈ R.subtype '' I) := fun i r b h => by
  induction i with
  | zero => exact h
  | succ k hk => exact (Function.iterate_succ_apply' σ k b) ▸ hs₂ r _ hk

lemma ideal_pow_mem {I : Ideal R} {r : ℕ} {a : K} : (∀ b ∈ I^r, a * b ∈ R)
    → (∀ c ∈ I^r * I, a * c ∈ R.subtype '' I) := fun h c hc => by
  refine Submodule.mul_induction_on hc ?_ ?_
  · intro m hm n hn
    rw [Subring.coe_mul, ← mul_assoc]
    use ⟨a * ↑m * n, Subring.mul_mem R (h m hm) (SetLike.coe_mem n)⟩
    simpa using Ideal.mul_mem_left I (⟨a * ↑m, h _ hm⟩) hn
  · intro x y hx hy
    rw [Subring.coe_add, mul_add]
    obtain ⟨x₁, hx₁, hx₂⟩ := hx
    obtain ⟨y₁, hy₁, hy₂⟩ := hy
    use (x₁ + y₁)
    simp [←hx₂, ←hy₂, (Submodule.add_mem_iff_right I hx₁).mpr hy₁]

lemma ideal_pow_mem' {I : Ideal R} {r s: ℕ} {x : K} (hs : s > r) : (∀ b ∈ I^r, x * b ∈ R)
    → (∀ c ∈ I^s, x * c ∈ R.subtype '' I) :=
  fun h c hc => (ideal_pow_mem h) c ((Ideal.pow_le_pow_right hs) hc)

open FiniteMultiplicity in
lemma multiplicity_aux {n i q : ℕ} (hq : 1 < q) (hn : n > 0) (hi : 1 ≤ i ∧ i ≤ multiplicity q n) :
    multiplicity q (n / q ^ i) < multiplicity q n :=
  (multiplicity_lt_iff_not_dvd (Nat.finiteMultiplicity_iff.mpr
    ⟨(Nat.ne_of_lt hq).symm, Nat.div_pos (Nat.le_of_dvd hn
    <| pow_dvd_of_le_multiplicity hi.2) (by positivity)⟩)).mpr <| by
    by_contra hc
    nlinarith [le_multiplicity_of_pow_dvd (Nat.finiteMultiplicity_iff.mpr
      ⟨(Nat.ne_of_lt hq).symm, hn⟩) <| (pow_add q _ _) ▸
        (Nat.dvd_div_iff_mul_dvd (pow_dvd_of_le_multiplicity hi.2)).mp hc]

include hs₁ hs₂ in
/- First technical lemma: Let $a_n$ be the coefficient of $f_g$, then $a_n * I^r ⊆ R$,
where $r$ is the multiplicity of $q$ in $n$. -/
theorem coeff_RecurFun_mul_mem (n : ℕ) :
    ∀ x, x ∈ R.subtype '' ↑(I^(multiplicity q n)) → ((RecurFun ht hq σ s hg).coeff n) * x ∈ R := by
  generalize h : (multiplicity q n) = m
  induction m using Nat.strongRecOn generalizing n with
  | ind k hk =>
    intro x hx
    by_cases hn₀ : n = 0
    · -- prove the case for n = 0
      simp [hn₀, RecurFun, RecurFunAux]
    · -- the case for n ≥ 1
      rw [← Nat.succ_pred_eq_of_ne_zero hn₀]
      simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, RecurFun, PowerSeries.coeff_mk,
        RecurFunAux]
      rw [show n - 1 + 1 = n by exact Nat.succ_pred_eq_of_ne_zero hn₀, add_mul]
      refine Subring.add_mem _ (Subring.mul_mem _ (SetLike.coe_mem _) (image_of_incl_mem _ hx)) ?_
      · -- second component is in R
        rw [sum_attach _ (fun x ↦ s x * (σ)^[x] (RecurFunAux ht hq σ s hg (n / q ^ x))), sum_mul]
        refine Subring.sum_mem R fun i hi =>
          (mul_assoc (s i) _ _) ▸ hs₁ _ _ (refinement_hs₂ σ hs₂ i k _ (fun b hb => ?_) _ hx)
        have aux : ⟨b, image_of_incl_mem b hb⟩ ∈ I ^ k := by
          obtain ⟨c, hc, hc'⟩ := hb
          exact hc' ▸ hc
        have lt_aux : multiplicity q (n / q ^ i) < k :=
          h.symm ▸  multiplicity_aux (hq ▸ Nat.one_lt_pow ht <| Nat.Prime.one_lt hp.out)
            (by omega) (mem_Icc.mp hi)
        refine ideal_pow_mem' lt_aux ?_ _ aux
        intro y hy
        obtain h' := hk _ lt_aux _ rfl ↑y <| Set.mem_image_of_mem _ hy
        rw [RecurFun, PowerSeries.coeff_mk] at h'
        exact h'

include hs₁ hs₂ in
lemma coeff_RecurFun_mul_mem_i (n i: ℕ) :
  ∀ (x : R), x ∈ I ^ (multiplicity q n + i) →
    ((RecurFun ht hq σ s hg).coeff n) * x ∈ R.subtype '' ↑(I ^ i) := by
  rw [pow_add]
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro y hy z hz
    rw [Subring.coe_mul, ← mul_assoc]
    obtain h₁ := coeff_RecurFun_mul_mem ht hq σ s hs₁ hs₂ hg n y
      (Set.mem_image_of_mem (⇑R.subtype) hy)
    use ⟨(PowerSeries.coeff n) (RecurFun ht hq σ s hg) * ↑y, h₁⟩ * z
    simpa using Ideal.mul_mem_left (I ^ i) _ hz
  · intro y z hy hz
    rw [Subring.coe_add, mul_add]
    obtain ⟨x₁, hx₁, hx₂⟩ := hy
    obtain ⟨y₁, hy₁, hy₂⟩ := hz
    use (x₁ + y₁)
    simp [←hx₂, ←hy₂, (Submodule.add_mem_iff_right (I ^ i) hx₁).mpr hy₁]

include hp_mem in
lemma p_pow_mod_p {G : MvPowerSeries (Fin 2) R} {l : ℕ} (l_pos : 0 < l) :
    ∀ d, ((G ^ (q ^ l)).ofSubring - ((G.subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)]).map (σ^l))).coeff d
      ∈ R.subtype '' I := by
  intro d
  have mem_aux : ((G ^ (q ^ l)).ofSubring -
    ((G.subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)]).map (σ^l))).coeff d ∈ R := by
    sorry
  have pdvd : (p : R) ∣ ⟨_, mem_aux⟩ := by
    sorry
  obtain ⟨pk, hpk⟩ := pdvd
  use ⟨_, mem_aux⟩
  nth_rw 1 [hpk]
  exact ⟨Ideal.IsTwoSided.mul_mem_of_left pk hp_mem, by simp⟩

include ht hq hp_mem hs in
/- Second Technical lemma: Forall `n, l ∈ ℕ` and `G(X,Y) ∈ R⟦X,Y⟧`  with assumption that $n=q^r m$,
we have that $G^{q^r m q^l} ≡ (σ^l G(X^{q^l},Y^{q^l}))^n$. -/
theorem pow_ModEq {G : MvPowerSeries (Fin 2) R} {n r l m : ℕ} (hn : n = q ^ r * m) (hl : l > 0) :
    ∀ d, ((G ^ (n * q ^ l)).ofSubring - (((G.subst ![X₀^(q^l), X₁^(q^l)])^n).map (σ^l))).coeff d
      ∈ R.subtype '' ↑(I^r) := by
  sorry

/- Given a `g ∈ R⟦X⟧`, Recursive function `RecurFun` is $f_g(X) ∈ K⟦X⟧ $, then
`inv_RecurFun` is $f_g^{-1}(X)$. -/
def inv_RecurFun := PowerSeries.subst_inv _ (coeff_RecurFun_unit ht hq σ s hg hg_unit)
  (constantCoeff_RecurFun ..)

lemma coeff_one_inv_RecurFun :
    (inv_RecurFun ht hq σ s hg hg_unit).coeff 1 = hg_unit.unit⁻¹ := by
  simp [inv_RecurFun, PowerSeries.subst_inv, PowerSeries.invFun_aux, coeff_one_RecurFun]
  refine Units.inv_eq_of_mul_eq_one_left ?_
  simp only [IsUnit.unit_spec]
  exact_mod_cast IsUnit.val_inv_mul hg_unit

lemma constantCoeff_inv_RecurFun :
    (inv_RecurFun ht hq σ s hg hg_unit).constantCoeff = 0 := by
  simp [inv_RecurFun, PowerSeries.subst_inv, PowerSeries.invFun_aux]



end technical_lemma

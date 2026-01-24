import FormalGroupLaws.Basic
import FormalGroupLaws.BasicLem
import Mathlib.RingTheory.PowerSeries.PiTopology
import FormalGroupLaws.MvPowerSeries
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Expand
import FormalGroupLaws.ForMathlib.MvPowerSeries

/-!
#Functional Integrality Lemma.

In this file, given a power series with integral coefficient, we construct a formal power series
using a functional equation, and prove some integrality lemmas related to this formal power series.

-/
noncomputable section

open Classical Finset
open scoped MvPowerSeries.WithPiTopology

/- The basic ingredients in this section are `R ⊆ K, σ : K → K, I ⊆ R, p, q, s₁, s₂ ⋯`,
  where `R` is a subring of `K`, `σ` is a ring homomorphism of `K`, which stablize `A`,
  `I` is an ideal of `A`, `p` is a prime number and `q` is a power of `p`, `s_i` are
  elements of `K`. -/

variable {K : Type*} [CommRing K] {R : Subring K} {I : Ideal R} (hI : I ≠ ⊤) {τ : Type*}
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

include hq in
lemma one_le_q_pow {i : ℕ} : 1 ≤ q ^ i := Nat.one_le_iff_ne_zero.mpr (q_pow_neZero hq)

include ht hq in
lemma isPrimePow_q : IsPrimePow q := hq ▸ IsPrimePow.pow (Nat.Prime.isPrimePow hp.out) ht

include ht hq in
lemma q_neOne : q ≠ 1 := IsPrimePow.ne_one <| isPrimePow_q ht hq

include hq in
lemma q_neZero : q ≠ 0 := hq ▸ pow_ne_zero t <| Nat.Prime.ne_zero hp.out

include ht hq in
lemma one_lt_q : 1 < q := IsPrimePow.one_lt <| isPrimePow_q ht hq

include ht hq in
lemma two_le_q_pow {i : ℕ} (hi : i ≠ 0) : 2 ≤ q ^ i  :=
  IsPrimePow.two_le <| IsPrimePow.pow (isPrimePow_q ht hq) hi

/-- define the $f_g$ by its coefficient recursively, and then we prove the functional equation
for $f_g$, namely $f_g(X)=g(X)+∑_{i=1}^∞ s_i σ^i f_g(X^{q^i})$.-/
def RecurFunAux (hg : g.constantCoeff = 0) : ℕ → K
  | 0 => 0
  | k + 1 =>
    g.coeff (k + 1) + ∑ j ∈ (Icc 1 (multiplicity q (k + 1))).attach,
      have : ((k + 1) / (q ^ (j : ℕ))) < k + 1 :=
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
    HasSum (fun i ↦ s i • ((RecurFun ht hq σ s hg).expand (q^i) (q_pow_neZero hq)).map (σ^i))
      (RecurFun ht hq σ s hg - g.map R.subtype) := by
  classical
  let x := fun i ↦ s i • ((RecurFun ht hq σ s hg).expand (q^i) (q_pow_neZero hq)).map (σ^i)
  have eq_aux : (RecurFun ht hq σ s hg - g.map R.subtype) =
    .mk (fun n => ∑ i ∈ range (n + 1), (PowerSeries.coeff n (x i))) := by
    ext d
    rw [coeff_mk]
    by_cases hd₀ : d = 0
    · simp [hd₀, RecurFun, RecurFunAux, x, hg]
    · nth_rw 1 [show d = d - 1 + 1 by omega]
      simp only [RecurFun, map_sub, coeff_mk, RecurFunAux, coeff_map, Subring.subtype_apply,
        add_sub_cancel_left, map_smul, smul_eq_mul, x]
      erw [show d - 1 + 1 = d by omega]
      rw [sum_attach (Icc 1 (multiplicity q d))
        (fun x => s x * (σ)^[x] (RecurFunAux ht hq σ s hg (d / q ^ x)))]
      have subset_aux : Icc 1 (multiplicity q d) ≤ range (d + 1) :=
        subset_range.mpr fun x hx => Order.lt_add_one_iff.mpr <| .trans (Nat.lt_pow_self
          <| IsPrimePow.one_lt <| isPrimePow_q ht hq).le (Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hd₀)
            <| pow_dvd_of_le_multiplicity (mem_Icc.mp hx).2)
      rw [← sum_subset subset_aux _ , sum_congr rfl _]
      · intro x hx
        congr
        rw [PowerSeries.coeff_expand, if_pos (pow_dvd_of_le_multiplicity (mem_Icc.mp hx).2),
          coeff_mk]
      · intro x hx₁ hx₂
        by_cases! hx₀ : x = 0
        · simp [hx₀, hs₀]
        rw [coeff_expand, if_neg, map_zero, mul_zero]
        refine not_pow_dvd_of_multiplicity_lt ?_ ?_
        refine Nat.finiteMultiplicity_iff.mpr ⟨q_neOne ht hq, Nat.zero_lt_of_ne_zero hd₀⟩
        simp only [mem_Icc, not_and, not_le] at hx₂
        exact Nat.lt_of_succ_le (hx₂ (Nat.one_le_iff_ne_zero.mpr hx₀))
  rw [eq_aux]
  apply PowerSeries.HasSum.increase_order
  intro n

  refine .trans (.trans ?_ (PowerSeries.le_order_map _)) (PowerSeries.le_order_smul)
  rw [PowerSeries.order_expand]
  refine .trans ?_ (nsmul_le_nsmul_right (PowerSeries.one_le_order (constantCoeff_RecurFun ..)) _)
  simp
  norm_cast
  refine (Nat.lt_pow_self (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    ⟨q_neZero hq, q_neOne ht hq⟩)).le

open PowerSeries in
include ht hq hg in
lemma summable_aux [TopologicalSpace K] (hs₀ : s 0 = 0) :
    Summable (fun i ↦ s i • ((RecurFun ht hq σ s hg).expand (q ^ i) (q_pow_neZero hq)).map (σ^i)) :=
  ⟨(RecurFun ht hq σ s hg - g.map R.subtype), hasSum_aux ht hq σ s hg hs₀ ⟩

open PowerSeries in
/-- this is the function equation that `f_g` satisfies, namely
  $f_g(X) = g(X) + ∑' s_i * σ^i f(X^{q^i})$-/
theorem FunEq_of_RecurFun [TopologicalSpace K] [T2Space K] (hs₀ : s 0 = 0) :
    let f := RecurFun ht hq σ s hg
    f = g.map R.subtype + ∑' (i : ℕ), s i • (f.expand (q ^ i) (q_pow_neZero hq)).map (σ^i) := by
  intro _
  rw [HasSum.tsum_eq <| hasSum_aux ht hq σ s hg hs₀]
  ring

end FunctionalEquation

section technical_lemma

/- In this section, we usually denote $f_g(X)$ as $f(X)$ for convention. -/

open MvPowerSeries

variable {g : PowerSeries R} (hg : g.constantCoeff = 0) (hg_unit : IsUnit (g.coeff 1))

lemma image_of_incl_mem {J : Ideal R} : ∀ x, x ∈ R.subtype '' J → x ∈ R := fun x hx => by
  obtain ⟨y, hy₁, hy₂⟩ := hx
  simp only [← hy₂,Subring.subtype_apply, SetLike.coe_mem]

include hs in
/-- For all natural number `j`, for all `a ∈ R` then `σ ^ j ∈ R `-/
lemma refinement_hs: ∀ (j : ℕ), ∀ (a : R), (σ ^ j) a ∈ R := fun j => by
  induction j with
  | zero => simp
  | succ k ih =>
    intro a
    have eq_aux : (σ ^ (k + 1)) ↑a = σ ((σ^k) a) := by
      simp [Function.iterate_succ_apply']
    exact eq_aux ▸ hs ⟨_, ih _⟩

include a_congr in
lemma refinement_a_congr (l : ℕ) :  ∀ a : R, ⟨(σ ^ l) a, refinement_hs σ hs _ _⟩ ≡
    (a ^ q ^ l) [SMOD I] := by
  induction l with
  | zero =>
    simp only [pow_zero, RingHom.coe_one, id_eq, Subtype.coe_eta, pow_one]
    exact fun _ => rfl
  | succ k ih =>
    intro a
    have : (σ ^ (k + 1)) ↑a = σ ((σ ^ k) ↑a) := by
      rw [Nat.add_comm, pow_add, pow_one, RingHom.coe_mul, Function.comp_apply]
    have eq_aux : (σ ^ k) a = (⟨(σ ^ k) ↑a, refinement_hs σ hs k a⟩: R) := rfl
    simp_rw [this, pow_succ, pow_mul]
    exact .trans (a_congr (⟨(σ ^ k) ↑a, refinement_hs σ hs k a⟩ : R)) (SModEq.pow q (ih a))

include hs₁ in
lemma refinement_hs₁ : ∀ i r, ∀ b, b ∈ (I ^ (r + 1)) →
    s i * b ∈ R.subtype '' ↑(I ^ r) := by
  intro i r b hb
  rw [pow_add, pow_one, mul_comm] at hb
  refine Submodule.mul_induction_on hb ?_ ?_
  · intro m hm n hn
    rw [Subring.coe_mul, ← mul_assoc]
    obtain aux := hs₁ i ↑m (by simp [hm])
    use ⟨_, aux⟩ * n
    simpa using  Ideal.mul_mem_left (I ^ r) ⟨s i * ↑m, aux⟩ hn
  intro m n ⟨x, hx₁, hx₂⟩ ⟨y, hy₁, hy₂⟩
  refine ⟨x + y, ?_⟩
  rw [map_add, hx₂, hy₂]
  simp [mul_add, (Submodule.add_mem_iff_right (I ^ r) hx₁).mpr hy₁]

include hs₁ in
lemma refinement_hs₁' : ∀ i r, ∀ b, b ∈ R.subtype '' ↑(I ^ (r + 1)) →
    s i * b ∈ R.subtype '' ↑(I ^ r) := by
  intro i r b hb
  have b_mem_R : b ∈ R := image_of_incl_mem b hb
  -- let b' : R := ⟨b, b_mem_R⟩
  have b_mem_I_pow : ⟨b, b_mem_R⟩ ∈ I ^ (r + 1) := by
    obtain ⟨x, hx₁, hx₂⟩ := hb
    simp_rw [← hx₂]
    simpa
  obtain ⟨x, hx₁, hx₂⟩ := refinement_hs₁ s hs₁ i r _ b_mem_I_pow
  use x

include hs₂ in
/-- for all natural number `i` and `r`, for all element `b ∈ K`, then
`I ^ r * b ⊆ I` implies `I ^ r * (σ ^ i) (b) ⊆ I`. -/
lemma refinement_hs₂ : ∀ (i r : ℕ), ∀ b, (∀ a, (a ∈ R.subtype '' ↑(I^r))
    → b * a ∈ R.subtype '' I) → (∀ a, a ∈ R.subtype '' ↑(I^r)
    → ((σ ^ i) b) * a ∈ R.subtype '' I) := fun i r b h => by
  induction i with
  | zero => exact h
  | succ k hk =>
    rw [RingHom.coe_pow] at hk ⊢
    exact (Function.iterate_succ_apply' σ k b) ▸ hs₂ r _ hk

include hs₂ in
/-- for all natural number `i` and `r`, for all element `b ∈ K`, then
`I ^ r * b ⊆ I` implies `I ^ r * (σ ^ i) (b) ⊆ I`. -/
lemma hs₂_aux : ∀ (i r : ℕ), ∀ (b : K), (∀ a, (a ∈ (I^r))
    → b * a ∈ R.subtype '' I) → (∀ a, a ∈ (I^r)
    → ((σ ^ i) b) * a ∈ R.subtype '' I) := by
  intro i r b h a ha
  have h' : ∀ a, a ∈ R.subtype '' ↑(I ^ r) → b * a ∈ R.subtype '' I := by
    intro x hx
    have : ⟨x, image_of_incl_mem x hx⟩ ∈ I ^ r := by
      obtain ⟨y, hy₁, hy₂⟩ := hx
      simpa [← hy₂]
    obtain ⟨y, hy₁, hy₂⟩ := h _ this
    use y
  obtain ⟨x, hx₁, hx₂⟩ := refinement_hs₂ σ hs₂ i r b h' a (by simpa)
  use x

include hs₂ in
/-- for all natural number `i` and `r`, for all element `b ∈ K`, then
`I ^ (r + j) * b ⊆ I ^ j` implies `I ^ (r + j) * (σ ^ i) (b) ⊆ I ^ j`. -/
lemma refinement_hs₂'_aux : ∀ (i r j : ℕ), ∀ (b : K), (∀ a, a ∈ (I^r)
    → b * a ∈ R.subtype '' ↑(I)) → (∀ a, a ∈ (I^(r + j))
    → ((σ ^ i) b) * a ∈ R.subtype '' ↑(I ^ (j + 1))) := by
  intro i r j b h
  induction j with
  | zero =>
    rw [zero_add, add_zero, pow_one]
    exact hs₂_aux σ hs₂ i r b h
  | succ k ih =>
    rw [← add_assoc r k 1, pow_add, pow_one]
    intro a ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro m hm n hn
      obtain ih_aux := ih m hm
      have : (σ ^ i) b * ↑m ∈ R := image_of_incl_mem _ (ih m hm)
      have mem_aux : ⟨(σ ^ i) b * ↑m, this⟩ ∈ I ^ (k + 1) := by
        obtain ⟨x, hx₁, hx₂⟩ := ih m hm
        simp_rw [← hx₂]
        simpa
      refine ⟨⟨_, this⟩ * n, ?_, by simp [map_mul, mul_assoc]⟩
      rw [pow_add, pow_one]
      exact Ideal.mul_mem_mul mem_aux hn
    · intro x y hx hy
      obtain ⟨u, hu₁, hu₂⟩ := hx
      obtain ⟨v, hv₁, hv₂⟩ := hy
      refine ⟨u + v, Ideal.add_mem _ hu₁ hv₁ , by simp [map_add, hv₂,  hu₂, mul_add]⟩

include hs₂ in
/-- for all natural number `i` and `r`, for all element `b ∈ K`, then
`I ^ (r + j) * b ⊆ I ^ j` implies `I ^ (r + j) * (σ ^ i) (b) ⊆ I ^ j`. -/
lemma refinement_hs₂' : ∀ (i r j : ℕ), ∀ b, (∀ a, (a ∈ R.subtype '' ↑(I^r))
    → b * a ∈ R.subtype '' ↑(I)) → (∀ a, a ∈ R.subtype '' ↑(I^(r + j))
    → ((σ ^ i) b) * a ∈ R.subtype '' ↑(I^(j + 1))) := by
  intro i r j b h a ha
  have a_mem : ⟨a, image_of_incl_mem a ha⟩ ∈ I ^ (r + j) := by
    obtain ⟨x, hx₁, hx₂⟩ := ha
    simp_rw [← hx₂]
    simpa
  have h' : ∀ a, a ∈ I ^ r → b * a ∈ R.subtype '' I := by
    intro x hx
    have : (x : K) ∈ R.subtype '' ↑(I ^ r) := ⟨x, by simpa⟩
    obtain ⟨y, hy₁, hy₂⟩ := h _ this
    use y
  obtain ⟨x, hx₁, hx₂⟩ := refinement_hs₂'_aux σ hs₂ i r j b h' ⟨a, image_of_incl_mem a ha⟩ a_mem
  use x

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

lemma ideal_pow_mem' {I : Ideal R} {r s: ℕ} {x : K} (hs : r < s) : (∀ b ∈ I^r, x * b ∈ R)
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
    simp [← hx₂, ← hy₂, (Submodule.add_mem_iff_right (I ^ i) hx₁).mpr hy₁]

include hs in
lemma refine_hs : ∀ (j : ℕ), ∀ (a : R), (σ ^ j) a ∈ R := fun j => by
  induction j with
  | zero =>
    simp
  | succ k ih =>
    intro a
    rw [RingHom.coe_pow, Function.iterate_succ_apply']
    exact hs ⟨_, ih _⟩

include hs in
lemma coeff_aux_mem {G : MvPowerSeries τ R} : ∀ (j : ℕ), ∀ (n : τ →₀ ℕ),
  (G.map ((σ ^ j).comp R.subtype)).coeff n ∈ R := fun j n => refine_hs σ hs j (G n)

include ht hq hp_mem in
lemma congr_pow_mod_add {r i : ℕ} {F G : MvPowerSeries τ R} (hr : 1 ≤ r)
    (h_congr : F ≡ G [SMOD (I^r).MvPowerSeries]) :
    F ^ q ^ i ≡ G ^ q ^ i [SMOD (I ^ (r + i)).MvPowerSeries] := by
  induction i with
  | zero => simpa
  | succ k ih =>
    let H := F ^ q ^ k - G ^ q ^ k
    have eq_aux : F ^ q ^ k = G ^ q ^ k + H := by simp [H]
    have coeff_H_mem : ∀ n, H.coeff n ∈ I ^ (r + k) := SModEq.sub_mem.mp ih
    refine SModEq.sub_mem.mpr ?_
    intro n
    obtain ⟨x, hx⟩ := exists_add_pow_prime_pow_eq hp.out (G ^ q ^ k) H t
    rw [← hq] at hx
    have {a b c : MvPowerSeries τ R} : a + b + c - a = b + c := by ring
    rw [pow_add q, pow_one, pow_mul, eq_aux, hx, pow_mul, this]
    refine Submodule.add_mem _ ?_ ?_
    · have two_le_q : 2 ≤ q := IsPrimePow.two_le (isPrimePow_q ht hq)
      have : H ^ q = H ^ 2 * H ^ (q - 2) := by
        rw [← pow_add]
        congr; omega
      rw [this]
      have mem_aux : H ^ 2 ∈ (I ^ (r + (k + 1))).MvPowerSeries := by
        rw [pow_two, pow_add]
        refine MvPowerSeries.mul_mem_mul _
          (fun n => Ideal.pow_le_pow_right (by linarith) (coeff_H_mem _))
          (fun n => Ideal.pow_le_pow_right (by linarith) (coeff_H_mem _))
      exact Ideal.IsTwoSided.mul_mem_of_left _ mem_aux _
    · have eq_aux₁ : (p : MvPowerSeries τ R) * G ^ q ^ k * H * x =
        (p * H) * (G ^ q ^ k * x) := by ring
      have mem_aux : (p * H) * (G ^ q ^ k * x) ∈ (I ^ (r + (k + 1))).MvPowerSeries := by
        have : (p * H) ∈ (I ^ (r + (k + 1))).MvPowerSeries := by
          have : I ^ (r + (k + 1)) = I * I ^ (r + k) := by ring
          rw [this]
          refine MvPowerSeries.mul_mem_mul _ ?_ coeff_H_mem
          simp only [Ideal.MvPowerSeries, Submodule.mem_mk, AddSubmonoid.mem_mk,
            AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
          intro n
          have : coeff n (p : MvPowerSeries τ R) = coeff n (C (p : R)) := rfl
          rw [this, coeff_C]
          by_cases hn : n = 0
          · simp [if_pos hn, hp_mem]
          · simp [if_neg hn]
        exact Ideal.IsTwoSided.mul_mem_of_left _ this
      rw [eq_aux₁]
      exact mem_aux n

include ht hq hp_mem in
lemma congr_pow_mod_add' {r : ℕ} (n : ℕ) {F G : MvPowerSeries τ R} (hr : 1 ≤ r)
    (h_congr : F ≡ G [SMOD (I^r).MvPowerSeries]) :
    F ^ n ≡ G ^ n [SMOD (I ^ (r + multiplicity q n)).MvPowerSeries] := by
  by_cases hn₀ : n = 0
  · simp [hn₀]
    rfl
  have dvd_aux : q ^  multiplicity q n ∣ n := pow_multiplicity_dvd q n
  obtain ⟨l, hl⟩ := dvd_aux
  nth_rw 2 3 [hl]
  rw [pow_mul, pow_mul]
  exact SModEq.pow l (congr_pow_mod_add ht hq hp_mem hr h_congr)

include hp a_congr hp_mem in
lemma p_pow_mod_p [Finite τ] {G : MvPowerSeries τ R} {l : ℕ} :
    G ^ (q ^ l) ≡ ((G.expand (q ^ l) (q_pow_neZero hq)).map ((σ^l).comp R.subtype)).toSubring _
    (coeff_aux_mem σ hs l) [SMOD I.MvPowerSeries] := by
  by_cases hI : I = ⊤
  · rw [hI]
    exact SModEq.sub_mem.mpr fun n => Submodule.mem_top
  apply SModEq.sub_mem.mpr
  simp [Ideal.MvPowerSeries]
  intro n
  simp_rw [hq, ← pow_mul]
  have pneq : p ≠ 0 := (NeZero.ne' p).symm
  let φ := Ideal.Quotient.mk I
  haveI : ExpChar (R ⧸ I) p := Rchar_p hI hp_mem
  obtain eq_aux₁ := map_iterateFrobenius_expand p pneq (G.map φ) (t * l)
  have eq_zero : coeff n ((MvPowerSeries.map φ) G ^ p ^ (t * l)) - coeff n ((MvPowerSeries.map
    (iterateFrobenius (↥R ⧸ I) p (t * l))) ((expand (p ^ (t * l)) (pow_ne_zero _ pneq))
    ((MvPowerSeries.map φ) G))) = 0 := by
    simp [eq_aux₁]
  have eq_σ_pow (a : R) : (iterateFrobenius (↥R ⧸ I) p (t * l)) (φ a) =
    φ (⟨(σ ^ l) a, refine_hs σ hs _ _ ⟩ ) := by
    simp only [iterateFrobenius, RingHom.coe_mk, powMonoidHom_apply]
    rw [pow_mul, ← hq]
    obtain h1 := SModEq.sub_mem.mp <| refinement_a_congr σ hs a_congr l a
    have aux : φ (⟨(σ ^ l) ↑a, refinement_hs σ hs _ _ ⟩ - a ^ q ^ l) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h1
    conv_lhs => rw [← add_zero (φ a ^ q ^ l), ← aux, map_sub, map_pow]
    ring_nf
  have eq_aux₂ : coeff n ((MvPowerSeries.map
    (iterateFrobenius (↥R ⧸ I) p (t * l))) ((expand (p ^ (t * l)) (pow_ne_zero _ pneq))
    ((MvPowerSeries.map φ) G))) = φ (coeff n (((G.expand (q ^ l) (q_pow_neZero hq)).map ((σ^l).comp R.subtype)).toSubring _
    (coeff_aux_mem σ hs l))) := by
    rw [coeff_map, ← map_expand, coeff_map, eq_σ_pow]
    congr
    simp_rw [coeff_map, pow_mul, ← hq]
    rfl
  rw [eq_aux₂, ← map_pow, coeff_map, ← map_sub] at eq_zero
  exact (Submodule.Quotient.mk_eq_zero I).mp eq_zero

include ht hq hs hp_mem a_congr in
/-- Forall `r m ∈ ℕ` and `G(X,Y) ∈ R⟦X,Y⟧`, we have that
  $G^{q^r m q^l} ≡ (σ^l G(X^{q^l},Y^{q^l}))^n$. -/
theorem pow_ModEq_aux
    (G : MvPowerSeries τ R) [Finite τ] {n r m : ℕ} (l : ℕ) (hn : n = q ^ r * m) :
    (((G.expand (q ^ l) (q_pow_neZero hq))^n).map ((σ ^ l).comp R.subtype)).toSubring _
      (coeff_aux_mem σ hs l)  ≡
    (G ^ (q ^ l * n)) [SMOD (I^(r + 1)).MvPowerSeries] := by
  by_cases hn₀ : n = 0
  · congr
    rw [hn₀, pow_zero, mul_zero]
    simp [npowRec, ← coeff_apply, coeff_one]
    ext d
    rw [coeff_one, coeff_apply]
    aesop
  obtain h1 := p_pow_mod_p hq σ hs a_congr hp_mem (G := G) (l := l)
  rw [← pow_one I] at h1
  obtain h₂ := congr_pow_mod_add' ht hq hp_mem n (le_refl _) h1
  have le_aux : r + 1 ≤ 1 + multiplicity q n := by
    have : r ≤ multiplicity q n :=
      FiniteMultiplicity.le_multiplicity_of_pow_dvd (Nat.finiteMultiplicity_iff.mpr
        ⟨q_neOne ht hq, n.zero_lt_of_ne_zero hn₀⟩) (hn ▸ Nat.dvd_mul_right _ _)
    linarith
  have {a b : MvPowerSeries τ R} {x y} (h : y ≤ x) :
    a ≡ b [SMOD (I ^ x).MvPowerSeries] → a ≡ b [SMOD (I^y).MvPowerSeries] := by
    intro h'
    refine SModEq.sub_mem.mpr fun n => Ideal.pow_le_pow_right h (SModEq.sub_mem.mp h' n)
  obtain aux := this le_aux h₂
  rw [pow_mul]
  refine (SModEq.trans aux ?_).symm
  congr
  ext d
  simp [coeff_pow]

include ht hq a_congr hp_mem hs in
/- this is more general version for second technical lemma. -/
/- Second Technical lemma: Forall `n, l ∈ ℕ` and `G(X,Y) ∈ R⟦X,Y⟧`  with assumption that $n=q^r m$,
we have that $G^{q^r m q^l} ≡ (σ^l G(X^{q^l},Y^{q^l}))^n$. -/
theorem pow_ModEq (G : MvPowerSeries τ R) [Finite τ] {n r m : ℕ} (l : ℕ) (hn : n = q ^ r * m) :
    ∀ d, ((((G.map (R.subtype)).expand (q ^ l) (q_pow_neZero hq))^n).map (σ^l) -
      (G ^ (q ^ l * n)).map (R.subtype)).coeff d ∈ R.subtype '' ↑(I^(r + 1)) := by
  obtain h₁ := pow_ModEq_aux ht hq σ hs a_congr hp_mem G l hn
  intro d
  obtain h₂ := SModEq.sub_mem.mp h₁ d
  use ((((MvPowerSeries.map ((σ ^ l).comp R.subtype))
    ((expand (q ^ l) (q_pow_neZero hq)) G ^ n)).toSubring R (coeff_aux_mem σ hs l) -
    G ^ (q ^ l * n)).coeff d)
  exact ⟨h₂, by simp [← map_pow, coeff_map]⟩

end technical_lemma

section inv_add_RecurFun

open MvPowerSeries

variable {g : PowerSeries R} (hg : g.constantCoeff = 0) (hg_unit : IsUnit (g.coeff 1))

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

/-- f⁻¹ (f (X)) = X. -/
lemma RecurFun_comp_inv_RecurFun :
    let f := RecurFun ht hq σ s hg
    let f_inv := inv_RecurFun ht hq σ s hg hg_unit
    f.subst f_inv = PowerSeries.X :=
  PowerSeries.subst_inv_eq _ (coeff_RecurFun_unit ht hq σ s hg hg_unit)
    (constantCoeff_RecurFun ..)

/-- f⁻¹ (f (X)) = X. -/
lemma inv_RecurFun_comp_RecurFun :
    let f := RecurFun ht hq σ s hg
    let f_inv := inv_RecurFun ht hq σ s hg hg_unit
    f_inv.subst f = PowerSeries.X := by
  refine PowerSeries.exist_subst_inv_aux _ ?_ (constantCoeff_inv_RecurFun ..) (RecurFun_comp_inv_RecurFun ..)
  simp [inv_RecurFun, PowerSeries.subst_inv, PowerSeries.invFun_aux]

/-- `inv_add_aux` define to be `f_g⁻¹(f_g(X) + f_g(Y))`, and we will prove this to be
a formal group law over coefficient ring `R`. Now we denote `F(X,Y) = f_g⁻¹(f_g(X) + f_g(Y))`
and `f (X) = f_g (X)` for convention. -/
def inv_add_RecurFun :=
    (inv_RecurFun ht hq σ s hg hg_unit).subst ((RecurFun ht hq σ s hg).toMvPowerSeries
      (0 : Fin 2) + (RecurFun ht hq σ s hg).toMvPowerSeries 1)

/-- constant coefficient of $f_g(X)+f_g(Y)$ is zero-/
lemma constantCoeff_add_RecurFun : constantCoeff ((RecurFun ht hq σ s hg).toMvPowerSeries
    (0 : Fin 2) + (RecurFun ht hq σ s hg).toMvPowerSeries 1) = 0 := by
  rw [RingHom.map_add, PowerSeries.toMvPowerSeries_apply,  PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun ..,
    PowerSeries.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun .., add_zero]

lemma coeff_X_inv_add_RecurFun :
    (inv_add_RecurFun ht hq σ s hg hg_unit).coeff (Finsupp.single 0 1) = 1 := by
  rw [inv_add_RecurFun, PowerSeries.coeff_subst <| PowerSeries.HasSubst.of_constantCoeff_zero
    <| constantCoeff_add_RecurFun .., finsum_eq_single _ 1]
  simp
  rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.coeff_subst_X_s,
    PowerSeries.toMvPowerSeries_apply, PowerSeries.coeff_subst_X_s' (one_ne_zero)]
  have eq_aux : ↑↑hg_unit.unit⁻¹ * (((PowerSeries.coeff 1) g : R) : K) = 1 := by
    exact_mod_cast IsUnit.val_inv_mul hg_unit
  simp [coeff_one_inv_RecurFun, coeff_one_RecurFun, eq_aux]
  intro x hx
  by_cases hx₀ : x = 0
  · simp [hx₀, constantCoeff_inv_RecurFun]
  rw [coeff_pow, Finset.sum_eq_zero _, smul_zero]
  intro d hd

  simp only [Fin.isValue, mem_finsuppAntidiag] at hd
  have exist_aux : ∃ i ∈ range x, d i = 0 := by
    have xge : x ≥ 2 := by omega
    by_contra hc
    simp only [not_exists, not_and] at hc
    have aux : ∀ x_1 ∈ range x, (d x_1).degree ≥ 1 := by
      intro t ht
      by_contra hc'
      exact hc t ht <| (Finsupp.degree_eq_zero_iff _).mp <| Nat.eq_zero_of_not_pos hc'
    have eq_aux : ((range x).sum ⇑d).degree = (Finsupp.single (0 : Fin 2) 1).degree := by
      rw [hd.1]
    simp only [map_sum, Fin.isValue, Finsupp.degree_single] at eq_aux
    have contra : 2 ≤ ∑ x ∈ range x, Finsupp.degree (d x) :=
      .trans (by simp [xge]) (sum_le_sum fun i hi =>  aux i hi)
    linarith
  obtain ⟨i, hi, hi'⟩ := exist_aux
  refine Finset.prod_eq_zero hi ?_
  simp [hi', PowerSeries.toMvPowerSeries_apply]
  rw [PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun ..,
    PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun .., add_zero]

lemma coeff_Y_inv_add_RecurFun :
    (coeff (Finsupp.single 1 1)) (inv_add_RecurFun ht hq σ s hg hg_unit) = 1 := by
  /- the proof of this should be similar as above `coeff_inv_add_aux_X`-/
  rw [inv_add_RecurFun, PowerSeries.coeff_subst <| PowerSeries.HasSubst.of_constantCoeff_zero
    <| constantCoeff_add_RecurFun .., finsum_eq_single _ 1]
  simp [PowerSeries.toMvPowerSeries_apply]
  rw [PowerSeries.coeff_subst_X_s, PowerSeries.coeff_subst_X_s' (one_ne_zero).symm]
  have eq_aux : ↑↑hg_unit.unit⁻¹ * (((PowerSeries.coeff 1) g : R) : K) = 1 := by
    exact_mod_cast IsUnit.val_inv_mul hg_unit
  simp [coeff_one_inv_RecurFun, coeff_one_RecurFun, eq_aux]
  intro x hx
  by_cases hx₀ : x = 0
  · simp [hx₀, constantCoeff_inv_RecurFun]
  rw [coeff_pow, Finset.sum_eq_zero _, smul_zero]
  intro d hd
  simp only [Fin.isValue, mem_finsuppAntidiag] at hd
  have exist_aux : ∃ i ∈ range x, d i = 0 := by
    have xge : x ≥ 2 := by omega
    by_contra hc
    simp only [not_exists, not_and] at hc
    have aux : ∀ x_1 ∈ range x, (d x_1).degree ≥ 1 := by
      intro t ht
      by_contra hc'
      exact hc t ht <| (Finsupp.degree_eq_zero_iff _).mp <| Nat.eq_zero_of_not_pos hc'
    have eq_aux : ((range x).sum ⇑d).degree = (Finsupp.single (1 : Fin 2) 1).degree := by
      rw [hd.1]
    simp only [map_sum, Fin.isValue, Finsupp.degree_single] at eq_aux
    have contra : 2 ≤ ∑ x ∈ range x, Finsupp.degree (d x) :=
      .trans (by simp [xge]) (sum_le_sum fun i hi =>  aux i hi)
    linarith
  obtain ⟨i, hi, hi'⟩ := exist_aux
  refine Finset.prod_eq_zero hi ?_
  simp [hi', PowerSeries.toMvPowerSeries_apply]
  rw [PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun ..,
    PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun .., add_zero]

open PowerSeries HasSubst in
/-- `f(F(X,Y)) = f (X) + f(Y)`-/
lemma f_F_eq_f_add :
    (RecurFun ht hq σ s hg).subst (inv_add_RecurFun ht hq σ s hg hg_unit) =
    (RecurFun ht hq σ s hg).subst X₀ + (RecurFun ht hq σ s hg).subst X₁ := by
  rw [inv_add_RecurFun, ← subst_comp_subst_apply (of_constantCoeff_zero' rfl)
    <| of_constantCoeff_zero <| constantCoeff_add_RecurFun .., inv_RecurFun,
    subst_inv_eq, subst_X <| .of_constantCoeff_zero <| constantCoeff_add_RecurFun ..,
    PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply]

open PowerSeries in
/- constant coefficient of `F` is zero. -/
lemma constantCoeff_inv_add_RecurFun :
    constantCoeff (inv_add_RecurFun ht hq σ s hg hg_unit) = 0 := by
  rw [inv_add_RecurFun, constantCoeff_subst <| .of_constantCoeff_zero
    <| constantCoeff_add_RecurFun .., finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd, inv_RecurFun, PowerSeries.subst_inv]
    rfl
  simp [constantCoeff_add_RecurFun, zero_pow hd]

open PowerSeries in
lemma HasSubst.inv_add_RecurFun : HasSubst (inv_add_RecurFun ht hq σ s hg hg_unit) :=
  .of_constantCoeff_zero <| constantCoeff_inv_add_RecurFun ..

section PartI

open AddMonoidHom PowerSeries in
/- for any natural number `i`, we have `σⁱ_* f( σⁱ_* F(X, Y)) = σⁱ_* f(X) + σⁱ_* f(Y)`. -/
lemma sigma_map_distrib (i : ℕ) :
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    (f.map (σ ^ i)).subst (F.map (σ ^ i)) =
    ((f.subst X₀).map (σ ^ i)) + ((f.subst X₁).map (σ ^ i)) := by
  refine .trans ?_ ((f_F_eq_f_add ht hq σ s hg hg_unit) ▸ (map_add _ _ _))
  ext n
  rw [MvPowerSeries.coeff_map, coeff_subst <| .of_constantCoeff_zero
    (by simp [constantCoeff_inv_add_RecurFun]), coeff_subst <| HasSubst.inv_add_RecurFun ..,
    (σ ^ i).eq_toAddMonoidHom, AddMonoidHom.map_finsum _ <| coeff_subst_finite
    (HasSubst.inv_add_RecurFun ..) _ _, finsum_congr (fun d => _)]
  simp [smul_eq_mul, PowerSeries.coeff_map, map_mul, MvPowerSeries.coeff_pow]

lemma constantCoeff_frobnius_F_zero (i : ℕ):
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    constantCoeff (subst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i] F) = 0 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  rw [constantCoeff_subst_zero] <;> simp [zero_pow <| q_pow_neZero hq,
    constantCoeff_inv_add_RecurFun]

/-- $σ^i f (F(X^{q^i}, Y^{q^i})) = ∑'(n ∈ ℕ), σ^i (a_n) * F(X^{q^i}, Y^{q^i})^n. $-/
lemma decomp_f (i : ℕ) [UniformSpace K] [T2Space K] [DiscreteUniformity K] :
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    ∑' (n : ℕ), ((f.map (σ ^ i)).coeff n) •
    ((F.expand (q^i) (q_pow_neZero hq)).map (σ ^ i)) ^ n =
    (f.map (σ ^ i)).subst ((F.map (σ ^ i)).expand (q^i) (q_pow_neZero hq)) := by
  /- this lemma need to use tsum_subst. -/
  let f := (RecurFun ht hq σ s hg)
  let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  simp_rw [←f_def, ←F_def]
  nth_rw 2 [(f.map (σ^i)).as_tsum]
  have has_subst₁ (b : ℕ) : PowerSeries.HasSubst ((F.map (σ ^ b)).expand (q ^ b)
      (q_pow_neZero hq)) := PowerSeries.HasSubst.of_constantCoeff_zero <| by
    rw [constantCoeff_expand, MvPowerSeries.constantCoeff_map,
      constantCoeff_inv_add_RecurFun, map_zero]
  rw [tsum_subst ⟨f.map (σ ^ i), (f.map (σ ^ i)).hasSum_of_monomials_self⟩ (has_subst₁ _),
    tsum_congr]
  intro n
  ext d
  simp_rw [PowerSeries.monomial_eq_C_mul_X_pow, ← PowerSeries.smul_eq_C_mul,
    PowerSeries.subst_smul (has_subst₁ _), PowerSeries.subst_pow (has_subst₁ _),
    PowerSeries.subst_X (has_subst₁ _), map_expand]

theorem Fun_eq_of_RecurFun_XY [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) {x : Fin 2} :
    let f := (RecurFun ht hq σ s hg)
    f.subst (X x) = g.subst (X x) + ∑' (i : ℕ), (s i • ((f.subst ((X x) ^ q ^ i)).map (σ ^ i)))
    := by
  /- this should be easy using the theorem tsum_subst-/
  intro f
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  obtain has_subst_aux := PowerSeries.HasSubst.X (x : Fin 2) (S := K)
  nth_rw 1 [f_def, FunEq_of_RecurFun ht hq σ s hg hs0]
  rw [PowerSeries.subst_add has_subst_aux, tsum_subst (summable_aux ht hq σ s hg hs0) has_subst_aux]
  congr! 1
  · ext n
    rw [g.coeff_subst has_subst_aux, (g.map R.subtype).coeff_subst has_subst_aux,
      finsum_congr (fun d => rfl)]
    rfl
  · apply tsum_congr <| fun i => by
      rw [PowerSeries.subst_smul has_subst_aux, ←f_def]
      nth_rw 1 [← map_X (σ ^ i) x]
      erw [← PowerSeries.map_subst has_subst_aux]
      congr! 2
      rw [PowerSeries.expand_apply, PowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.X_pow (q_pow_neZero hq)) has_subst_aux, PowerSeries.subst_congr]
      funext d
      rw [PowerSeries.subst_pow has_subst_aux,
        PowerSeries.subst_X has_subst_aux]

include ht hq hg in
lemma summable_X_x  [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0) (x : τ):
    let f := (RecurFun ht hq σ s hg)
    Summable (fun i ↦ (s i • ((PowerSeries.subst ((X x) ^ q ^ i) f).map (σ ^ i)))) := by
  intro f
  have eq_aux : ∀ i, s i • (MvPowerSeries.map (σ ^ i)) (PowerSeries.subst ((X x) ^ q ^ i) f)
      =  PowerSeries.subst (X x) (s i • ((RecurFun ht hq σ s hg).expand (q ^ i) (
      q_pow_neZero hq)).map (σ^i)) := fun i => by
    rw [PowerSeries.subst_smul (PowerSeries.HasSubst.X x), PowerSeries.map_subst
      (PowerSeries.HasSubst.pow (PowerSeries.HasSubst.X x) (one_le_q_pow hq)), PowerSeries.map_expand, PowerSeries.expand_apply,
          PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow (q_pow_neZero hq))
          (PowerSeries.HasSubst.X x)]
    congr! 2
    simp [PowerSeries.subst_pow (PowerSeries.HasSubst.of_constantCoeff_zero _),
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero _)]
  simp_rw [eq_aux]
  exact Summable.summable_of_subst (summable_aux ht hq σ s hg hs0) (PowerSeries.HasSubst.X x)

open AddMonoidHom in
/-- this auxiliary lemma shows that $∑ s_i ∑ σ^i_*(a_n)(σ^i_*F(X^{q^i}, Y^{q^i}))^n =
  f(X) + f(Y) - g(X) - g(Y)$. ref: 2.4.12 in Page 14. -/
lemma tsum_eq_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0):
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    ∑' i : ℕ, (s i) • ∑' n : ℕ, ((σ ^ i) (f.coeff n)) •
    ((F.expand (q^i) (q_pow_neZero hq)).map (σ^i)) ^ n
    = f.subst X₀ + f.subst X₁ - g.subst X₀ - g.subst X₁ := by
  let f := (RecurFun ht hq σ s hg)
  let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  calc
    _ = ∑' i : ℕ, (s i) • (f.map (σ^i)).subst ((F.map (σ^i)).expand (q^i) (q_pow_neZero hq))
      := by
      apply tsum_congr <| fun i => by
        congr
        simp_rw [← PowerSeries.coeff_map]
        exact decomp_f ..
    _ = ∑' i : ℕ, (s i) • ((f.subst X₀).map (σ^i) + (f.subst X₁).map (σ^i)).expand (q^i)
      (q_pow_neZero hq) := by
      apply tsum_congr <| fun i => by
        congr
        rw [←sigma_map_distrib ht hq σ s hg hg_unit i, ←F_def, ←f_def]
        have eq_aux :((f.map (σ ^ i)).subst (F.map (σ ^ i))).expand (q^i) (q_pow_neZero hq) =
          (f.map (σ ^ i)).subst ((F.expand (q^i) (q_pow_neZero hq)).map (σ ^ i)) := by
          simp only [map_expand]
          rw [PowerSeries.subst, expand_subst]
          rfl
          refine PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero ?_)
          rw [constantCoeff_map, constantCoeff_inv_add_RecurFun, map_zero]
        ext n
        rw [eq_aux, PowerSeries.coeff_subst, PowerSeries.coeff_subst, finsum_congr]
        intro d
        rw [map_expand]
        · refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
          rw [constantCoeff_map, constantCoeff_expand, constantCoeff_inv_add_RecurFun, map_zero]
        · refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
          rw [constantCoeff_expand, constantCoeff_map, constantCoeff_inv_add_RecurFun, map_zero]
    _ = ∑' i, (s i • ((f.subst (X₀ ^ (q ^ i))).map (σ ^ i) +
      (f.subst (X₁ ^ (q ^ i))).map (σ ^ i))) := tsum_congr <| fun i => by
        simp [map_add, expand]
        have (x : Fin 2): subst (fun s ↦ X s ^ q ^ i) (((f.subst (X x)).map (σ ^ i))) =
          ((f.subst ((X x) ^ q ^ i)).map (σ ^ i)) := by
          rw [PowerSeries.map_subst (PowerSeries.HasSubst.X _), PowerSeries.map_subst,
            PowerSeries.subst, subst_comp_subst_apply _ (HasSubst.X_pow (q_pow_neZero hq))]
          apply subst_congr
          funext s
          simp only [map_X, map_pow]
          rw [subst_X (HasSubst.X_pow (q_pow_neZero hq))]
          · simpa using PowerSeries.HasSubst.const (PowerSeries.HasSubst.X _)
          · refine PowerSeries.HasSubst.pow (PowerSeries.HasSubst.X _) (one_le_q_pow hq)
        rw [this 0, this 1]
    _ = _ := by
      simp_rw [smul_add, Fun_eq_of_RecurFun_XY ht hq σ s hg hs0]
      rw [Summable.tsum_add (summable_X_x ht hq σ s hg hs0 0) (summable_X_x ht hq σ s hg hs0 1)]
      ring

lemma mem_ideal_aux {m : ℕ} {α : ℕ → K} (h : ∀ i ∈ range m, α i ∈ ⇑(algebraMap (↥R) K) '' ↑I) :
    ∑ i ∈ range m, α i ∈ ⇑(algebraMap (↥R) K) '' ↑I := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [range_add_one, sum_insert (by simp)]
    specialize ih fun i hi => h i (mem_range.mpr (by nlinarith [mem_range.mp hi]))
    specialize h k (self_mem_range_succ k)
    simp at h ⊢ ih
    obtain ⟨a, ha₀, ha₁, ha₂⟩ := ih
    obtain ⟨b, hb₀, hb₁, hb₂⟩ := h
    have : (⟨a + b, Subring.add_mem R ha₀ hb₀⟩ : R) = ⟨a, ha₀⟩ + ⟨b, hb₀⟩ := rfl
    use (a + b), Subring.add_mem R ha₀ hb₀, ((Submodule.add_mem_iff_right I ha₁).mpr hb₁)
    rw [←hb₂, ←ha₂, this, map_add]
    ring_nf

lemma le_order₁ {b : ℕ} : b ≤ (PowerSeries.subst (inv_add_RecurFun ht hq σ s hg hg_unit)
    (PowerSeries.C (s b) * (PowerSeries.map (σ ^ b)) ((RecurFun ht hq σ s hg).expand (q ^ b)
      (q_pow_neZero hq)))).order := by
  have aux : (b : ENat) ≤ q ^ b := by
    exact_mod_cast (Nat.lt_pow_self (IsPrimePow.one_lt (isPrimePow_q ht hq))).le
  refine (.trans aux ?_)
  have le_aux₁ : q ^ b ≤ ((RecurFun ht hq σ s hg).expand (q ^ b) (q_pow_neZero hq)).order := by
    simp only [PowerSeries.order_expand, nsmul_eq_mul, Nat.cast_pow]
    exact le_mul_of_one_le_right' <| PowerSeries.one_le_order (constantCoeff_RecurFun ..)
  refine .trans (ENat.self_le_mul_left _ (zero_ne_one' _).symm) <|
    .trans (mul_le_mul (ENat.one_le_iff_ne_zero.mpr <| order_ne_zero_iff_constCoeff_eq_zero.mpr
      (constantCoeff_inv_add_RecurFun ..)) ?_ (zero_le _) (zero_le _))
        (PowerSeries.le_order_subst _ (HasSubst.inv_add_RecurFun ..) _)
  rw [← PowerSeries.smul_eq_C_mul]
  exact .trans le_aux₁ (.trans (PowerSeries.le_order_map _) (PowerSeries.le_order_smul))

lemma tsum_to_finite₂ {n : Fin 2 →₀ ℕ} [UniformSpace K] [T2Space K]
    [DiscreteUniformity K] :
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    ∑' (i : ℕ), (coeff n) (PowerSeries.subst F (PowerSeries.C (s i)
    * (PowerSeries.map (σ ^ i)) (f.expand (q ^ i) (q_pow_neZero hq)))) =
    ∑ i ∈ range (n.degree + 1), (coeff n) (PowerSeries.subst F (PowerSeries.C (s i) *
    (PowerSeries.map (σ ^ i)) (f.expand (q ^ i) (q_pow_neZero hq)))) := by
  refine tsum_eq_sum ?_
  intro b hb
  simp at hb
  exact coeff_of_lt_order <| (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp
    (.trans (by norm_cast) (le_order₁ ..))

include ht in
lemma coeff_coe_aux {F : MvPowerSeries (Fin 2) K} {F' : MvPowerSeries (Fin 2) R}
    {n : Fin 2 →₀ ℕ} {i b k : ℕ} (h : n.degree = k) (hi₀ : i ≠ 0)
    (h_ind : ∀ d, d.degree < k → MvPowerSeries.coeff d F' = F.coeff d)
    (hF' : F'.constantCoeff = 0) (hF : F.constantCoeff = 0):
    ((expand (q ^ i) (q_pow_neZero hq)) (F.map (σ ^ i)) ^ b).coeff n =
    ((expand (q ^ i) (q_pow_neZero hq)) ((F'.map R.subtype).map (σ ^ i)) ^ b).coeff n := by
  rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow, Finset.sum_congr rfl]
  intro l hl
  simp only [mem_finsuppAntidiag] at hl
  rw [Finset.prod_congr rfl]
  intro x hx
  by_cases! h_dvd : ∀ (a : Fin 2), q ^ i ∣ l x a
  · by_cases lx_zero : l x = 0
    · simp [lx_zero, constantCoeff_expand, hF, hF']
    obtain ⟨m, hm⟩ : ∃ m, (l x) = (q ^ i) • m :=
      ⟨Finsupp.equivFunOnFinite.symm fun a => (l x) a / (q ^ i),
      by ext a; simp [(Nat.mul_div_cancel' (h_dvd a))]⟩
    have : m.degree < k := by
      have le_aux : (l x).degree ≤ n.degree := by
        rw [← hl.1]
        simp
        have : ∀ j ∈ range b, 0 ≤ (l j).degree := by simp
        exact Finset.single_le_sum this hx
      have lt_aux : m.degree < Finsupp.degree (l x) := by
        simp [hm]
        obtain h := two_le_q_pow ht hq hi₀
        refine lt_mul_left ?_ (two_le_q_pow ht hq hi₀)
        have neq : m.degree ≠ 0 := by
          by_contra! hc
          obtain this := (Finsupp.degree_eq_zero_iff _).mp hc
          rw [this, smul_zero] at hm
          exact lx_zero hm
        exact Nat.zero_lt_of_ne_zero neq
      linarith
    simp [hm, coeff_expand_smul, coeff_expand_smul, coeff_map, coeff_map, h_ind _ this]
  · obtain ⟨a, ha⟩ := h_dvd
    rw [coeff_expand_of_not_dvd _ _ _ ha, coeff_expand_of_not_dvd _ _ _ ha]

open PowerSeries in
include hs hp_mem a_congr hs₁ hs₂ in
/-- f(F(X,Y)) ≡ g(F(X,Y)) + f(X) + f(Y) - g(X) - g(Y) [MOD R]-/
lemma RModEq_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) {n : Fin 2 →₀ ℕ} {k : ℕ} (h : n.degree = k) :
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    (h_ind : ∀ m < k, ∀ (n : Fin 2 →₀ ℕ), n.degree = m → F.coeff n ∈ R) →
      (g.subst F + f.subst X₀ + f.subst X₁ - g.subst X₀ - g.subst X₁ - f.subst F).coeff n ∈ R  := by
  /- this need to use the equation we prove above. -/
  intro f F h_ind
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  have has_subst_F : PowerSeries.HasSubst F := HasSubst.inv_add_RecurFun ht hq σ s hg hg_unit
  have has_subst_monomial (i : ℕ) := PowerSeries.HasSubst.monomial'
    (q_pow_neZero hq (x := i)) (1 : K)
  have le_q_pow {i : ℕ} : 1 ≤ q ^ i := Nat.one_le_pow i q (by positivity [q_neZero hq])
  by_cases hn₀ : n = 0
  · /- all these terms are equal to zero. -/
    simp [hn₀]
    have coeff_zero₁: constantCoeff (g.subst F) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_inv_add_RecurFun ..) _ hg
    have coeff_zero_XY {x : Fin 2} : (f.subst (X x (R := K))).constantCoeff = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X x) _ (constantCoeff_RecurFun ..)
    have coeff_zero_XY' {x : Fin 2} : (g.subst (X x (R := K))).constantCoeff = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X x) _ hg
    have coeff_zero₂ : (f.subst F).constantCoeff = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_inv_add_RecurFun ..) _ (constantCoeff_RecurFun ..)
    simp [coeff_zero₁, coeff_zero_XY, coeff_zero_XY', coeff_zero₂]
  have has_subst₁ (b : ℕ) : PowerSeries.HasSubst ((F.map (σ ^ b)).expand (q ^ b)
      (q_pow_neZero hq)) := HasSubst.of_constantCoeff_zero <| by
    rw [MvPowerSeries.constantCoeff_expand, MvPowerSeries.constantCoeff_map,
      constantCoeff_inv_add_RecurFun, map_zero]
  have tsum_eq_subst {b : ℕ} : (∑' (n : ℕ), (σ ^ b) ((PowerSeries.coeff n) f) •
    (MvPowerSeries.map (σ ^ b)) (F.expand (q ^ b) (q_pow_neZero hq)) ^ n) =
      (f.map (σ ^ b)).subst ((F.map (σ ^ b)).expand (q ^ b) (q_pow_neZero hq)) := by
    rw [(f.map (σ ^ b)).as_tsum, tsum_subst _ (has_subst₁ _)]
    congr! 2 with i
    rw [PowerSeries.monomial_eq_C_mul_X_pow, ← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul
      (has_subst₁ _), PowerSeries.coeff_map, PowerSeries.subst_pow (has_subst₁ _),
        PowerSeries.subst_X (has_subst₁ b), MvPowerSeries.map_expand]
    exact ⟨_, PowerSeries.hasSum_of_monomials_self _⟩
  have b_le_qb (b : ℕ) : (b : ENat) ≤ q ^ b := by
    exact_mod_cast (Nat.lt_pow_self (IsPrimePow.one_lt (isPrimePow_q ht hq))).le
  have le_order_aux {b : ℕ} : ↑b ≤ (s b • PowerSeries.subst
      ((F.map (σ ^ b)).expand (q^b) (q_pow_neZero hq)) ((PowerSeries.map (σ ^ b)) f)).order := by
    have le_aux : q ^ b ≤ ((F.map (σ ^ b)).expand (q ^ b) (q_pow_neZero hq)).order := by
      rw [MvPowerSeries.order_expand]
      simpa using le_mul_of_one_le_right' (.trans (F.one_le_order
        (constantCoeff_inv_add_RecurFun ..)) (MvPowerSeries.le_order_map _))
    refine (.trans (b_le_qb b) (.trans (.trans ?_ (PowerSeries.le_order_subst _ (has_subst₁ _) _))
      (MvPowerSeries.le_order_smul)))
    refine le_mul_of_le_of_one_le le_aux (one_le_order ?_)
    rw [PowerSeries.constantCoeff_map, constantCoeff_RecurFun, map_zero]
  have eq_aux {a₀ a₁ a₂ b₀ b₁ b₂ : MvPowerSeries (Fin 2) K}: a₀ + a₁ + a₂ - b₀ - b₁ - b₂ =
    a₀ + (a₁ + a₂ - b₀ - b₁) - b₂ := by ring
  rw [eq_aux, ←tsum_eq_aux ht hq σ s hg hg_unit hs0, f_def]
  nth_rw 2 [FunEq_of_RecurFun ht hq σ s hg hs0]
  rw [subst_add has_subst_F]
  have eq_aux₁ : (g.map R.subtype).subst F = g.subst F := by
    erw [g.map_algebraMap_eq_subst_X, subst_comp_subst_apply
      HasSubst.X' has_subst_F, subst_X has_subst_F]
  have eq_aux₂ {i_1 i : ℕ}: (monomial i_1 (coeff i_1 f)).subst
    (monomial (q ^ i) (R := K) 1) = monomial (i_1 * q ^ i) (R := K) (f.coeff i_1) := by
    nth_rw 2 [monomial_eq_C_mul_X_pow]
    rw [← PowerSeries.smul_eq_C_mul, subst_smul (has_subst_monomial i),
      subst_pow (has_subst_monomial i), subst_X (has_subst_monomial i),
      PowerSeries.monomial_pow, monomial_eq_C_mul_X_pow,
      monomial_eq_C_mul_X_pow, PowerSeries.smul_eq_C_mul]
    simp
  rw [eq_aux₁]
  ring_nf
  rw [tsum_subst _ has_subst_F, map_sub, ←F_def, ←f_def,
    Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n),
    Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n)]
  /- here need to use the second technical lemma! It is the equation 2.4.11 in Hazewinkel. -/
  rw [tsum_eq_sum (s := range (n.degree + 1)), tsum_eq_sum (s := range (n.degree + 1)),
    ← sum_sub_distrib]
  refine Subring.sum_mem R <| fun i hi => by
    simp_rw [PowerSeries.subst_smul has_subst_F, MvPowerSeries.coeff_smul, ← mul_sub]
    refine hs₁ i _ ?_
    rw [Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n)]
    /- there should be a tsum to finite -/
    rw [tsum_eq_sum (s := range (n.degree + 1))]
    have eq_aux : (MvPowerSeries.coeff n) (PowerSeries.subst F ((MvPowerSeries.map (σ ^ i))
      (f.expand (q ^ i) (q_pow_neZero hq)))) = ∑ b ∈ range (n.degree + 1),
      MvPowerSeries.coeff n ((σ ^ i) ((PowerSeries.coeff b) f) • F ^ (q ^ i * b)) := by
      /- to finite-/
      erw [PowerSeries.map_expand]
      rw [PowerSeries.expand_apply, PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow (q_pow_neZero hq)) has_subst_F,
        PowerSeries.subst_pow has_subst_F, PowerSeries.subst_X has_subst_F,
        PowerSeries.coeff_subst (HasSubst.pow has_subst_F le_q_pow)]
      simp_rw [MvPowerSeries.coeff_smul, PowerSeries.coeff_map, smul_eq_mul, pow_mul]
      refine finsum_eq_finset_sum_of_support_subset _ (Function.support_subset_iff'.mpr ?_)
      intro d hd
      simp only [coe_range, Set.mem_Iio, not_lt] at hd
      have : (MvPowerSeries.coeff n) ((F ^ q ^ i) ^ d) = 0 := by
        refine MvPowerSeries.coeff_of_lt_order
          <| (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp ?_
        rw [← pow_mul]
        have aux : (d : ENat) ≤ (q ^ i * d) := by
          exact_mod_cast Nat.le_mul_of_pos_left d (Nat.pow_pos (q.pos_of_ne_zero (q_neZero hq)))
        refine .trans (.trans (by norm_cast) aux)
          (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_inv_add_RecurFun ..))
      simp [this]
    rw [PowerSeries.map, eq_aux, ← sum_sub_distrib]
    simp_rw [MvPowerSeries.coeff_smul, ← mul_sub]
    apply mem_ideal_aux
    intro b hb
    by_cases hb₀ : b = 0
    · simp [hb₀]
    have mem_aux : ((MvPowerSeries.coeff n) ((MvPowerSeries.map (σ ^ i))
      (F.expand (q^i) (q_pow_neZero hq)) ^ b) - (MvPowerSeries.coeff n)
        (F ^ (q ^ i * b))) ∈ R.subtype '' ↑(I ^ (multiplicity q b + 1)) := by
      by_cases hi₀ : i = 0
      · have aux : (MvPowerSeries.coeff n) ((MvPowerSeries.map (1 : K →+* K)) F ^ b) -
          (MvPowerSeries.coeff n) (F ^ b) = 0 := by
          simp [MvPowerSeries.map, MvPowerSeries.coeff_apply]
        simp [hi₀, aux]
      · obtain ⟨m, hm⟩ := pow_multiplicity_dvd q b
        /- Here need another version of pow_ModEq. -/
        let F₁_aux : (Fin 2 →₀ ℕ) → K := fun (i : Fin 2 →₀ ℕ) => if i.degree < k then F.coeff i
          else 0
        have F₁_mem : ∀ i, MvPowerSeries.coeff i F₁_aux ∈ R := by
          intro i
          by_cases hi : i.degree < k
          · simp [F₁_aux, coeff_apply, if_pos hi]
            exact h_ind (Finsupp.degree i) hi i rfl
          · simp [F₁_aux, coeff_apply, if_neg hi]
        let F₁ := MvPowerSeries.toSubring F₁_aux R F₁_mem
        have F₁_apply : ∀ d, d.degree < k → MvPowerSeries.coeff d F₁ = F.coeff d := by
          intro d hd
          simp [F₁, F₁_aux]
          rw [coeff_apply, if_pos hd]
        obtain ⟨x, hx₁, hx₂⟩ := pow_ModEq ht hq σ hs a_congr hp_mem F₁ i hm n
        have eq_aux₁ : (MvPowerSeries.coeff n) ((MvPowerSeries.map (σ ^ i)) (F.expand (q ^ i)
          (q_pow_neZero hq)) ^ b) = (MvPowerSeries.coeff n) ((MvPowerSeries.map (σ ^ i))
            ((MvPowerSeries.expand (q ^ i) (q_pow_neZero hq)) (F₁.map (R.subtype))) ^ b) := by
          simp only [MvPowerSeries.map_expand]
          rw [coeff_coe_aux ht hq σ h hi₀ F₁_apply _ (constantCoeff_inv_add_RecurFun ..)]
          · have aux : MvPowerSeries.constantCoeff F₁ = (0 : K) := by
              unfold F₁ F₁_aux
              rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_toSubring,
                coeff_apply]
              split_ifs
              · rw [MvPowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_inv_add_RecurFun]
              · rfl
            norm_cast at aux
        have eq_aux₂ : (F ^ (q ^ i * b)).coeff n = ((F₁.map (R.subtype)) ^ (q ^ i * b)).coeff n := by
          rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow, Finset.sum_congr rfl]
          intro l hl
          simp only [mem_finsuppAntidiag] at hl
          by_cases! ha : ∀ a ∈ range (q ^ i * b), (l a).degree < k
          · rw [Finset.prod_congr rfl]
            intro a' ha'
            simp [← F₁_apply (l a') (ha a' ha')]
          obtain ⟨a, ha₁, ha₂⟩ := ha
          obtain ⟨a', ha'₁, ha'₂⟩ : ∃ a' ∈ (range (q ^ i * b)).erase a, l a' = 0 := by
            by_contra! hc
            have le_aux : 2 ≤ q ^ i * b := .trans (by norm_num) (Nat.mul_le_mul
              (two_le_q_pow ht hq hi₀) (Nat.one_le_iff_ne_zero.mpr hb₀))
            obtain ⟨a', ha'⟩ : ∃ a', a' ∈ (range (q ^ i * b)).erase a :=
              nonempty_def.mp <| (erase_nonempty ha₁).mpr (range_nontrivial le_aux)
            specialize hc a' ha'
            have a_neq : a ≠ a' := (ne_of_mem_erase ha').symm
            have : ∀ j ∈ range (q ^ i * b), 0 ≤ (l j).degree := by simp
            obtain h := Finset.add_le_sum this ha₁ (mem_of_mem_erase ha')
              (ne_of_mem_erase ha').symm
            have : ∑ k ∈ range (q ^ i * b), Finsupp.degree (l k) = n.degree := by
              simp [← hl.1]
            rw [this] at h
            have one_le : 0 < (l a').degree := by
              refine Nat.zero_lt_of_ne_zero ?_
              by_contra! hc'
              exact hc ((Finsupp.degree_eq_zero_iff _).mp hc')
            linarith
          obtain h1 := constantCoeff_inv_add_RecurFun ht hq σ s hg hg_unit
          rw [Finset.prod_eq_zero (mem_of_mem_erase ha'₁) _, Finset.prod_eq_zero (mem_of_mem_erase ha'₁)]
          · simp only [ha'₂, coeff_apply, MvPowerSeries.map_toSubring, map_zero, ite_eq_right_iff, F₁,
            F₁_aux]
            rw [← coeff_apply F, MvPowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_inv_add_RecurFun]
            simp
          · rw [ha'₂, MvPowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_inv_add_RecurFun]
        rw [eq_aux₁, eq_aux₂]
        use x
        rw [SetLike.mem_coe] at hx₁
        simp [hx₁, hx₂]
    refine refinement_hs₂ σ hs₂ i (multiplicity q b + 1) _ ?_ _ mem_aux
    intro a ha
    have a_mem : ⟨a, image_of_incl_mem a ha⟩ ∈ I ^ (multiplicity q b + 1) := by
      obtain ⟨a', ha'₁, ha'₂⟩ := ha
      simp_rw [← ha'₂]
      simpa using ha'₁
    obtain h1 := coeff_RecurFun_mul_mem_i ht hq σ s hs₁ hs₂ hg b 1 ⟨a, image_of_incl_mem a ha⟩ a_mem
    simpa using h1
    · intro b hb
      simp only [mem_range, not_lt] at hb
      apply MvPowerSeries.coeff_of_lt_order
      refine (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp ?_
      have le_aux : b ≤ ((MvPowerSeries.map (σ ^ i)) (F.expand (q ^ i) (q_pow_neZero hq)) ^ b).order := by
        refine .trans (le_refl _) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ?_)
        rw [MvPowerSeries.constantCoeff_map, MvPowerSeries.constantCoeff_expand,
          constantCoeff_inv_add_RecurFun, map_zero]
      -- using order_expand
      refine .trans (by norm_cast) (.trans le_aux (MvPowerSeries.le_order_smul))
    have summable_aux : ∀ n, (σ ^ i) ((PowerSeries.coeff n) f) • (MvPowerSeries.map (σ ^ i))
      (F.expand (q^i) (q_pow_neZero hq)) ^ n = PowerSeries.subst
      ((F.map (σ ^ i)).expand (q^i) (q_pow_neZero hq))
      ((PowerSeries.monomial n) ((PowerSeries.coeff n) ((PowerSeries.map (σ ^ i)) f))) := by
      intro n
      rw [PowerSeries.monomial_eq_C_mul_X_pow, ← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul (has_subst₁ _),
        PowerSeries.subst_pow (has_subst₁ _), PowerSeries.subst_X (has_subst₁ _),
          PowerSeries.coeff_map, MvPowerSeries.map_expand]
    simp_rw [summable_aux]
    exact Summable.summable_of_subst ⟨_, PowerSeries.hasSum_of_monomials_self _⟩ (has_subst₁ _)
  · intro b hb
    simp only [mem_range, not_lt] at hb
    apply MvPowerSeries.coeff_of_lt_order
    refine (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp
      (.trans (by norm_cast) (.trans (b_le_qb b) (.trans (le_mul_of_one_le_of_le
        (F.one_le_order (constantCoeff_inv_add_RecurFun ..))
        (.trans (.trans ?_ (PowerSeries.le_order_map _)) le_order_smul)) (le_order_subst _ has_subst_F _))))
    have le_aux' : q ^ b ≤ (monomial (q ^ b) (1 : K)).order * f.order := by
      refine .trans (ENat.self_le_mul_right _ (zero_ne_one' _).symm)
        (mul_le_mul ?_ ?_ zero_le_one (zero_le _))
      · rw [PowerSeries.order_monomial]
        split_ifs <;> simp
      exact ENat.one_le_iff_ne_zero.mpr <| PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr
        (constantCoeff_RecurFun ..)
    refine .trans le_aux' ?_
    rw [PowerSeries.order_eq_order]
    refine .trans (PowerSeries.le_order_subst _ (has_subst_monomial (i := b)) f) ?_
    simp [PowerSeries.order_eq_order, PowerSeries.expand_apply, monomial_eq_C_mul_X_pow]
  · intro b hb
    simp at hb
    rw [tsum_eq_subst]
    exact MvPowerSeries.coeff_of_lt_order <| (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp
      (.trans (by norm_cast) le_order_aux)
  · exact MvPowerSeries.Summable.increase_order fun n =>
      (MvPowerSeries.smul_eq_C_mul _ (s n)) ▸ (le_order₁ ..)
  · exact MvPowerSeries.Summable.increase_order fun n => tsum_eq_subst ▸ le_order_aux
  · exact PowerSeries.Summable.increase_order fun n => by
      have le_aux : n ≤ ((MvPowerSeries.map (σ ^ n)) ((RecurFun ht hq σ s hg).expand (q ^ n)
        (q_pow_neZero hq))).order := by
        refine .trans ?_ (MvPowerSeries.le_order_map _)
        simp [← PowerSeries.order_eq_order, PowerSeries.order_expand]
        exact le_mul_of_le_of_one_le (b_le_qb n) <|
          PowerSeries.one_le_order (constantCoeff_RecurFun ..)
      rw [PowerSeries.order_eq_order]
      exact .trans le_aux (MvPowerSeries.le_order_smul)

open AddMonoidHom PowerSeries in
lemma coeff_subst_X_mem_aux {n : Fin 2 →₀ ℕ} {x : Fin 2} :
    (g.subst (X x (R := K))).coeff n ∈ R := by
  have eq_aux : g.subst (X x (R := K)) = (g.subst (X x)).map R.subtype := by
    ext d
    rw [coeff_subst <| .X x, MvPowerSeries.coeff_map, coeff_subst <| .X x,
      R.subtype.eq_toAddMonoidHom, AddMonoidHom.map_finsum _ <| coeff_subst_finite (.X x) g d, finsum_congr]
    intro m
    congr
    rw [MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X_pow]
    norm_cast
  simp [eq_aux]

include hs a_congr hp_mem hs₁ hs₂ in
/-- by above lemma we can deduce that all coefficient in g(F(X,Y)) is in `R`, since
  f(F(X,Y)) = f(X) + f(Y).-/
lemma RModEq_aux₂ [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0)
    {n : Fin 2 →₀ ℕ} {k : ℕ} (h : n.degree = k) :
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    (h_ind : ∀ m < k, ∀ (n : Fin 2 →₀ ℕ), n.degree = m → F.coeff n ∈ R) → (g.subst F).coeff n ∈ R := by
  intro F h_ind
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  obtain h₀ := RModEq_aux ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hs0 h h_ind
  rw [f_F_eq_f_add, ←F_def] at h₀
  ring_nf at h₀
  simp at h₀
  have mem_aux : (-(coeff n) (g.subst X₀) - (coeff n) (g.subst X₁)) ∈ R :=
    Subring.sub_mem R (Subring.neg_mem R coeff_subst_X_mem_aux) coeff_subst_X_mem_aux
  exact (add_mem_cancel_right mem_aux).mp h₀

lemma F_coeff_mem_ind [UniformSpace K] [T2Space K] [DiscreteUniformity K]
     {n : Fin 2 →₀ ℕ} {k : ℕ} (h : n.degree = k) :
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    (h_ind : ∀ m < k, ∀ (n : Fin 2 →₀ ℕ), n.degree = m → F n ∈ R) →
    (g.coeff 1) * F.coeff n - (g.subst F).coeff n ∈ R := by
  intro  F h_ind
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  obtain h₁ := g.coeff_subst_finite (HasSubst.inv_add_RecurFun ht hq σ s hg hg_unit) n
  rw [PowerSeries.coeff_subst <| HasSubst.inv_add_RecurFun .., finsum_eq_sum _ h₁]
  have eq_aux : ↑((PowerSeries.coeff 1) g) * (coeff n) F =
    ∑ i ∈ h₁.toFinset, if i = 1 then ↑((PowerSeries.coeff 1) g) * (coeff n) F else 0 := by
    by_cases hd : (coeff n) F = 0
    · simp [hd]
    refine Eq.symm <| sum_eq_single 1 (fun b _ hb' => if_neg hb') (by simp; tauto)
  rw [eq_aux, ←sum_sub_distrib]
  apply Subring.sum_mem R
  intro i hi
  by_cases hi₀ : i = 0
  · simp [hi₀, hg]
  by_cases hi' : i = 1
  · simp [hi', Subring.smul_def, F]
  · simp only [if_neg hi', Subring.smul_def, smul_eq_mul, zero_sub, neg_mem_iff]
    refine Subring.mul_mem R (SetLike.coe_mem _) ?_
    rw [coeff_pow]
    refine Subring.sum_mem R <| fun l hl => by
      by_cases h_neZero : ∃ j ∈ range i, l j = 0
      · obtain ⟨j, hj, hj'⟩ := h_neZero
        have eq_zero : ∏ i ∈ range i, (coeff (l i)) F = 0 := by
          refine prod_eq_zero hj ?_
          simpa [hj'] using constantCoeff_inv_add_RecurFun ..
        exact eq_zero ▸ R.zero_mem
      simp only [mem_range, not_exists, not_and] at h_neZero
      have aux : ∀ t ∈ range i, 0 ≤ (l t).degree := fun t ht => by simp
      refine Subring.prod_mem R <| fun j hj => by
        simp at hl
        have le_aux : (l j).degree ≤ n.degree := by
          rw [←hl.1, map_sum]
          exact Finset.single_le_sum aux hj
        by_cases hlj : (l j).degree < n.degree
        · rw [h] at hlj
          exact h_ind _ hlj _ rfl
        have eq_aux : (l j).degree = n.degree := by linarith
        have neq_aux : ∀ b ∈ range i, b ≠ j → l b = 0 := by
          intro b hb hb'
          by_contra hc
          have hlb : (l b).degree ≥ 1 := by
            refine Nat.one_le_iff_ne_zero.mpr ?_
            by_contra hc'
            exact hc <| (Finsupp.degree_eq_zero_iff _).mp hc'
          have contra_aux : ∑ s ∈ range i, (l s).degree ≥ (l b).degree + (l j).degree :=
            add_le_sum aux hb hj hb'
          rw [eq_aux, ← map_sum, hl.1] at contra_aux
          linarith
        have i_ge : 2 ≤ i := by omega
        have exist_b : ∃ b ∈ range i, b ≠ j := by
          by_cases hj₀ : j = 0
          · use 1; simpa [hj₀]
          use 0
          simp only [mem_range, ne_eq, Ne.symm hj₀, not_false_eq_true, and_true]
          linarith
        obtain ⟨b, hb, hb'⟩ := exist_b
        exfalso
        exact (h_neZero b (mem_range.mp hb)) (neq_aux b hb hb')

include hs a_congr hp_mem hs₁ hs₂ in
/-- `inv_add_aux` define to be `f_g⁻¹(f_g(X) + f_g(Y))`, the coeff of this multi variate
  power series are all in `R`.-/
theorem coeff_inv_add_mem_Subring [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs₀ : s 0 = 0) : ∀ n, (inv_add_RecurFun ht hq σ s hg hg_unit).coeff n ∈ R := by
  intro n
  generalize h : n.degree = d
  induction d using Nat.strongRecOn generalizing n with
  | ind k hk =>
    have eq_aux : (inv_add_RecurFun ht hq σ s hg hg_unit).coeff n = hg_unit.unit⁻¹ *
      ↑(g.coeff 1) * (coeff n) (inv_add_RecurFun ht hq σ s hg hg_unit) := by
      norm_cast; simp [IsUnit.val_inv_mul hg_unit]
    rw [eq_aux, mul_assoc]
    exact Subring.mul_mem R (SetLike.coe_mem _) <| by
      simpa using (Subring.add_mem _ (F_coeff_mem_ind ht hq σ s hg hg_unit h hk)
        (RModEq_aux₂ ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hs₀ h hk))

def CommFormalGroup.InvAdd_RecurFun_Aux : CommFormalGroup K where
  toFun := inv_add_RecurFun ht hq σ s hg hg_unit
  zero_constantCoeff := by
    rw [inv_add_RecurFun, PowerSeries.constantCoeff_subst_eq_zero _ _
      (constantCoeff_inv_RecurFun ..)]
    · rw [map_add]
      simp_rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero
        (constantCoeff_X _) _ (constantCoeff_RecurFun ..), zero_add]
  lin_coeff_X := coeff_X_inv_add_RecurFun ht hq σ s hg hg_unit
  lin_coeff_Y := coeff_Y_inv_add_RecurFun ht hq σ s hg hg_unit
  assoc := by
    let f := RecurFun ht hq σ s hg
    let f_inv := inv_RecurFun ht hq σ s hg hg_unit
    let F := inv_add_RecurFun ht hq σ s hg hg_unit
    have f_def : f = RecurFun ht hq σ s hg := rfl
    have f_inv_def : f_inv = inv_RecurFun ht hq σ s hg hg_unit := rfl
    have F_def : F = inv_add_RecurFun ht hq σ s hg hg_unit := rfl
    have f_comp_F : f.subst F = f.toMvPowerSeries 0 + f.toMvPowerSeries 1 := by
      rw [(f_F_eq_f_add ht hq σ s hg hg_unit), PowerSeries.toMvPowerSeries_apply,
        PowerSeries.toMvPowerSeries_apply]
    rw [PowerSeries.subst] at f_comp_F
    have eq_aux {α β : MvPowerSeries (Fin 3) K} {γ : PowerSeries K} (h : HasSubst ![α, β]) :
      subst ![α, β] (γ.toMvPowerSeries 0 + γ.toMvPowerSeries 1) =
        γ.subst α + γ.subst β := by
      simp [subst_add h, PowerSeries.toMvPowerSeries_apply, PowerSeries.subst,
        subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X _)) h,
        subst_X h]
    have has_subst₁ : HasSubst ![subst ![Y₀ (R := K), Y₁] F, Y₂] :=
      has_subst_aux₁ (constantCoeff_inv_add_RecurFun ..)
    have has_subst₂ : HasSubst ![Y₀, subst ![Y₁ (R := K), Y₂] F] :=
      has_subst_aux₂ (constantCoeff_inv_add_RecurFun ..)
    have has_subst₃ : PowerSeries.HasSubst ((RecurFun ht hq σ s hg).toMvPowerSeries (0 : Fin 2) +
      (RecurFun ht hq σ s hg).toMvPowerSeries 1) := by
      refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
      rw [map_add, PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply,
        PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
        (constantCoeff_RecurFun ..), PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
          (constantCoeff_RecurFun ..), add_zero]
    nth_rw 2 4 [inv_add_RecurFun]
    rw [PowerSeries.subst, subst_comp_subst_apply (PowerSeries.HasSubst.const has_subst₃)
      has_subst₁, subst_comp_subst_apply (PowerSeries.HasSubst.const has_subst₃) has_subst₂,
        subst_congr]
    funext i
    have eq_aux₁ : subst ![subst ![Y₀, Y₁] F, Y₂] (f.toMvPowerSeries 0) =
      f.toMvPowerSeries 0 + f.toMvPowerSeries 1 := by
      rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.subst, subst_comp_subst_apply
        (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X _)) has_subst₁, subst_X has_subst₁,
        Matrix.cons_val_zero, ← subst_comp_subst_apply (PowerSeries.HasSubst.const
        (HasSubst.inv_add_RecurFun ..)) has_subst_XY, f_comp_F, eq_aux has_subst_XY,
        PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply]
    have eq_aux₂ : subst ![Y₀, subst ![Y₁, Y₂] F] ((RecurFun ht hq σ s hg).toMvPowerSeries 1)
      = f.toMvPowerSeries 1 + f.toMvPowerSeries 2 := by
      rw [PowerSeries.toMvPowerSeries_val _ has_subst₂, Matrix.cons_val_one,
        Matrix.cons_val_zero, PowerSeries.subst, ← subst_comp_subst_apply
        (PowerSeries.HasSubst.const (HasSubst.inv_add_RecurFun ..)) has_subst_YZ,
          f_comp_F, eq_aux has_subst_YZ, PowerSeries.toMvPowerSeries_apply,
          PowerSeries.toMvPowerSeries_apply]
    rw [subst_add has_subst₁, eq_aux₁, PowerSeries.toMvPowerSeries_val _ has_subst₁,
      Matrix.cons_val_one, Matrix.cons_val_zero, subst_add has_subst₂,
      PowerSeries.toMvPowerSeries_val _ has_subst₂, Matrix.cons_val_zero, eq_aux₂]
    simpa [PowerSeries.toMvPowerSeries_apply] using add_assoc _ _ _
  comm := by
    rw [inv_add_RecurFun, PowerSeries.subst, subst_comp_subst_apply _ has_subst_swap, subst_congr]
    funext i
    conv_rhs =>
      rw [add_comm ((RecurFun ht hq σ s hg).toMvPowerSeries 0), subst_add has_subst_swap]
    congr
    · simp_rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.subst, subst_comp_subst_apply
        (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X _)) has_subst_swap,
          subst_X has_subst_swap, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · simp_rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.subst, subst_comp_subst_apply
        (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X _)) has_subst_swap,
          subst_X has_subst_swap, Matrix.cons_val_zero]
    · refine PowerSeries.HasSubst.const <| PowerSeries.HasSubst.of_constantCoeff_zero ?_
      rw [map_add, PowerSeries.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
        (constantCoeff_RecurFun ..), PowerSeries.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
          (constantCoeff_RecurFun ..), add_zero]

def CommFormalGroup.InvAdd_RecurFun [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs₀ : s 0 = 0) : CommFormalGroup R :=
  (CommFormalGroup.InvAdd_RecurFun_Aux ht hq σ s hg hg_unit).toSubring _
    (coeff_inv_add_mem_Subring ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hs₀)

include hs a_congr hp_mem hs₁ hs₂ in
theorem decomp_InvAdd_RecurFun [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs₀ : s 0 = 0) : ∃ (G : MvPowerSeries (Fin 2) R),
    (inv_add_RecurFun ht hq σ s hg hg_unit) = X₁ + X₀ * G.map R.subtype := by
  obtain ⟨G, hG⟩ := FormalGroup.decomp_Y_add (CommFormalGroup.InvAdd_RecurFun ht hq σ hs a_congr hp_mem s hs₁
    hs₂ hg hg_unit hs₀ : FormalGroup R)
  use G
  simp only [CommFormalGroup.InvAdd_RecurFun, CommFormalGroup.toSubring,
    CommFormalGroup.InvAdd_RecurFun_Aux] at hG
  have : ∀ n, coeff n (inv_add_RecurFun ht hq σ s hg hg_unit) =
    (coeff n (X₁ + X₀ * G) : R) := by simp [← hG]
  ext n
  simp only [this, map_add, Subring.coe_add]
  congr
  · simp_rw [coeff_X]
    split_ifs with h <;> simp
  rw [coeff_mul, coeff_mul]
  simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, coeff_map, Subring.subtype_apply]
  congr! 2 with l  hl
  simp_rw [coeff_X]
  split_ifs with h <;> simp

include hs a_congr hp_mem hs₁ hs₂ in
theorem decomp_InvAdd_RecurFun_Subring [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs₀ : s 0 = 0) : ∃ (G : MvPowerSeries (Fin 2) R),
    (inv_add_RecurFun ht hq σ s hg hg_unit).toSubring _
      (coeff_inv_add_mem_Subring ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hs₀)
        = X₁ + X₀ * G :=
  FormalGroup.decomp_Y_add (CommFormalGroup.InvAdd_RecurFun ht hq σ hs a_congr
    hp_mem s hs₁ hs₂ hg hg_unit hs₀: FormalGroup R)

end PartI

section PartII

variable {g' : PowerSeries R} (hg' : g'.constantCoeff = 0)
/- In this section, we denote $G(X) = f_g⁻¹(f_{g'} (X))$ for simplicity. -/

open PowerSeries HasSubst in
/-- f_g'(X) = f(G(X)). -/
lemma f_g'_eq_f_G :
    let f := RecurFun ht hq σ s hg
    let f_g' := RecurFun ht hq σ s hg'
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    f_g' = f.subst G := by
  intro f f_g' G
  rw [← subst_comp_subst_apply (of_constantCoeff_zero' rfl) (.of_constantCoeff_zero'
    (constantCoeff_RecurFun ..)), inv_RecurFun, subst_inv_eq, subst_X
      (.of_constantCoeff_zero' (constantCoeff_RecurFun ..))]

lemma constantCoeff_G :
    constantCoeff (PowerSeries.subst (RecurFun ht hq σ s hg')
      (inv_RecurFun ht hq σ s hg hg_unit)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_RecurFun ..) _ rfl

lemma decomp_f_g' [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0):
    let f := RecurFun ht hq σ s hg
    let f_g' := RecurFun ht hq σ s hg'
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    f_g' = g.subst G + ∑' i, s i • ((f.map (σ ^ i)).subst (G ^ q ^ i)) := by
  intro f f_g' G
  unfold f_g'
  have has_subst_aux : PowerSeries.HasSubst (PowerSeries.subst (RecurFun ht hq σ s hg')
    (inv_RecurFun ht hq σ s hg hg_unit)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero <| constantCoeff_G ..
  rw [f_g'_eq_f_G ht hq σ s hg hg_unit hg', FunEq_of_RecurFun ht hq σ s hg hs0,
    PowerSeries.subst_add has_subst_aux]
  congr! 2
  ext n
  rw [PowerSeries.coeff_subst' has_subst_aux, PowerSeries.coeff_subst' has_subst_aux, finsum_congr]
  intro d
  simp only [PowerSeries.coeff_map, Subring.subtype_apply, smul_eq_mul]
  exact (smul_eq_mul _ _).symm
  rw [tsum_subst _ has_subst_aux, tsum_congr]
  intro i
  rw [PowerSeries.subst_smul has_subst_aux, PowerSeries.map_expand, PowerSeries.expand_apply,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow (q_pow_neZero hq)) has_subst_aux,
    PowerSeries.subst_pow has_subst_aux, PowerSeries.subst_X has_subst_aux]
  · exact summable_aux ht hq σ s hg hs0

lemma tsum_eq_aux₁ [TopologicalSpace K] :
    let f := RecurFun ht hq σ s hg
    ∑' (i : ℕ), s i • (PowerSeries.map (σ ^ i))
    ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) (RecurFun ht hq σ s hg')) =
    ∑' (i : ℕ), s i • (PowerSeries.map (σ ^ i)) ((PowerSeries.expand (q ^ i) (q_pow_neZero hq))
    (f.subst (PowerSeries.subst (RecurFun ht hq σ s hg') (inv_RecurFun ht hq σ s hg hg_unit)))) := by
  nth_rw 1 [f_g'_eq_f_G ht hq σ s hg hg_unit hg']

include ht hs a_congr hp_mem in
lemma coeff_mem_aux {i b n : ℕ} (hi : i ≠ 0) {G : PowerSeries K} (hG : G.constantCoeff = 0)
    (h_ind : ∀ m < n, (PowerSeries.coeff m) G ∈ R) :
    (σ ^ i) ((PowerSeries.coeff n) ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) (G ^ b))) -
      (PowerSeries.coeff n) ((G ^ q ^ i) ^ b) ∈ R.subtype '' ↑(I ^ (multiplicity q b + 1)) := by
  let G₁_aux := PowerSeries.mk (fun i => if i < n then G.coeff i else 0)
  have G₁_mem : ∀ i, G₁_aux.coeff i ∈ R := by
    intro i
    by_cases hi : i < n
    · simp [G₁_aux, if_pos hi, h_ind i hi]
    · simp [G₁_aux, if_neg hi]
  let G₁ := G₁_aux.toSubring R G₁_mem
  have G₁_apply : ∀ i, i < n → G₁.coeff i = G.coeff i := by
    intro i hi
    simp only [PowerSeries.coeff_toSubring, PowerSeries.coeff_mk, ite_eq_left_iff, not_lt, G₁,
      G₁_aux]
    exact fun h ↦ by linarith
  have hG₁ : G₁.constantCoeff = 0 := by
    have : G₁.constantCoeff = (0 : K) := by simp [G₁, G₁_aux, hG]
    norm_cast at this
  have eq_aux₁ : ((PowerSeries.coeff n) ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) (G ^ b))) =
    ((PowerSeries.coeff n) ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) (G₁ ^ b))) := by
    by_cases hn : n = 0
    · simp [hn, PowerSeries.constantCoeff_expand, hG, hG₁]
    by_cases hdvd : q ^ i ∣ n
    · obtain ⟨d, hd⟩ := hdvd
      simp_rw [hd, PowerSeries.coeff_expand_mul, PowerSeries.coeff_pow]
      simp only [AddSubmonoidClass.coe_finset_sum, SubmonoidClass.coe_finset_prod]
      rw [sum_congr rfl]
      intro l hl
      rw [prod_congr rfl]
      intro j hj
      simp only [mem_finsuppAntidiag] at hl
      have : ∀ t ∈ range b, l t ≤ d := fun t ht => hl.1 ▸ single_le_sum_of_canonicallyOrdered ht
      have d_le : d < n := by
        rw [hd]
        obtain aux := two_le_q_pow ht hq hi
        refine (Nat.lt_mul_iff_one_lt_left ?_).mpr aux
        by_contra! hc
        rw [Nat.eq_zero_of_le_zero hc, mul_zero] at hd
        exact hn hd
      have : ∀ t ∈ range b, l t < n := fun t ht => by linarith [this t ht]
      exact (G₁_apply _ (this j hj)).symm
    simp_rw [PowerSeries.coeff_expand_of_not_dvd _ (q_pow_neZero hq) _ hdvd]
    rfl
  have eq_aux₂ : (PowerSeries.coeff n) ((G ^ q ^ i) ^ b) =
    (PowerSeries.coeff n) ((G₁ ^ q ^ i) ^ b) := by
    by_cases hb₀ : b = 0
    · simp [hb₀]; aesop
    simp_rw [← pow_mul]
    simp [PowerSeries.coeff_pow, PowerSeries.coeff_pow]
    rw [sum_congr rfl]
    intro l hl
    simp at hl
    by_cases! h_exist : ∃ j ∈ range (q ^ i * b), l j = 0
    · obtain ⟨a, ha₁, ha₂⟩ := h_exist
      rw [prod_eq_zero ha₁, prod_eq_zero ha₁]
      · simp [ha₂, hG₁]
      · simp [ha₂, hG]
    have two_le : 2 ≤ q ^ i * b := .trans (by norm_num) (Nat.mul_le_mul
      (two_le_q_pow ht hq hi) (Nat.one_le_iff_ne_zero.mpr hb₀))
    have lt_aux : ∀ j ∈ range (q ^ i * b), l j < n := by
      by_contra! hc
      obtain ⟨j, hj₁, hj₂⟩ := hc
      obtain ⟨k, hk⟩ : ((range (q ^ i * b)).erase j).Nonempty :=
        (erase_nonempty hj₁).mpr <| range_nontrivial two_le
      have : ∀ j ∈ (range (q ^ i * b)), 0 ≤ l j := by simp
      have k_neq_j : k ≠ j := (ne_of_mem_erase hk)
      obtain aux := Finset.add_le_sum this (mem_of_mem_erase hk) hj₁ (ne_of_mem_erase hk)
      have lk_pos : 0 < l k := pos_of_ne_zero <| h_exist k (mem_of_mem_erase hk)
      linarith
    exact (prod_congr rfl fun j hj => G₁_apply (l j) (lt_aux j hj)).symm
  rw [eq_aux₁, eq_aux₂]
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd q b
  obtain ⟨x, hx₁, hx₂⟩ := pow_ModEq ht hq σ hs a_congr hp_mem G₁ i hm
    (Finsupp.single () n)
  use x
  rw [SetLike.mem_coe] at hx₁
  simp only [SetLike.mem_coe, hx₁, hx₂, ← map_expand, map_pow, MvPowerSeries.map_map,
    PowerSeries.coeff_coe, map_sub, RingHom.coe_pow, true_and]
  rw [← map_pow, ← map_pow, ← map_pow ((MvPowerSeries.map R.subtype))]
  erw [PowerSeries.coeff_map, PowerSeries.coeff_map]
  simp [Subring.subtype_apply, pow_mul, PowerSeries.expand]

include hs a_congr hp_mem hs₁ hs₂ in
lemma coeff_g_G_mem_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) {n : ℕ} :
    let f_g' := RecurFun ht hq σ s hg'
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    (h_ind : ∀ m < n, (PowerSeries.coeff m) G ∈ R) →
      PowerSeries.coeff n (g.subst G + f_g' - g'.map R.subtype - f_g') ∈ R := by
  intro f_g' G h_ind
  have G_def : G = (inv_RecurFun ht hq σ s hg hg_unit).subst f_g' := rfl
  unfold f_g'
  nth_rw 2 [decomp_f_g' ht hq σ s hg hg_unit hg' hs0]
  nth_rw 1 [FunEq_of_RecurFun ht hq σ s hg' hs0]
  ring_nf
  have order_G_pow (b : ℕ) : b ≤ PowerSeries.order (G ^ b) :=
    .trans (le_refl _) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_G ..))
  have has_subst_G : PowerSeries.HasSubst G :=
    PowerSeries.HasSubst.of_constantCoeff_zero <| constantCoeff_G ..
  have le_order_aux₁ (b : ℕ) : b ≤ ((PowerSeries.expand (q ^ b) (q_pow_neZero hq))
    (PowerSeries.subst G (RecurFun ht hq σ s hg))).order := by
    rw [PowerSeries.order_expand]
    have : b ≤ q ^ b := (Nat.lt_pow_self (one_lt_q ht hq)).le
    have aux : q ^ b ≤ q ^ b • PowerSeries.order (PowerSeries.subst G (RecurFun ht hq σ s hg)) := by
      simp
      exact le_mul_of_one_le_right' (PowerSeries.one_le_order <|
        PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_G .. ) _ (constantCoeff_RecurFun ..))
    exact .trans (by norm_cast) aux
  have le_order_aux₂ (b : ℕ) : ↑b ≤ PowerSeries.order (s b • PowerSeries.subst (G ^ q ^ b)
    ((PowerSeries.map (σ ^ b)) (RecurFun ht hq σ s hg))) := by
    refine .trans ?_ PowerSeries.le_order_smul
    rw [PowerSeries.order_eq_order]
    refine .trans ?_ (PowerSeries.le_order_subst _ (PowerSeries.HasSubst.pow has_subst_G
      (one_le_q_pow hq)) _)
    have : q ^ b * 1 ≤ (G ^ q ^ b).order * ((PowerSeries.map (σ ^ b)) (RecurFun ht hq σ s hg)).order := by
      refine mul_le_mul ?_ (.trans (PowerSeries.one_le_order (constantCoeff_RecurFun ..))
        (PowerSeries.le_order_map _)) (zero_le_one' ℕ∞) (zero_le _)
      rw [← PowerSeries.order_eq_order]
      exact order_G_pow _
    rw [mul_one] at this
    exact .trans (by exact_mod_cast (Nat.lt_pow_self (one_lt_q ht hq)).le) this
  have {a b c : PowerSeries K} : a + b + (- a - c) = b - c := by ring
  rw [this]
  rw [tsum_eq_aux₁ ht hq σ s hg hg_unit hg']
  rw [map_sub, Summable.map_tsum _ _
    (PowerSeries.WithPiTopology.continuous_coeff K n), Summable.map_tsum _ _
    (PowerSeries.WithPiTopology.continuous_coeff K n), tsum_eq_sum (s := range (n + 1)),
    tsum_eq_sum (s := range (n + 1)), ← Finset.sum_sub_distrib]
  simp_rw [PowerSeries.coeff_smul, ← smul_sub, smul_eq_mul]
  rw [← G_def]
  refine Subring.sum_mem R ?_
  intro i hi
  by_cases hi₀ : i = 0
  · simp [hi₀, hs0]
  refine hs₁ i _ ?_
  rw [PowerSeries.subst_express_as_tsum _ (has_subst_G), PowerSeries.subst_express_as_tsum _
    (PowerSeries.HasSubst.pow has_subst_G (one_le_q_pow hq)),
    PowerSeries.expand_tsum (q_pow_neZero hq), PowerSeries.coeff_map,
    Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n),
    Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n)]
  rw [tsum_eq_sum (s := range (n + 1)), tsum_eq_sum (s := range (n + 1)), map_sum,
    ← sum_sub_distrib]
  apply mem_ideal_aux
  intro b hb
  rw [PowerSeries.coeff_smul, PowerSeries.expand_smul, PowerSeries.coeff_map,
    PowerSeries.coeff_smul, smul_eq_mul, map_mul, smul_eq_mul, ← mul_sub]
  refine refinement_hs₂ σ hs₂ i (multiplicity q b + 1) _ ?_ _
    (coeff_mem_aux ht hq σ hs a_congr hp_mem hi₀ (constantCoeff_G ..) h_ind)
  · intro a ha
    have a_mem : ⟨a, image_of_incl_mem a ha⟩ ∈ I ^ (multiplicity q b + 1) := by
      obtain ⟨a', ha'₁, ha'₂⟩ := ha
      simp_rw [← ha'₂]
      simpa using ha'₁
    obtain h1 := coeff_RecurFun_mul_mem_i ht hq σ s hs₁ hs₂ hg b 1 ⟨a, image_of_incl_mem a ha⟩ a_mem
    simpa using h1
  · intro b hb
    apply PowerSeries.coeff_of_lt_order
    simp only [mem_range, not_lt] at hb
    refine (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp (.trans ?_ (PowerSeries.le_order_smul))
    refine .trans (by norm_cast) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ?_)
    rw [map_pow, PowerSeries.constantCoeff, constantCoeff_G .., zero_pow (q_pow_neZero hq)]
  · intro b hb
    simp at hb
    apply PowerSeries.coeff_of_lt_order
    rw [PowerSeries.expand_smul]
    refine (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp (.trans ?_ (PowerSeries.le_order_smul))
    rw [PowerSeries.order_expand]
    exact .trans (.trans (by norm_cast) (le_self_nsmul b.cast_nonneg' (q_pow_neZero hq)))
      (nsmul_le_nsmul_right (order_G_pow _) _)
  · exact PowerSeries.Summable.increase_order fun n =>  .trans (.trans le_rfl
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (by erw [map_pow, constantCoeff_G, zero_pow
        (q_pow_neZero hq)]))) PowerSeries.le_order_smul
  · apply PowerSeries.Summable.increase_order fun b => by
      rw [PowerSeries.expand_smul]
      refine .trans ?_ PowerSeries.le_order_smul
      rw [PowerSeries.order_expand]
      refine .trans (le_self_nsmul (b.cast_nonneg') (q_pow_neZero hq))
        (nsmul_le_nsmul_right (order_G_pow b) (q ^ i))
  · exact PowerSeries.Summable.increase_order fun n =>
      .trans (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_G ..)) PowerSeries.le_order_smul
  · intro b hb
    simp at hb
    apply PowerSeries.coeff_of_lt_order
    refine (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp (.trans (by norm_cast) (le_order_aux₂ b))
  · intro b hb
    simp only [mem_range, not_lt] at hb
    apply PowerSeries.coeff_of_lt_order
    refine (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp (.trans ?_ PowerSeries.le_order_smul)
    refine .trans ?_ (PowerSeries.le_order_map _)
    exact .trans (by norm_cast) (le_order_aux₁ b)
  · exact PowerSeries.Summable.increase_order fun b => le_order_aux₂ b
  · -- summable
    apply PowerSeries.Summable.increase_order
    intro b
    refine .trans (.trans ?_ (PowerSeries.le_order_map _)) PowerSeries.le_order_smul
    exact le_order_aux₁ b

include hs a_congr hp_mem hs₁ hs₂ in
lemma coeff_g_G_mem [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0) {n : ℕ}:
    let f_g' := RecurFun ht hq σ s hg'
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    (h_ind : ∀ m < n, (PowerSeries.coeff m) G ∈ R) → PowerSeries.coeff n (g.subst G) ∈ R := by
  intro f_g' G h_ind
  obtain h := coeff_g_G_mem_aux ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hg' hs0 h_ind
  ring_nf at h
  rw [map_sub] at h
  rw [← sub_add_cancel ((PowerSeries.coeff n) (PowerSeries.subst G g))
    ((PowerSeries.coeff n) ((PowerSeries.map R.subtype) g'))]
  exact Subring.add_mem R h (by simp)

open PowerSeries in
lemma HasSubst.G : HasSubst ((inv_RecurFun ht hq σ s hg hg_unit).subst (RecurFun ht hq σ s hg')) :=
  .of_constantCoeff_zero (constantCoeff_G ..)

lemma G_coeff_mem_ind [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    {n: ℕ} :
    let f_g' := (RecurFun ht hq σ s hg')
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    (h_ind : ∀ m < n, (PowerSeries.coeff m) G ∈ R) →
    (g.coeff 1) * PowerSeries.coeff n G - PowerSeries.coeff n (g.subst G) ∈ R := by
  intro f_g' G h_ind
  obtain h₁ := PowerSeries.coeff_subst_finite' (HasSubst.G ht hq σ s hg hg_unit hg') g n
  rw [PowerSeries.coeff_subst' (HasSubst.G ..), finsum_eq_sum _ h₁]
  have eq_aux : ↑(g.coeff 1) * (PowerSeries.coeff n G) =
    ∑ i ∈ h₁.toFinset, if i = 1 then ↑(g.coeff 1) * PowerSeries.coeff n G else 0 := by
    by_cases hd : PowerSeries.coeff n G = 0
    · simp [hd]
    refine Eq.symm <| sum_eq_single 1 (fun b _ hb' => if_neg hb') (by simp; tauto)
  rw [eq_aux, ←sum_sub_distrib]
  apply Subring.sum_mem R
  intro i hi
  by_cases hi₀ : i = 0
  · simp [hi₀, hg]
  by_cases hi' : i = 1
  · simp [hi', Subring.smul_def, f_g', G]
  · simp only [if_neg hi', Subring.smul_def, smul_eq_mul, zero_sub, neg_mem_iff]
    refine Subring.mul_mem R (SetLike.coe_mem _) ?_
    rw [PowerSeries.coeff_pow]
    refine Subring.sum_mem R <| fun l hl => by
      by_cases h_neZero : ∃ j ∈ range i, l j = 0
      · obtain ⟨j, hj, hj'⟩ := h_neZero
        have eq_zero : ∏ i ∈ range i, PowerSeries.coeff (l i) G = 0 := by
          refine prod_eq_zero hj ?_
          simpa [hj'] using constantCoeff_G ..
        exact eq_zero ▸ R.zero_mem
      simp only [not_exists, not_and] at h_neZero
      have aux : ∀ t ∈ range i, 0 ≤ (l t) := fun t ht => by simp
      refine Subring.prod_mem R <| fun j hj => by
        simp only [mem_finsuppAntidiag] at hl
        by_cases hlj : (l j) < n
        · exact h_ind _ hlj
        have neq_aux : ∀ b ∈ range i, b ≠ j → l b = 0 := by
          intro b hb hb'
          by_contra hc
          have hlb : (l b) ≥ 1 := by
            refine Nat.one_le_iff_ne_zero.mpr ?_
            by_contra hc'
            exact h_neZero b hb hc'
          have contra_aux : ∑ s ∈ range i, (l s) ≥ (l b) + (l j) :=
            add_le_sum aux hb hj hb'
          linarith
        have i_ge : 2 ≤ i := by omega
        have exist_b : ∃ b ∈ range i, b ≠ j := by
          by_cases hj₀ : j = 0
          · use 1; simpa [hj₀]
          use 0
          simp only [mem_range, ne_eq, Ne.symm hj₀, not_false_eq_true, and_true]
          linarith
        obtain ⟨b, hb, hb'⟩ := exist_b
        exfalso
        exact (h_neZero b hb) (neq_aux b hb hb')

include hs a_congr hp_mem hs₁ hs₂ in
/-- functional equaltion lemma II: let `g'` be another power series with coefficient in `R`,
then the coefficient of $f_g^{-1} (f_{g'} (X)) are all in `R`$. -/
lemma coeff_inv_RecurFun_g'_mem_Subring [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) :
    let f_g' := (RecurFun ht hq σ s hg')
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    ∀ n, PowerSeries.coeff n G ∈ R := by
  intro f_g' G n
  induction n using Nat.strongRecOn with
  | ind k hk =>
    have eq_aux : PowerSeries.coeff k G = hg_unit.unit⁻¹ *
      ↑(g.coeff 1) * PowerSeries.coeff k G := by
      norm_cast; simp [IsUnit.val_inv_mul hg_unit]
    rw [eq_aux, mul_assoc]
    exact Subring.mul_mem R (SetLike.coe_mem _) <| by
      simpa using (Subring.add_mem _ (G_coeff_mem_ind ht hq σ s hg hg_unit hg' hk)
        (coeff_g_G_mem ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hg' hs0 hk))

end PartII

section PartIII

lemma PartIII.tsum_eq_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    {h : PowerSeries R} (h₀ : h.constantCoeff = 0) {i : ℕ}:
    let f := (RecurFun ht hq σ s hg)
    let f₁ : PowerSeries K := f.subst (h.map R.subtype)
    (f₁.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i) =
      ∑' n, (σ ^ i) (f.coeff n) • ((h.expand (q^i) (q_pow_neZero hq)).map
        ((σ ^ i).comp R.subtype)) ^ n := by
  intro f f₁
  have f_def : f = RecurFun ht hq σ s hg := rfl
  have f₁_def : f₁ = f.subst (h.map R.subtype) := rfl
  rw [PowerSeries.map_expand, PowerSeries.map, PowerSeries.map_subst _ ,
    PowerSeries.expand, PowerSeries.expand_subst _, PowerSeries.subst_express_as_tsum]
  apply tsum_congr
  intro j
  rw [PowerSeries.coeff_map, PowerSeries.map_expand]
  rfl
  · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    erw [PowerSeries.constantCoeff_expand, PowerSeries.constantCoeff_map]
    simp [h₀]
  · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    erw [PowerSeries.constantCoeff_map]
    simp [h₀]
  · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    simp [h₀]

lemma PartIII.tsum_eq_aux₁ [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    {h : PowerSeries R} (h₀ : h.constantCoeff = 0) {i : ℕ}:
    let f := (RecurFun ht hq σ s hg)
    let f₁ : PowerSeries K := f.subst (h.map R.subtype)
    f₁.expand (q ^ i) (q_pow_neZero hq) =
      ∑' n, (f.coeff n) • ((h.expand (q^i) (q_pow_neZero hq)).map (R.subtype)) ^ n := by
  intro f f₁
  rw [PowerSeries.expand, PowerSeries.expand_subst _, PowerSeries.subst_express_as_tsum]
  apply tsum_congr
  intro j
  rw [PowerSeries.map_expand]
  rfl
  · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    erw [PowerSeries.constantCoeff_expand]
    simp [h₀]
  · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    simp [h₀]

lemma PartIII.tsum_eq_aux₂ [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    {h : PowerSeries R} (h₀ : h.constantCoeff = 0) (i: ℕ) :
    let f := (RecurFun ht hq σ s hg)
    ((f.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i)).subst (h.map R.subtype) =
    ∑' n, (σ ^ i) (f.coeff n) • h.map (R.subtype) ^ (q ^ i * n) := by
  intro f
  have has_subst_h : PowerSeries.HasSubst (h.map R.subtype) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [h₀])
  rw [PowerSeries.map_expand, PowerSeries.expand_apply, PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.X_pow (q_pow_neZero hq)) has_subst_h,
    PowerSeries.subst_express_as_tsum]
  apply tsum_congr
  intro b
  rw [PowerSeries.coeff_map, PowerSeries.subst_pow has_subst_h,
    PowerSeries.subst_X has_subst_h, pow_mul]
  · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    apply PowerSeries.constantCoeff_subst_eq_zero
    simp [h₀]
    simp [zero_pow (q_pow_neZero hq)]

include ht hs a_congr hp_mem in
lemma PartIII.coeff_mem_aux {i b n : ℕ} {h : PowerSeries R} :
    (σ ^ i) ((PowerSeries.coeff n) ((PowerSeries.map R.subtype) ((PowerSeries.expand (q ^ i)
      (q_pow_neZero hq)) h) ^ b)) - (PowerSeries.coeff n) ((PowerSeries.map R.subtype)
      h ^ (q ^ i * b)) ∈ ⇑R.subtype '' ↑(I ^ (multiplicity q b + 1)) := by
  simp_rw [← map_pow, PowerSeries.coeff_map]
  rw [Subring.subtype_apply, Subring.subtype_apply]
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd q b
  obtain ⟨x, hx₁, hx₂⟩ := pow_ModEq ht hq σ hs a_congr hp_mem h i hm
    (Finsupp.single () n)
  use x
  rw [SetLike.mem_coe] at hx₁
  simp only [SetLike.mem_coe, hx₁, hx₂, ← map_expand, map_pow, MvPowerSeries.map_map,
    PowerSeries.coeff_coe, map_sub, RingHom.coe_pow, true_and]
  rw [← map_pow, ← map_pow,← map_pow ((MvPowerSeries.map R.subtype))]
  erw [PowerSeries.coeff_map, PowerSeries.coeff_map]
  simp [PowerSeries.expand]

include hs a_congr hp_mem hs₁ hs₂ in
lemma PartIII.coeff_tsum_mem [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    {h : PowerSeries R} (h₀ : h.constantCoeff = 0) (n : ℕ) (hs₀ : s 0 = 0):
    let f := (RecurFun ht hq σ s hg)
    let f₁ : PowerSeries K := f.subst (h.map R.subtype)
    PowerSeries.coeff n (∑' i, s i • (f₁.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i)
      - ∑' i, s i • ((f.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i)).subst (h.map R.subtype)) ∈ R := by
  intro f f'
  have le_order_aux₁ (i b : ℕ) : b ≤ PowerSeries.order
    ((PowerSeries.map R.subtype) ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) h) ^ b) := by
    rw [← map_pow]
    refine .trans (.trans (le_refl _) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ?_)) (PowerSeries.le_order_map _)
    rw [PowerSeries.constantCoeff_expand, h₀]
  have le_order_aux₂ (i b : ℕ) : b ≤ PowerSeries.order
    ((PowerSeries.map R.subtype) h ^ (q ^ i * b)) := by
    rw [← map_pow]
    have le_aux : b ≤ q ^ i * b :=
      Nat.le_mul_of_pos_left b <|  Nat.pow_pos (Nat.pos_of_ne_zero (q_neZero hq))
    refine .trans (.trans (by norm_cast) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ h₀))
      (PowerSeries.le_order_map _)
  have le_expand_aux (b : ℕ) {f : PowerSeries K} (hf : f.constantCoeff = 0) :
    ↑b ≤ ((PowerSeries.expand (q ^ b) (q_pow_neZero hq)) f).order := by
    rw [PowerSeries.order_expand]
    exact .trans (by simp) (smul_le_smul (Nat.lt_pow_self (one_lt_q ht hq)).le
      (PowerSeries.one_le_order hf) b.zero_le (zero_le _))
  have le_order_aux₃ (b : ℕ) : b ≤ PowerSeries.order (PowerSeries.subst ((PowerSeries.map
    R.subtype) h) (((f.expand (q ^ b) (q_pow_neZero hq)).map (σ ^ b)))) := by
    have : ((PowerSeries.map R.subtype) h).order * ((PowerSeries.map (σ ^ b))
      ((PowerSeries.expand (q ^ b) (q_pow_neZero hq)) f)).order ≤ PowerSeries.order
      (PowerSeries.subst ((PowerSeries.map R.subtype) h) ((PowerSeries.map (σ ^ b))
      ((PowerSeries.expand (q ^ b) (q_pow_neZero hq)) f))) := by
      conv_rhs => rw [PowerSeries.order_eq_order]
      rw [PowerSeries.order_eq_order]
      exact PowerSeries.le_order_subst _
        (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [h₀])) _
    have le_aux : b ≤ ((PowerSeries.map (σ ^ b)) ((PowerSeries.expand (q ^ b)
      (q_pow_neZero hq)) f)).order := by
      refine .trans ?_ (PowerSeries.le_order_map _)
      exact le_expand_aux b (constantCoeff_RecurFun ..)
    exact .trans (.trans (by simp) (mul_le_mul (PowerSeries.one_le_order (by simp [h₀]))
      le_aux b.cast_nonneg' (zero_le _))) this
  have le_order_aux₄ (b : ℕ) : b ≤ PowerSeries.order ((PowerSeries.map (σ ^ b))
    ((PowerSeries.expand (q ^ b) (q_pow_neZero hq)) f')) := by
    refine .trans (le_expand_aux b <| PowerSeries.constantCoeff_subst_eq_zero (by simp [h₀]) _
      <| constantCoeff_RecurFun ..) (PowerSeries.le_order_map _)
  rw [map_sub, Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n),
    Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n),
    tsum_eq_sum (s := range (n + 1)), tsum_eq_sum (s := range (n + 1)), ← sum_sub_distrib]
  refine Subring.sum_mem R ?_
  intro i hi
  by_cases hi₀ : i = 0
  · simp [hi₀, hs₀]
  simp_rw [PowerSeries.coeff_smul, smul_eq_mul, ← mul_sub]
  refine hs₁ i _ ?_
  rw [PowerSeries.coeff_map, PartIII.tsum_eq_aux₁ ht hq σ s hg h₀,
    PartIII.tsum_eq_aux₂ ht hq σ s hg h₀ i,
    Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n),
    Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n),
    tsum_eq_sum (s := range (n + 1)), tsum_eq_sum (s := range (n + 1)), map_sum, ← sum_sub_distrib]
  apply mem_ideal_aux
  intro b hb
  simp_rw [PowerSeries.coeff_smul, smul_eq_mul, map_mul, ← mul_sub]
  refine refinement_hs₂ σ hs₂ i (multiplicity q b + 1) _ ?_ _
    (PartIII.coeff_mem_aux ht hq σ hs a_congr hp_mem)
  · intro a ha
    have a_mem : ⟨a, image_of_incl_mem a ha⟩ ∈ I ^ (multiplicity q b + 1) := by
      obtain ⟨a', ha'₁, ha'₂⟩ := ha
      simp_rw [← ha'₂]
      simpa using ha'₁
    obtain h1 := coeff_RecurFun_mul_mem_i ht hq σ s hs₁ hs₂ hg b 1 _ a_mem
    simpa using h1
  · intro b hb
    simp only [mem_range, not_lt] at hb
    refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp
      <| .trans (.trans (by norm_cast) (le_order_aux₂ _ _)) PowerSeries.le_order_smul
  · intro b hb
    simp only [mem_range, not_lt] at hb
    refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp
      <| .trans (.trans (by norm_cast) (le_order_aux₁ _ _)) PowerSeries.le_order_smul
  · exact PowerSeries.Summable.increase_order fun b =>
      .trans (.trans (by norm_cast) (le_order_aux₂ _ _)) PowerSeries.le_order_smul
  · exact PowerSeries.Summable.increase_order fun b =>
      .trans (.trans (by norm_cast) (le_order_aux₁ _ _)) PowerSeries.le_order_smul
  · intro b hb
    simp only [mem_range, not_lt] at hb
    refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp
      <| .trans (.trans (by norm_cast) (le_order_aux₃ _)) PowerSeries.le_order_smul
  · intro b hb
    simp only [mem_range, not_lt] at hb
    refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp
      <| .trans (.trans (by norm_cast) (le_order_aux₄ _)) PowerSeries.le_order_smul
  · exact PowerSeries.Summable.increase_order fun b =>
      .trans (.trans (by norm_cast) (le_order_aux₃ _)) PowerSeries.le_order_smul
  · exact PowerSeries.Summable.increase_order fun b =>
      .trans (.trans (by norm_cast) (le_order_aux₄ _)) PowerSeries.le_order_smul

/- functional equaltion lemma III: let `h` be another power series with coefficient in `R`,
  then there exist a power series `h₁` over `R` such that `f(h(X)) = f_{h₁}(X)`, this is
  equivalent to say that `f₁(X) - ∑s_i σ^i(f₁(X^{q^i}))` is a power series in `R`, where
  `f₁(X) := f(h(X))` and `f(X) := f_g(X)` -/
include hs a_congr hp_mem hs₁ hs₂ in
lemma coeff_inv_RecurFun_g'_mem_Subring' [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs₀ : s 0 = 0) {h : PowerSeries R} (h₀ : h.constantCoeff = 0):
    let f := (RecurFun ht hq σ s hg)
    let f₁ : PowerSeries K := f.subst (h.map R.subtype)
    ∀ n, (f₁ - ∑' i, (s i) • (f₁.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i)).coeff n ∈ R := by
  intro f f₁ n
  have has_subst_h : PowerSeries.HasSubst ((PowerSeries.map R.subtype) h) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [h₀])
  have eq_aux : f₁ - ∑' i, (s i) • (f₁.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i) =
    (f₁ - ∑' i, s i • ((f.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i)).subst (h.map R.subtype)) - (∑' i, s i • (f₁.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i)
    - ∑' i, s i • ((f.expand (q ^ i) (q_pow_neZero hq)).map (σ ^ i)).subst (h.map R.subtype))
    := by ring
  rw [eq_aux, map_sub]
  refine Subring.sub_mem R ?_ (PartIII.coeff_tsum_mem ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg h₀ n hs₀)
  have eq_aux₁ : (f₁ - ∑' (i : ℕ), s i • PowerSeries.subst ((PowerSeries.map R.subtype) h)
    ((PowerSeries.map (σ ^ i)) ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) f))) =
    (g.map (R.subtype)).subst (h.map (R.subtype)) := by
    have : g.map (R.subtype) = f - ∑' (i : ℕ), s i • (PowerSeries.map (σ ^ i))
      ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) f) := by
      unfold f
      nth_rw 1 [FunEq_of_RecurFun ht hq σ s hg hs₀]
      ring
    rw [this, PowerSeries.subst_sub has_subst_h, tsum_subst _ has_subst_h]
    congr
    funext i
    rw [PowerSeries.subst_smul has_subst_h]
    · apply PowerSeries.Summable.increase_order
      intro n
      have le_expand_aux (b : ℕ) {f : PowerSeries K} (hf : f.constantCoeff = 0) :
        ↑b ≤ ((PowerSeries.expand (q ^ b) (q_pow_neZero hq)) f).order := by
        rw [PowerSeries.order_expand]
        exact .trans (by simp) (smul_le_smul (Nat.lt_pow_self (one_lt_q ht hq)).le
          (PowerSeries.one_le_order hf) b.zero_le (zero_le _))
      refine .trans (.trans (le_expand_aux n (constantCoeff_RecurFun ..))
        (PowerSeries.le_order_map _)) PowerSeries.le_order_smul
  rw [eq_aux₁]
  have eq_aux₂ : (PowerSeries.coeff n) (PowerSeries.subst ((PowerSeries.map R.subtype) h)
    (g.map (R.subtype))) = PowerSeries.coeff n (g.subst h) := by
    erw [← PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h₀),
      PowerSeries.coeff_map, Subring.subtype_apply]
  rw [eq_aux₂]
  exact SetLike.coe_mem _

end PartIII

section PartIV

/- also could generalize to the theorem above. name : `mem_ideal_aux`-/
lemma mem_ideal_aux' {m r: ℕ} {α : ℕ → K} (h : ∀ i ∈ range m, α i ∈ ⇑(algebraMap (↥R) K) '' ↑(I ^ r)) :
    ∑ i ∈ range m, α i ∈ ⇑(algebraMap (↥R) K) '' ↑(I ^ r) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [range_add_one, sum_insert (by simp)]
    specialize ih fun i hi => h i (mem_range.mpr (by nlinarith [mem_range.mp hi]))
    specialize h k (self_mem_range_succ k)
    simp at h ⊢ ih
    obtain ⟨a, ha₀, ha₁, ha₂⟩ := ih
    obtain ⟨b, hb₀, hb₁, hb₂⟩ := h
    have : (⟨a + b, Subring.add_mem R ha₀ hb₀⟩ : R) = ⟨a, ha₀⟩ + ⟨b, hb₀⟩ := rfl
    use (a + b), Subring.add_mem R ha₀ hb₀, ((Submodule.add_mem_iff_right _ ha₁).mpr hb₁)
    rw [←hb₂, ←ha₂, this, map_add]
    ring_nf

lemma mem_ideal_aux₂ {α : Type*} {s : Finset α} {r : ℕ} {f : α → K}
     : (h : ∀ i ∈ s, f i ∈ R.subtype '' ↑(I ^ r)) →
    ∑ i ∈ s, f i ∈ R.subtype '' ↑(I ^ r) := by
  refine Finset.induction (by simp) ?_ s
  intro a s' hs' ih ih'
  have a_mem : a ∈ insert a s' := mem_insert_self a s'
  obtain ⟨x, hx₁, hx₂⟩ := ih fun i hi => ih' _ (mem_insert_of_mem hi)
  obtain ⟨y, hy₁, hy₂⟩ := ih' _ (mem_insert_self a s')
  rw [sum_insert hs', ← hx₂, ← hy₂]
  use y + x
  simpa using (Submodule.add_mem_iff_right _ hy₁).mpr hx₁


include hp_mem hs₁ hs₂ in
theorem congr_equiv_forward₀ [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    {α : PowerSeries R} {β : PowerSeries K} (hα : α.constantCoeff = 0) (hβ : β.constantCoeff = 0)
    {r : ℕ} (hr : 1 ≤ r):
    let f := RecurFun ht hq σ s hg
    (∀ n, α.coeff n - β.coeff n ∈ R.subtype '' ↑(I ^ r)) →
      (∀ n, PowerSeries.coeff n (f.subst (α.map R.subtype)) - PowerSeries.coeff n (f.subst β)
        ∈ R.subtype '' ↑(I ^ r)) := by
  intro f h_congr n
  have has_subst_α : PowerSeries.HasSubst ((PowerSeries.map R.subtype) α) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    simp [hα]
  have has_subst_β : PowerSeries.HasSubst β := PowerSeries.HasSubst.of_constantCoeff_zero' hβ
  have le_order_aux₁ (b : ℕ) : b ≤ ((f.coeff b) • β ^ b).order :=
    .trans (.trans (le_refl _) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hβ)) PowerSeries.le_order_smul
  have le_order_aux₂ (b : ℕ) : b ≤ ((f.coeff b) • (α.map R.subtype) ^ b).order :=
    .trans (.trans (le_refl _) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (by simp [hα])))
      PowerSeries.le_order_smul
  rw [PowerSeries.subst_express_as_tsum _ has_subst_α, PowerSeries.subst_express_as_tsum _ has_subst_β,
    Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n),
    Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K n),
    tsum_eq_sum (s := range (n + 1)), tsum_eq_sum (s := range (n + 1)), ← sum_sub_distrib]
  apply mem_ideal_aux'
  intro i hi
  simp_rw [PowerSeries.coeff_smul, smul_eq_mul, ← mul_sub]
  /- now only need to prove that α^i ≡ β^i (mod I ^ (r + multiplicity q i)) and use the
  first technical lemma -/
  have coeff_β_mem_R : ∀ n, β.coeff n ∈ R := by
    intro n
    have eq_aux : β.coeff n = - (↑(α.coeff n) - β.coeff n) + α.coeff n := by ring
    rw [eq_aux]
    refine Subring.add_mem _ (R.neg_mem (image_of_incl_mem _ (h_congr n))) (SetLike.coe_mem _)
  let β' : PowerSeries R := β.toSubring _ coeff_β_mem_R
  have coeff_β'_apply : ∀ n, β'.coeff n = β.coeff n := fun n => β.coeff_toSubring _ _
  have α_congr_β' : α ≡ β' [SMOD (I ^ r).MvPowerSeries] := by
    refine SModEq.sub_mem.mpr ?_
    intro d
    simp [← coeff_β'_apply] at h_congr
    obtain ⟨x, hx₁⟩ := h_congr (d ())
    have eq_aux : (coeff d) (α - β') = α.coeff (d ()) - β'.coeff (d ()) := by
      rw [PowerSeries.coeff_def rfl]
      rfl
    rw [eq_aux]
    exact hx₁
  obtain aux := congr_pow_mod_add' ht hq hp_mem i hr α_congr_β'
  have mem_aux : ((PowerSeries.coeff n) ((PowerSeries.map R.subtype) α ^ i) -
    (PowerSeries.coeff n) (β ^ i)) ∈ R.subtype '' ↑(I ^ (multiplicity q i + r)) := by
    /- here need to use the same strategy as in the second technical lemma-/
    rw [add_comm _ r]
    obtain hx := SModEq.sub_mem.mp aux (Finsupp.single () n)
    have eq_aux : (α ^ i - β' ^ i) (Finsupp.single () n) = (α ^ i - β' ^ i).coeff n := rfl
    use (α ^ i - β' ^ i).coeff n
    refine ⟨hx, ?_⟩
    simp only [map_sub, Subring.subtype_apply]
    congr
    · rw [← map_pow, PowerSeries.coeff_map, Subring.subtype_apply]
    · simp [PowerSeries.coeff_pow, β']
  have mem_aux' : ⟨_, image_of_incl_mem _ mem_aux⟩ ∈ (I ^ ( multiplicity q i + r)) := by
    obtain ⟨a, ha₁, ha₂⟩ := mem_aux
    simp_rw [← ha₂]
    exact ha₁
  obtain h1 := coeff_RecurFun_mul_mem_i ht hq σ s hs₁ hs₂ hg i r ⟨_, image_of_incl_mem _ mem_aux⟩ mem_aux'
  simp only [Subring.subtype_apply, Set.mem_image, SetLike.mem_coe, Subtype.exists,
    exists_and_right, exists_eq_right] at h1
  obtain ⟨ha₁, ha₂⟩ := h1
  simpa using ⟨_ , ⟨ha₁, ⟨ha₂, rfl⟩⟩⟩
  · intro b hb
    simp only [mem_range, not_lt] at hb
    refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top _)).mp
      <| (.trans (by norm_cast) (le_order_aux₁ _))
  · intro b hb
    simp only [mem_range, not_lt] at hb
    refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top _)).mp
      <| (.trans (by norm_cast) (le_order_aux₂ _))
  · exact PowerSeries.Summable.increase_order fun n => (le_order_aux₁ n)
  · exact PowerSeries.Summable.increase_order fun n => (le_order_aux₂ n)

lemma coeff_pow_mem_ind {γ : PowerSeries K} (k i r : ℕ) (h_le : 2 ≤ i)
    (hγ : γ.constantCoeff = 0) :
    (∀ m < k, γ.coeff m ∈ R.subtype '' ↑(I ^ r)) →
    (γ ^ i).coeff k ∈ R.subtype '' ↑(I ^ r):= by
  intro ih
  have h : ∀ m ≤ k, (γ ^ i).coeff m ∈ R.subtype '' ↑(I ^ r) := by
    induction i, h_le using Nat.le_induction with
    | base =>
      intro m hm
      rw [pow_two, PowerSeries.coeff_mul]
      apply mem_ideal_aux₂
      intro l hl
      simp only [mem_antidiagonal] at hl
      by_cases hl₁ : l.1 = 0
      · simp [hl₁, hγ]
      by_cases hl₁' : l.1 = k
      · have eq_aux : l.2 = 0 := by linarith
        simp [eq_aux, hγ]
      have lt_aux₁ : l.1 < k := by omega
      have lt_aux₂ : l.2 < k := by omega
      use ⟨_, image_of_incl_mem _ (ih l.1 lt_aux₁)⟩ * ⟨_, image_of_incl_mem _ (ih _ lt_aux₂)⟩
      refine ⟨Ideal.mul_mem_left _ _ ?_ , by simp⟩
      obtain ⟨x, hx₁, hx₂⟩ := ih _ lt_aux₂
      simpa [← hx₂]
    | succ j hj hj_mem =>
      intro m hm
      rw [pow_succ, PowerSeries.coeff_mul]
      apply mem_ideal_aux₂
      intro l hl
      simp only [mem_antidiagonal] at hl
      by_cases hl₁ : l.2 = k
      · have eq_aux : l.1 = 0 := by omega
        have j_ne : j ≠ 0 := Nat.ne_zero_of_lt hj
        have eq_aux₂ : (PowerSeries.coeff l.1) (γ ^ j) = 0 := by
          simp [eq_aux, map_pow, hγ, zero_pow (Nat.ne_zero_of_lt hj)]
        simp [eq_aux₂]
      have lt_aux : l.2 < k := by omega
      refine ⟨⟨_, image_of_incl_mem _ (hj_mem l.1 (by linarith))⟩ *
        ⟨_, image_of_incl_mem _ (ih _ lt_aux)⟩, Ideal.mul_mem_right _ _ ?_, by simp⟩
      obtain ⟨x, hx₁, hx₂⟩ := hj_mem l.1 (by linarith)
      simpa [← hx₂]
  exact h _ (le_refl _)

lemma coeff_pow_eq_ind {α : PowerSeries K} {β : PowerSeries R} {k i: ℕ} (hi : 2 ≤ i)
    (hα : α.constantCoeff = 0) (hβ : β.constantCoeff = 0) :
    (∀ n < k, α.coeff n = β.coeff n) →  ∀ n ≤ k, (α ^ i).coeff n = (β ^ i).coeff n := by
  intro h_ind
  induction i, hi using Nat.le_induction with
  | base =>
    intro n hn
    simp only [pow_two, PowerSeries.coeff_mul, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]
    rw [sum_congr rfl]
    intro l hl
    simp only [mem_antidiagonal] at hl
    by_cases hl₁ : l.1 = 0
    · simp [hl₁, hα, hβ]
    by_cases hl₂ : l.2 = 0
    · simp [hl₂, hα, hβ]
    rw [h_ind _ (by omega), h_ind _ (by omega)]
  | succ m hm ih =>
    intro n hn
    simp only [pow_succ, PowerSeries.coeff_mul, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]
    rw [sum_congr rfl]
    intro l hl
    simp only [mem_antidiagonal] at hl
    by_cases hl₁ : l.1 = 0
    · simp [hl₁, map_pow, hα, hβ, zero_pow (Nat.ne_zero_of_lt hm)]
    rw [ih l.1 (by linarith), h_ind _ (by omega)]

include ht hq hp_mem in
lemma coeff_pow_mem_ind₁ {γ : PowerSeries K} (hγ : γ.constantCoeff = 0) (k i r j : ℕ)
    (hj : j ≠ 0) (i_ne : i ≠ 0)
    (hr : 1 ≤ r) : (h_ind : ∀ m < k, γ.coeff m ∈ R.subtype '' ↑(I ^ r)) →
    (((γ ^ q ^ i) ^ j).coeff k) ∈ R.subtype '' ↑(I ^ (multiplicity q j + (r + 1))) := by
  intro h_ind
  let γ_aux := (γ.trunc k).toPowerSeries
  have coeff_γ_aux_mem : ∀ n, γ_aux.coeff n ∈ R := by
    intro n
    by_cases hn_lt : n < k
    · simpa [γ_aux, PowerSeries.coeff_trunc, if_pos hn_lt] using
        image_of_incl_mem _ (h_ind n hn_lt)
    simp [γ_aux, PowerSeries.coeff_trunc, if_neg hn_lt]
  let γ' := γ_aux.toSubring _ coeff_γ_aux_mem
  have eq_aux : ∀ n < k,  γ.coeff n = γ'.coeff n := by
    intro n hn
    simp [γ', γ_aux]
    rw [PowerSeries.coeff_trunc, if_pos hn]
  have coeff_eq : ∀ n, (hn_lt : n < k) →
    γ'.coeff n = ⟨γ.coeff n, image_of_incl_mem _ (h_ind n hn_lt)⟩ := by
    intro n hn_lt
    simp [eq_aux _ hn_lt]
  have coeff_eq' : ∀ n, ¬ n < k → γ'.coeff n = 0 := by
    intro n hn
    have eq_aux : γ'.coeff n = (0 : K) := by simp [γ', γ_aux, PowerSeries.coeff_trunc, if_neg hn]
    norm_cast at eq_aux
  have γ'_congr : γ' ≡ 0 [SMOD (I ^ r).MvPowerSeries] := by
    refine SModEq.sub_mem.mpr ?_
    intro n
    have eq_aux : (coeff n) (γ' - 0) = γ'.coeff (n ()) := by
      rw [sub_zero, PowerSeries.coeff_def rfl, coeff_apply]
    rw [sub_zero, ← PowerSeries.coeff_def rfl]
    by_cases hn : n () < k
    · rw [coeff_eq _ hn]
      obtain ⟨x, hx₁, hx₂⟩ := h_ind _ hn
      simpa [← hx₂]
    simp [coeff_eq' _ hn]
  have constantCoeff_γ' : γ'.constantCoeff = 0 := by
    have : γ'.constantCoeff = (0 : K) := by
      by_cases hk : 0 < k
      · rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← eq_aux _ hk,
          PowerSeries.coeff_zero_eq_constantCoeff, hγ]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_eq' _ hk, ZeroMemClass.coe_zero R]
    norm_cast at this
  have coeff_eq_aux : ((γ ^ q ^ i) ^ j).coeff k = ((γ' ^ q ^ i) ^ j).coeff k := by
    rw [← pow_mul, ← pow_mul]
    have le_aux : 2 ≤ q ^ i * j :=
      le_mul_of_le_of_one_le (two_le_q_pow ht hq i_ne) (Nat.one_le_iff_ne_zero.mpr hj)
    exact coeff_pow_eq_ind le_aux hγ constantCoeff_γ'
      eq_aux k (le_refl _)
  simp only [Subring.subtype_apply, coeff_eq_aux, Set.mem_image, SetLike.mem_coe,
    SetLike.coe_eq_coe, exists_eq_right]
  rw [← pow_mul]
  have neq : (q ^ i * j) ≠ 0 := mul_ne_zero (q_pow_neZero hq) hj
  obtain h_congr := congr_pow_mod_add' ht hq hp_mem (q ^ i * j) hr γ'_congr
  have le_aux : i + multiplicity q j ≤ multiplicity q (q ^ i * j) := by
    refine (FiniteMultiplicity.pow_dvd_iff_le_multiplicity (Nat.finiteMultiplicity_iff.mpr
      ⟨q_neOne ht hq, Nat.zero_lt_of_ne_zero neq⟩)).mp ?_
    rw [pow_add]
    exact Nat.mul_dvd_mul_left _ (pow_multiplicity_dvd q j)
  rw [zero_pow neq] at h_congr
  have le_aux' : multiplicity q j + (r + 1) ≤ (r + multiplicity q (q ^ i * j)) := by omega
  obtain h_mem := SModEq.sub_mem.mp h_congr (Finsupp.single () k)
  rw [sub_zero] at h_mem
  have eq_aux : (PowerSeries.coeff k) (γ' ^ (q ^ i * j)) =
    (γ' ^ (q ^ i * j)) (Finsupp.single () k) := by
    rw [PowerSeries.coeff]
    rfl
  rw [eq_aux]
  exact Ideal.pow_le_pow_right le_aux' h_mem

lemma PowerSeries.subst_expand_pow {α β : PowerSeries K} (hβ : β.constantCoeff = 0)
    (i : ℕ) :
    (α.expand (q ^ i) (q_pow_neZero hq)).subst β =  α.subst (β ^ q ^ i) := by
    obtain h := HasSubst.of_constantCoeff_zero' hβ
    rw [expand_apply, subst_comp_subst_apply (HasSubst.X_pow (q_pow_neZero hq)) h,
      subst_pow h, subst_X h]

include hp_mem hs₁ hs₂ in
theorem congr_equiv_backward_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs₀ : s 0 = 0) {α : PowerSeries K} (hα : α.constantCoeff = 0) {r : ℕ} (hr : 1 ≤ r) :
    let f_inv := inv_RecurFun ht hq σ s hg hg_unit
    (∀ n, α.coeff n ∈ R.subtype '' ↑(I ^ r)) →
      ∀ n, PowerSeries.coeff n (f_inv.subst α)
        ∈ R.subtype '' ↑(I ^ r) := by
  intro f_inv h n
  let f := RecurFun ht hq σ s hg
  let γ : PowerSeries K := f_inv.subst α
  let b₁ := g.coeff 1
  obtain has_subst_α := PowerSeries.HasSubst.of_constantCoeff_zero' hα
  have has_subst_f_inv : PowerSeries.HasSubst f_inv :=
    PowerSeries.HasSubst.of_constantCoeff_zero' rfl
  have constantCoeff_γ : γ.constantCoeff = 0 := by
    rw [PowerSeries.constantCoeff, PowerSeries.constantCoeff_subst_eq_zero hα _ rfl]
  have has_subst_γ : PowerSeries.HasSubst γ := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_γ
  have has_subst_γ_pow {i : ℕ} : PowerSeries.HasSubst (γ ^ q ^ i) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    rw [map_pow, constantCoeff_γ, zero_pow (q_pow_neZero hq)]
  have eq_aux₀ : α = f.subst γ := by
    rw [← PowerSeries.subst_comp_subst_apply has_subst_f_inv has_subst_α,
      RecurFun_comp_inv_RecurFun, PowerSeries.subst_X has_subst_α]
  have eq_aux₁ : α = (g.map R.subtype).subst γ + ∑' i, s i • (f.map (σ^i)).subst (γ ^ q ^ i) := by
    rw [eq_aux₀]
    conv_lhs => unfold f; rw [FunEq_of_RecurFun ht hq σ s hg hs₀,
      PowerSeries.subst_add has_subst_γ]
    rw [tsum_subst (summable_aux ht hq σ s hg hs₀) has_subst_γ]
    congr! 3 with i
    rw [PowerSeries.map_expand, PowerSeries.subst_smul has_subst_γ,
      PowerSeries.subst_expand_pow hq constantCoeff_γ _]
  have le_order_aux₁ {b i : ℕ} : b ≤ PowerSeries.order
    ((PowerSeries.coeff b) ((PowerSeries.map (σ ^ i)) f) • (γ ^ q ^ i) ^ b) := by
    refine .trans (.trans (le_refl _) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ?_)) PowerSeries.le_order_smul
    rw [map_pow, constantCoeff_γ, zero_pow (q_pow_neZero hq)]
  have le_order_aux₂ {b : ℕ} : b ≤ PowerSeries.order (s b • PowerSeries.subst (γ ^ q ^ b)
    ((PowerSeries.map (σ ^ b)) f)) := by
    refine .trans ?_ PowerSeries.le_order_smul
    refine .trans (.trans ?_ (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ?_))
      (PowerSeries.le_order_subst_right' ?_ ?_)
    · exact_mod_cast (Nat.lt_pow_self (one_lt_q ht hq)).le
    · exact constantCoeff_γ
    · rw [map_pow, constantCoeff_γ, zero_pow (q_pow_neZero hq)]
    · rw [PowerSeries.constantCoeff_map, constantCoeff_RecurFun .., map_zero]
  induction n using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk₀ : k = 0
    · rw [hk₀,PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff,
        PowerSeries.constantCoeff_subst_eq_zero hα _ (constantCoeff_inv_RecurFun ..)]
      exact ⟨0, (by simp)⟩
    -- by_cases hk₁ : k = 1
    -- · sorry
    /- the case for 1 < k. -/
    obtain ⟨x, hx₁, hx₂⟩ : b₁ * γ.coeff k ∈ R.subtype '' ↑(I^r) := by
      have ⟨x, hx₁, hx₂⟩ : PowerSeries.coeff k ((g.map R.subtype).subst γ) -
        b₁ * γ.coeff k ∈ R.subtype '' ↑(I ^ r) := by
        obtain h₁ := PowerSeries.coeff_subst_finite' has_subst_γ (g.map R.subtype) k
        have : ↑b₁ * γ.coeff k = ∑ i ∈ h₁.toFinset, if i = 1 then b₁ * γ.coeff k else 0 := by
          rw [sum_eq_single 1 fun _ _ hb₂ => if_neg hb₂, if_pos rfl]
          simp only [PowerSeries.coeff_map, Subring.subtype_apply, smul_eq_mul,
            Set.Finite.mem_toFinset, Function.mem_support, pow_one, ne_eq, Decidable.not_not,
            ↓reduceIte]
          exact fun h => h
        rw [PowerSeries.coeff_subst' has_subst_γ, finsum_eq_sum _ h₁, this,
          ← Finset.sum_sub_distrib]
        apply mem_ideal_aux₂
        intro i hi
        by_cases hi₀ : i = 0
        · simp [hi₀, if_neg hk₀]
        by_cases hi₁ : i = 1
        · rw [hi₁, pow_one, if_pos rfl, PowerSeries.coeff_map, Subring.subtype_apply, smul_eq_mul,
            sub_self]
          exact ⟨0, by simp⟩
        rw [if_neg hi₁, sub_zero]
        have h_le : 2 ≤ i := by omega
        obtain ⟨x, hx₁, hx₂⟩ := coeff_pow_mem_ind k i r h_le constantCoeff_γ ih
        use g.coeff i * x
        refine ⟨Ideal.mul_mem_left _ _ hx₁, ?_⟩
        rw [map_mul, hx₂, smul_eq_mul, PowerSeries.coeff_map]
      obtain ⟨y, hy₁, hy₂⟩ : PowerSeries.coeff k (∑' (i : ℕ), s i • (f.map (σ ^ i)).subst
        (γ ^ q ^ i)) ∈ R.subtype '' ↑(I ^ r) := by
        /- here is hard, use Summable.map_tsum, tsum_to_finite. -/
        rw [Summable.map_tsum _ _ (PowerSeries.WithPiTopology.continuous_coeff K k),
          tsum_eq_sum (s := range (k + 1))]
        apply mem_ideal_aux₂
        intro i h
        by_cases hi₀ : i = 0
        · simp only [Subring.subtype_apply, hi₀, hs₀, pow_zero, pow_one, zero_smul, map_zero,
          Set.mem_image, SetLike.mem_coe, ZeroMemClass.coe_eq_zero, exists_eq_right, zero_mem]
        rw [PowerSeries.coeff_smul, smul_eq_mul]
        refine refinement_hs₁' s hs₁ i r _ ?_
        rw [PowerSeries.subst_express_as_tsum _ has_subst_γ_pow, Summable.map_tsum _ _
          (PowerSeries.WithPiTopology.continuous_coeff K k), tsum_eq_sum (s := range (k + 1))]
        apply mem_ideal_aux₂
        intro j hj
        by_cases hj₀ : j = 0
        · simp [hj₀, if_neg hk₀]
        rw [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_map]
        have mem_aux : (PowerSeries.coeff k) ((γ ^ q ^ i) ^ j)
          ∈ R.subtype '' ↑(I ^ (multiplicity q j + 1 + r)) := by
          have : multiplicity q j + 1 + r = multiplicity q j + r + 1 := by ring
          exact this ▸  coeff_pow_mem_ind₁ ht hq hp_mem constantCoeff_γ k i r j hj₀ hi₀ hr ih
          -- exact coeff_pow_mem_ind₁ ht hq hp_mem constantCoeff_γ k i r j hj₀ hi₀ hr ih
          /- here use the same strategy as in the first part of this lemma. -/
        have mem_aux' : ⟨_, image_of_incl_mem _ mem_aux⟩ ∈ (I ^ (multiplicity q j + (1 + r))) := by
          rw [add_assoc _ 1 r] at mem_aux
          obtain ⟨a, ha₁, ha₂⟩ := mem_aux
          simp_rw [← ha₂]
          exact ha₁
        obtain h1 := coeff_RecurFun_mul_mem_i ht hq σ s hs₁ hs₂ hg j _ _ mem_aux'
        -- ∀ x ∈ I ^ (multiplicity q j + (r + 1)), (PowerSeries.coeff j) (RecurFun ht hq σ s hg) * ↑x ∈ ⇑R.subtype '' ↑(I ^ (r + 1))
        refine refinement_hs₂' σ hs₂ i (multiplicity q j + 1) r _ ?_ _ mem_aux
        · intro a ha
          have a_mem : ⟨a, image_of_incl_mem a ha⟩ ∈ (I ^ (multiplicity q j + 1)) := by
            obtain ⟨x, hx₁, hx₂⟩ := ha
            simp_rw [← hx₂]
            simpa
          exact pow_one I ▸ coeff_RecurFun_mul_mem_i ht hq σ s hs₁ hs₂ hg j 1 _ a_mem
        /- two result about summable, use order estimate. -/
        · intro b hb
          simp only [mem_range, not_lt] at hb
          refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top _)).mp
            <| (.trans (by norm_cast) le_order_aux₁)
        · exact PowerSeries.Summable.increase_order fun n => le_order_aux₁
        /- two result about summable, use order estimate. -/
        · intro b hb
          simp only [mem_range, not_lt] at hb
          refine PowerSeries.coeff_of_lt_order _ <| (ENat.add_one_le_iff (ENat.coe_ne_top _)).mp
            <| (.trans (by norm_cast) le_order_aux₂)
        · exact PowerSeries.Summable.increase_order fun n => le_order_aux₂
      obtain ⟨z, hz₁, hz₂⟩ := h k
      refine ⟨z - x - y, ?_, ?_⟩
      · exact SetLike.mem_coe.mpr <|
        (Submodule.sub_mem_iff_left _ hy₁).mpr ((Submodule.sub_mem_iff_left _ hx₁).mpr hz₁)
      · rw [map_sub, map_sub, hx₂, hy₂, hz₂, eq_aux₁, map_add]
        ring
    use hg_unit.unit⁻¹ * x
    rw [map_mul, hx₂, ← mul_assoc]
    simp only [SetLike.mem_coe, Units.isUnit, Ideal.unit_mul_mem_iff_mem, Subring.subtype_apply]
    refine ⟨hx₁, ?_⟩
    rw [← Subring.subtype_apply, ← Subring.subtype_apply, ← map_mul,
      IsUnit.val_inv_mul hg_unit, Subring.subtype_apply, OneMemClass.coe_one, one_mul]

lemma coeff_pow_mem {f : MvPowerSeries τ K} (h : ∀ i, f.coeff i ∈ R) {n : ℕ} :
    ∀ i, (f ^ n).coeff i ∈ R :=
  fun _ => (coeff_pow f _) ▸  Subring.sum_mem _ fun l _ => Subring.prod_mem R fun c _ ↦ h (l c)

lemma PowerSeries.coeff_pow_mem {f : PowerSeries K} (h : ∀ i, f.coeff i ∈ R) {n : ℕ} :
    ∀ i, (f ^ n).coeff i ∈ R :=
  fun _ => (coeff_pow _ _ f) ▸  Subring.sum_mem _ fun l _ => Subring.prod_mem R fun c _ ↦ h (l c)

include hs a_congr hp_mem hs₁ hs₂ hg_unit in
theorem congr_equiv [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs₀ : s 0 = 0)
    {α : PowerSeries R} {β : PowerSeries K} (hα : α.constantCoeff = 0) (hβ : β.constantCoeff = 0)
    {r : ℕ} (hr : 1 ≤ r) :
    let f := RecurFun ht hq σ s hg
    (∀ n, α.coeff n - β.coeff n ∈ R.subtype '' ↑(I ^ r)) ↔
      (∀ n, PowerSeries.coeff n (f.subst (α.map R.subtype)) - PowerSeries.coeff n (f.subst β)
        ∈ R.subtype '' ↑(I ^ r)) := by
  intro f
  let F := inv_add_RecurFun ht hq σ s hg hg_unit
  let f_inv := inv_RecurFun ht hq σ s hg hg_unit
  refine ⟨congr_equiv_forward₀ ht hq σ hp_mem s hs₁ hs₂ hg hα hβ hr, ?_⟩
  intro h n
  let δ := f_inv.subst (f.subst β - f.subst (α.map R.subtype))
  /- δ (X) ≡ 0 [SMOD I ^ r] -/
  have δ_coeff_mem : ∀ n, PowerSeries.coeff n δ ∈ R.subtype '' ↑(I ^ r) := by
    refine congr_equiv_backward_aux ht hq σ hp_mem s hs₁ hs₂ hg hg_unit hs₀ ?_ hr ?_
    · rw [map_sub, PowerSeries.constantCoeff, PowerSeries.constantCoeff_subst_eq_zero hβ _
      (constantCoeff_RecurFun ..), PowerSeries.constantCoeff_subst_eq_zero (by simp [hα]) _
        (constantCoeff_RecurFun ..), sub_zero]
    · intro d
      obtain ⟨x, hx₁, hx₂⟩ := h d
      use -x
      exact ⟨by simpa, by simp [map_neg, hx₂]⟩
  have δ_coeff_mem_R : ∀ n, (PowerSeries.coeff n) δ ∈ R :=
    fun n ↦ image_of_incl_mem ((PowerSeries.coeff n) δ) (δ_coeff_mem n)
  let δ' := PowerSeries.toSubring δ _ δ_coeff_mem_R
  /- here β (X) = f⁻¹ (f (δ(X)) + f (α (X))), and follow by the first functional equation lemma,
  F (X, Y) = f⁻¹ (f (X) + f (Y)) has coefficient in R, and F(X,Y) = Y + X * G(X,Y) (for some G),
  (this followed by F is a formal group law), and δ (X) ≡ 0 [SMOD I ^ r].  -/
  have constantCoeff_δ : constantCoeff δ = 0 := by
    unfold δ
    rw [PowerSeries.constantCoeff_subst_eq_zero]
    · rw [← sub_zero 0, map_sub]
      congr
      · rw [PowerSeries.constantCoeff_subst_eq_zero hβ _ (constantCoeff_RecurFun ..)]
      · rw [PowerSeries.constantCoeff_subst_eq_zero (by simp [hα]) _ (constantCoeff_RecurFun ..)]
    · exact constantCoeff_inv_RecurFun ht hq σ s hg hg_unit
  have has_subst_aux : HasSubst ![δ, (PowerSeries.map R.subtype) α] :=
    HasSubst.FinPairing constantCoeff_δ (by simp [hα])
  have has_subst_aux' : HasSubst ![δ', α] := by
    refine HasSubst.FinPairing ?_ (by simp [hα])
    simpa [δ', PowerSeries.toSubring] using constantCoeff_δ
  have eq_aux₀ : f.subst δ =  f.subst β - f.subst (α.map R.subtype) := by
    unfold δ
    have : PowerSeries.HasSubst (PowerSeries.subst β f - PowerSeries.subst
      ((PowerSeries.map R.subtype) α) f) := by
      refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
      rw [map_sub, PowerSeries.constantCoeff, PowerSeries.constantCoeff_subst_eq_zero hβ _
        (constantCoeff_RecurFun ..), PowerSeries.constantCoeff_subst_eq_zero (by simp [hα]) _
        (constantCoeff_RecurFun ..), sub_zero]
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' rfl)
      this, RecurFun_comp_inv_RecurFun, PowerSeries.subst_X this]
  have eq_aux : β = F.subst ![δ, α.map R.subtype] := by
    have : f.subst β = f.subst (α.map R.subtype) + f.subst δ := by
      rw [eq_aux₀]
      ring_nf
    have has_subst_const {i : Fin 2}: HasSubst fun (x : Unit) ↦ (X i (R := K)) :=
      (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X _))
    calc
      _ = f_inv.subst (f.subst β) := by
        rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero'
          (constantCoeff_RecurFun ..)) ((PowerSeries.HasSubst.of_constantCoeff_zero' hβ)),
          inv_RecurFun_comp_RecurFun,
          PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hβ)]
      _ = _ := by
        simp [this, F, inv_add_RecurFun]
        simp_rw [PowerSeries.subst]
        rw [subst_comp_subst_apply _ has_subst_aux, subst_congr]
        funext i
        rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply, subst_add has_subst_aux,
          PowerSeries.subst, subst_comp_subst_apply has_subst_const has_subst_aux, PowerSeries.subst,
          subst_comp_subst_apply has_subst_const
          has_subst_aux, subst_X has_subst_aux, subst_X has_subst_aux,
          _root_.add_comm]
        rfl
        · refine PowerSeries.HasSubst.const <| PowerSeries.HasSubst.of_constantCoeff_zero ?_
          rw [map_add, PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply,
            PowerSeries.constantCoeff_subst_eq_zero, PowerSeries.constantCoeff_subst_eq_zero,
              add_zero]
          all_goals simp [constantCoeff_RecurFun ht hq σ s hg]
  have β_coeff_mem_R : ∀ d, PowerSeries.coeff d β ∈ R := by
    rw [eq_aux]
    intro d
    rw [PowerSeries.coeff, coeff_subst has_subst_aux, finsum_eq_sum _
      (coeff_subst_finite has_subst_aux F (Finsupp.single () d))]
    refine Subring.sum_mem _ ?_
    intro c hc
    rw [smul_eq_mul]
    refine Subring.mul_mem _ ?_ ?_
    exact coeff_inv_add_mem_Subring ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hs₀ c
    simp only [Finsupp.prod, Nat.succ_eq_add_one, Nat.reduceAdd, PowerSeries.coeff_coe]
    rw [PowerSeries.coeff_prod]
    refine Subring.sum_mem _ ?_
    intro c' hc'
    refine Subring.prod_mem _ ?_
    intro i hi
    fin_cases i
    · simpa using PowerSeries.coeff_pow_mem δ_coeff_mem_R  _
    · simpa using PowerSeries.coeff_pow_mem (by simp) _
  let β' := β.toSubring _ β_coeff_mem_R
  let F' := F.toSubring _ (coeff_inv_add_mem_Subring ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hs₀)
  have coeff_δ_eq : ∀ d, PowerSeries.coeff d δ = δ'.coeff d := by simp [δ']
  have coeff_β_eq : ∀ d, β.coeff d = β'.coeff d := by simp [β']
  have eq_aux' : β' = F'.subst ![δ', α] := by
    ext n
    have aux {a : R} : R.subtype a = R.subtype.toAddMonoidHom a := rfl
    rw [← coeff_β_eq, eq_aux, PowerSeries.coeff, coeff_subst has_subst_aux,
      PowerSeries.coeff, coeff_subst has_subst_aux', ← Subring.subtype_apply, aux,
      AddMonoidHom.map_finsum _ (coeff_subst_finite has_subst_aux' F' (Finsupp.single () n)),
        finsum_congr]
    intro d
    simp [F', δ', PowerSeries.coeff_mul]
    congr! 2 with l hl
    all_goals simp [PowerSeries.coeff_pow]
  obtain ⟨G, hG⟩ := decomp_InvAdd_RecurFun_Subring ht hq σ hs a_congr hp_mem s hs₁ hs₂ hg hg_unit hs₀
  rw [coeff_β_eq]
  have mem_ideal_MvPowerSeries_aux : (δ' * subst ![δ', α] G) ∈ (I ^ r).PowerSeries := by
    refine Ideal.IsTwoSided.mul_mem_of_left _ ?_
    simp only [Ideal.PowerSeries, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq]
    intro n
    simp only [Subring.subtype_apply, coeff_δ_eq, Set.mem_image, SetLike.mem_coe,
      SetLike.coe_eq_coe, exists_eq_right] at δ_coeff_mem
    exact δ_coeff_mem _
  have mem_aux : α.coeff n - β'.coeff n ∈ I ^ r := by
    simp_rw [eq_aux', F', F, hG, subst_add has_subst_aux', subst_mul has_subst_aux',
      subst_X has_subst_aux']
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, map_add, sub_add_cancel_left, neg_mem_iff]
    exact Submodule.mem_comap.mp (mem_ideal_MvPowerSeries_aux n)
  use α.coeff n - β'.coeff n
  simpa

end PartIV

end inv_add_RecurFun

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

variable {K : Type*} [CommRing K] {R : Subring K} {I : Ideal R} {τ : Type*}
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

include hq in
lemma q_neZero : q ≠ 0 := hq ▸ pow_ne_zero t <| Nat.Prime.ne_zero hp.out

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
  have : (MvPowerSeries.map (σ ^ n)) ((monomial (q ^ n)) 1) = monomial (q^n) 1 := by
    ext d
    erw [coeff_map, coeff_monomial, MonoidWithZeroHom.map_ite_one_zero]
  rw [smul_eq_C_mul, ← subst_map (.monomial' (q_pow_neZero hq) 1), this]
  refine .trans (le_add_of_le_right (.trans ?_ (le_order_subst _
    (HasSubst.monomial' (q_pow_neZero hq) 1) _))) (MvPowerSeries.le_order_mul)
  rw [← PowerSeries.order_eq_order, order_monomial]
  have neZero : ((PowerSeries.map (σ ^ n)) (RecurFun ht hq σ s hg)).order ≠ 0 :=
    order_ne_zero_iff_constCoeff_eq_zero.mpr <| by simp [constantCoeff_RecurFun ht hq σ s hg]
  split_ifs with h
  · rw [ENat.top_mul neZero]; exact le_top
  obtain h := (Nat.lt_pow_self (n := n) (hq ▸ Nat.one_lt_pow ht (Nat.Prime.one_lt' p).out)).le
  exact .trans (ENat.self_le_mul_right ↑n (zero_ne_one' ℕ∞).symm) <| mul_le_mul' (by norm_cast)
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

/- In this section, we usually denote $f_g(X)$ as $f(X)$ for convention. -/

open MvPowerSeries

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
    → ((σ ^ i) b) * a ∈ R.subtype '' I) := fun i r b h => by
  induction i with
  | zero => exact h
  | succ k hk =>
    rw [RingHom.coe_pow] at hk ⊢
    exact (Function.iterate_succ_apply' σ k b) ▸ hs₂ r _ hk

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
    simp [←hx₂, ←hy₂, (Submodule.add_mem_iff_right (I ^ i) hx₁).mpr hy₁]

include hp_mem in
lemma p_pow_mod_p {G : MvPowerSeries (Fin 2) K} {l : ℕ} (l_pos : 0 < l) :
    ∀ d, ((G ^ (q ^ l)) - ((G.subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)]).map (σ^l))).coeff d
      ∈ R.subtype '' I := by
  intro d
  have mem_aux : (G ^ (q ^ l) -
    ((G.subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)]).map (σ^l))).coeff d ∈ R := by
    sorry
  have pdvd : (p : R) ∣ ⟨_, mem_aux⟩ := by
    sorry
  obtain ⟨pk, hpk⟩ := pdvd
  use ⟨_, mem_aux⟩
  nth_rw 1 [hpk]
  exact ⟨Ideal.IsTwoSided.mul_mem_of_left pk hp_mem, by simp⟩

include ht hq hp_mem hs in
/- I think here should be `G ∈ K⟦X,Y⟧` and change the set up for `σ` to be
`∀ a ∈ K, σ a ≡ a ^ q mod I`-/
/- Second Technical lemma: Forall `n, l ∈ ℕ` and `G(X,Y) ∈ K⟦X,Y⟧`  with assumption that $n=q^r m$,
we have that $G^{q^r m q^l} ≡ (σ^l G(X^{q^l},Y^{q^l}))^n$. -/
theorem pow_ModEq (G : MvPowerSeries (Fin 2) K) {n r l m : ℕ} (hn : n = q ^ r * m) (hl : 0 < l) :
    ∀ d, (G ^ (n * q ^ l) -
      ((G.subst ![X₀^(q^l), X₁^(q^l)])^n).map (σ^l)).coeff d ∈ R.subtype '' ↑(I^(r + 1)) := by
  sorry

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

/-- `inv_add_aux` define to be `f_g⁻¹(f_g(X) + f_g(Y))`, and we will prove this to be
a formal group law over coefficient ring `R`. Now we denote `F(X,Y) = f_g⁻¹(f_g(X) + f_g(Y))`
and `f (X) = f_g (X)` for convention. -/
def inv_add_RecurFun :=
    (inv_RecurFun ht hq σ s hg hg_unit).subst ((RecurFun ht hq σ s hg).subst (X₀ (R := K)) +
    (RecurFun ht hq σ s hg).subst X₁)

/-- constant coefficient of $f_g(X)+f_g(Y)$ is zero-/
lemma constantCoeff_add_RecurFun : constantCoeff ((RecurFun ht hq σ s hg).subst (X₀ (R := K)) +
    (RecurFun ht hq σ s hg).subst X₁) = 0 := by
  rw [RingHom.map_add, PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun ..,
    PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun .., add_zero]

lemma coeff_X_inv_add_RecurFun :
    (inv_add_RecurFun ht hq σ s hg hg_unit).coeff (Finsupp.single 0 1) = 1 := by
  rw [inv_add_RecurFun, PowerSeries.coeff_subst <| PowerSeries.HasSubst.of_constantCoeff_zero
    <| constantCoeff_add_RecurFun .., finsum_eq_single _ 1]
  simp
  rw [PowerSeries.coeff_subst_X_s, PowerSeries.coeff_subst_X_s' (one_ne_zero)]
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
  simp [hi']
  rw [PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun ..,
    PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun .., add_zero]

lemma coeff_Y_inv_add_RecurFun :
    (coeff (Finsupp.single 1 1)) (inv_add_RecurFun ht hq σ s hg hg_unit) = 1 := by
  /- the proof of this should be similar as above `coeff_inv_add_aux_X`-/
  rw [inv_add_RecurFun, PowerSeries.coeff_subst <| PowerSeries.HasSubst.of_constantCoeff_zero
    <| constantCoeff_add_RecurFun .., finsum_eq_single _ 1]
  simp
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
  simp [hi']
  rw [PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun ..,
    PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun .., add_zero]

open PowerSeries HasSubst in
/-- `f(F(X,Y)) = f (X) + f(Y)`-/
lemma f_F_eq_f_add :
    (RecurFun ht hq σ s hg).subst (inv_add_RecurFun ht hq σ s hg hg_unit) =
    (RecurFun ht hq σ s hg).subst X₀ + (RecurFun ht hq σ s hg).subst X₁ := by
  rw [inv_add_RecurFun, ← subst_comp_subst_apply (of_constantCoeff_zero' rfl)
    <| of_constantCoeff_zero <| constantCoeff_add_RecurFun .., inv_RecurFun,
    subst_inv_eq, subst_X <| .of_constantCoeff_zero <| constantCoeff_add_RecurFun ..]

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
    (σ ^ i).eq_toAddMonoidHom, map_finsum _ <| coeff_subst_finite
    (HasSubst.inv_add_RecurFun ..) _ _, finsum_congr (fun d => _)]
  simp [smul_eq_mul, PowerSeries.coeff_map, map_mul, MvPowerSeries.coeff_pow]

lemma constantCoeff_frobnius_F_zero (i : ℕ):
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    constantCoeff (subst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i] F) = 0 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  rw [constantCoeff_subst_zero] <;> simp [zero_pow <| q_pow_neZero hq,
    constantCoeff_inv_add_RecurFun]

include hq in
lemma has_subst_X_pow (i : ℕ): HasSubst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i] := by
  refine HasSubst.FinPairing ?_ ?_
  · rw [X₀, X, monomial_pow, ←coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
    exact Finsupp.ne_iff.mpr ⟨0, by simp [Ne.symm <| pow_ne_zero i (q_neZero hq)]⟩
  · rw [X₁, X, monomial_pow, ←coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
    exact Finsupp.ne_iff.mpr ⟨1, by simp [Ne.symm <| pow_ne_zero i (q_neZero hq)]⟩

lemma map_X_pow {i : ℕ} (j : ℕ) : ![X₀ ^ (q^i), X₁ ^ (q^i)] =
    fun n => (![X₀^(q^i), X₁^(q^i)] n).map (σ^j)  := by
  ext s : 1
  fin_cases s
  dsimp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
  rw [map_pow, map_X]
  dsimp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [map_pow, map_X]

/-- $σ^i f (F(X^{q^i}, Y^{q^i})) = ∑'(n ∈ ℕ), σ^i (a_n) * F(X^{q^i}, Y^{q^i})^n. $-/
lemma decomp_f (i : ℕ) [UniformSpace K] [T2Space K] [DiscreteUniformity K] :
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    ∑' (n : ℕ), ((f.map (σ ^ i)).coeff n) •
    ((subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F).map (σ ^ i)) ^ n =
    (f.map (σ ^ i)).subst ((F.map (σ ^ i)).subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] ) := by
  /- this lemma need to use tsum_subst. -/
  let f := (RecurFun ht hq σ s hg)
  let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  simp_rw [←f_def, ←F_def]
  obtain has_subst := has_subst_X_pow hq (K := K)
  have has_subst_aux : PowerSeries.HasSubst ((F.map (σ ^ i)).subst
    ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero <| by
      rw [map_X_pow σ i, subst_map (has_subst i), constantCoeff_map,
        constantCoeff_frobnius_F_zero, map_zero]
  nth_rw 2 [(f.map (σ^i)).as_tsum]
  rw [tsum_subst ⟨f.map (σ ^ i), (f.map (σ ^ i)).hasSum_of_monomials_self⟩ has_subst_aux, tsum_congr]
  intro n
  ext d
  simp_rw [PowerSeries.coeff_map, Nat.succ_eq_add_one, Nat.reduceAdd, map_smul,
    smul_eq_mul, ←map_pow, coeff_map, PowerSeries.monomial_eq_C_mul_X_pow,
    ←PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul has_subst_aux,  PowerSeries.subst_pow
    has_subst_aux, PowerSeries.subst_X has_subst_aux, map_smul, smul_eq_mul,
    ← subst_pow (has_subst i), ← map_pow]
  congr! 1
  nth_rw 2 [map_X_pow σ i]
  rw [subst_map (has_subst i), coeff_map]

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
      erw [PowerSeries.subst_map has_subst_aux]
      congr! 2
      rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.monomial' (q_pow_neZero hq) 1)
        has_subst_aux, PowerSeries.subst_congr]
      funext d
      rw [←PowerSeries.X_pow_eq, PowerSeries.subst_pow has_subst_aux,
        PowerSeries.subst_X has_subst_aux]

include ht hq hg in
lemma summable_X_x  [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0) (x : τ):
    let f := (RecurFun ht hq σ s hg)
    Summable (fun i ↦ (s i • ((PowerSeries.subst ((X x) ^ q ^ i) f).map (σ ^ i)))) := by
  intro f
  have eq_aux : ∀ i, s i • (MvPowerSeries.map (σ ^ i)) (PowerSeries.subst ((X x) ^ q ^ i) f)
      =  PowerSeries.subst (X x) (s i • ((RecurFun ht hq σ s hg).subst
      ((PowerSeries.monomial (q ^ i)) 1)).map (σ^i)) := fun i => by
    rw [PowerSeries.subst_smul (PowerSeries.HasSubst.X x), ← PowerSeries.subst_map,
      ← PowerSeries.subst_map , PowerSeries.subst_comp_subst_apply _ (PowerSeries.HasSubst.X x)]
    congr! 2
    simp
    have aux : X x = (X x).map (σ ^ i) := by simp
    nth_rw 2 [aux]
    rw [PowerSeries.monomial_eq_C_mul_X_pow, ← PowerSeries.smul_eq_C_mul, one_smul]
    erw [PowerSeries.subst_map (PowerSeries.HasSubst.X x)]
    rw [PowerSeries.subst_pow (PowerSeries.HasSubst.X x), PowerSeries.subst_X
      (PowerSeries.HasSubst.X x)]
    simp
    · refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
      erw [PowerSeries.constantCoeff_map]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_monomial, if_neg (q_pow_neZero hq).symm, map_zero]
    · refine PowerSeries.HasSubst.monomial' (q_pow_neZero hq) 1
    · refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
      simp [zero_pow (q_pow_neZero hq)]
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
    ((F.subst ![X₀^(q ^ i), X₁^(q^i)]).map (σ^i)) ^ n
    = f.subst X₀ + f.subst X₁ - g.subst X₀ - g.subst X₁ := by
  let f := (RecurFun ht hq σ s hg)
  let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  obtain has_subst := has_subst_X_pow hq (K:=K)
  calc
    _ = ∑' i : ℕ, (s i) • ((f.map (σ^i)).subst (((F.map (σ^i)).subst ![X₀^(q ^ i), X₁^(q^i)])))
      := by
      apply tsum_congr <| fun i => by
        congr
        simp_rw [←f_def, ←F_def, ←PowerSeries.coeff_map]
        exact decomp_f ..
    _ = ∑' i : ℕ, (s i) • ((f.subst X₀).map (σ^i) + (f.subst X₁).map (σ^i)).subst
      ![X₀^(q^i), X₁^(q^i)] := by
      apply tsum_congr <| fun i => by
        congr
        rw [←sigma_map_distrib ht hq σ s hg hg_unit i, ←F_def, ←f_def]
        have eq_aux : subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] ((f.map (σ ^ i)).subst (F.map (σ ^ i))) =
          (f.map (σ ^ i)).subst ((subst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i] F).map (σ ^ i)) := by
          rw [PowerSeries.subst, PowerSeries.subst, subst_comp_subst_apply _ <|has_subst i]
          apply subst_congr
          funext s
          nth_rw 1 [map_X_pow]
          rw [subst_map <|has_subst i]
          refine PowerSeries.HasSubst.const <| PowerSeries.HasSubst.of_constantCoeff_zero ?_
          rw [constantCoeff_map, constantCoeff_inv_add_RecurFun, map_zero]
        ext n
        rw [eq_aux, PowerSeries.coeff_subst, PowerSeries.coeff_subst, finsum_congr]
        intro d
        nth_rw 1 [map_X_pow σ i, subst_map <|has_subst i]
        refine PowerSeries.HasSubst.of_constantCoeff_zero <| by rw [constantCoeff_map,
          constantCoeff_frobnius_F_zero, map_zero]
        refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
        nth_rw 1 [map_X_pow]
        rw [subst_map (has_subst i), constantCoeff_map, constantCoeff_frobnius_F_zero, map_zero]
    _ = ∑' i, (s i • ((f.subst (X₀ ^ (q ^ i))).map (σ ^ i) +
      (f.subst (X₁ ^ (q ^ i))).map (σ ^ i))) := tsum_congr <| fun i => by
      rw [subst_add (has_subst i), map_X_pow, subst_map (has_subst i), subst_map (has_subst i)]
      congr! 3
      · rw [PowerSeries.subst, subst_comp_subst_apply
        (PowerSeries.HasSubst.const <| PowerSeries.HasSubst.X _) (has_subst _)]
        apply subst_congr
        funext s
        simp [subst_X (has_subst i)]
      · rw [PowerSeries.subst, subst_comp_subst_apply
        (PowerSeries.HasSubst.const <| PowerSeries.HasSubst.X _) (has_subst i)]
        apply subst_congr
        funext s
        simp [subst_X (has_subst i)]
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

lemma tsum_to_finite₁ {n : Fin 2 →₀ ℕ} (hn₀ : n ≠ 0) [UniformSpace K] [T2Space K]
    [DiscreteUniformity K] :
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    (∑' (i : ℕ), (coeff n) (s i •
    ∑' (j : ℕ), (σ ^ i) ((PowerSeries.coeff j) f) • (MvPowerSeries.map (σ ^ i))
    (subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F) ^ j)) = (∑ i ∈ range (n.degree + 1),(coeff n) (s i •
    ∑' (j : ℕ), (σ ^ i) ((PowerSeries.coeff j) f) • (MvPowerSeries.map (σ ^ i))
    (subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F) ^ j)) := by
  intro f F
  refine tsum_eq_sum ?_
  intro b hb
  simp only [mem_range, not_lt, Nat.succ_eq_add_one, Nat.reduceAdd, map_smul,
    smul_eq_mul] at ⊢ hb
  if hsum : Summable (fun j => (σ ^ b) ((PowerSeries.coeff j) f) • (MvPowerSeries.map (σ ^ b))
    (subst ![X₀ ^ q ^ b, X₁ ^ q ^ b] F) ^ j) then
    rw [Summable.map_tsum hsum _ (WithPiTopology.continuous_coeff K n)]
    have eqZero_aux : ∑' (i : ℕ), (coeff n)
      ((σ ^ b) ((PowerSeries.coeff i) f) • (MvPowerSeries.map (σ ^ b))
      (subst ![X₀ ^ q ^ b, X₁ ^ q ^ b] F) ^ i) = 0 := by
      have aux : ∀ (i : ℕ), (coeff n)
        ((σ ^ b) ((PowerSeries.coeff i) f) • (MvPowerSeries.map (σ ^ b))
        (subst ![X₀ ^ q ^ b, X₁ ^ q ^ b] F) ^ i) = 0 := fun i => by
        rw [@coeff_smul, ←map_pow, coeff_map]
        have aux' : (coeff n) ((subst ![(X₀ (R := K)) ^ q ^ b, X₁ ^ q ^ b] F) ^ i) = 0 := by
          if hi₀ : i = 0 then simp [hi₀, coeff_one]; tauto
          else
          rw [←subst_pow <| has_subst_X_pow hq b,
            coeff_subst <| has_subst_X_pow hq b]
          apply finsum_eq_zero_of_forall_eq_zero
          intro x
          simp
          if hx₀ : x = 0 then simp [hx₀, coeff_one]; tauto
          else
          rw [X_pow_eq, X_pow_eq, monomial_pow, monomial_pow, monomial_mul_monomial,
            coeff_monomial]
          have aux : n ≠ x 0 • Finsupp.single 0 (q ^ b) + x 1 • Finsupp.single 1 (q ^ b) := by
            by_contra hc
            have degree_aux : n.degree = ((x 0 +  x 1) * q ^ b) := by
              simp [hc, add_mul]
            have ge_aux : x 0 + x 1 ≥ 1 := by
              rw [show x 0 + x 1 = x.degree by simp [Finsupp.degree_eq_sum]]
              by_contra hc'
              have degreeZero : x.degree = 0 := by linarith
              have x_eq_zero : x = 0 := (Finsupp.degree_eq_zero_iff x).mp degreeZero
              exact hx₀ x_eq_zero
            have ge_aux' : n.degree ≥ b := by
              rw [←one_mul b, degree_aux]
              refine Nat.mul_le_mul ge_aux ?_
              have qge_aux : q ≥ 2 := by
                nlinarith [Nat.le_self_pow ht p, Nat.Prime.two_le hp.out]
              exact (Nat.lt_pow_self qge_aux).le
            linarith
          rw [if_neg aux, mul_zero]
        simp [aux']
      simp_rw [aux]
      exact tsum_zero
    rw [eqZero_aux, mul_zero]
  /- if not summable then equal to zero, but in fact it is summable-/
  else
  rw [tsum_eq_zero_of_not_summable hsum, coeff_zero, mul_zero]

lemma le_order₁ {b : ℕ} : b ≤ (PowerSeries.subst (inv_add_RecurFun ht hq σ s hg hg_unit)
    (PowerSeries.C (s b) * (PowerSeries.map (σ ^ b)) (PowerSeries.subst
      (PowerSeries.monomial (q ^ b) 1) (RecurFun ht hq σ s hg)))).order := by
  have aux : (b : ENat) ≤ q ^ b := by
    exact_mod_cast (Nat.lt_pow_self (IsPrimePow.one_lt (isPrimePow_q ht hq))).le
  refine (.trans aux ?_)
  have le_aux₁ : q ^ b ≤ ((RecurFun ht hq σ s hg).subst
    (PowerSeries.monomial (q ^ b) (1 : K))).order := by
    refine .trans (ENat.self_le_mul_right _ (zero_ne_one' ℕ∞).symm) (.trans (mul_le_mul ?_
      (ENat.one_le_iff_ne_zero.mpr <| PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr
        (constantCoeff_RecurFun ..)) (zero_le_one' _) (zero_le _))
          (PowerSeries.le_order_subst _ (PowerSeries.HasSubst.monomial' (q_pow_neZero hq) 1) _))
    · simp [←order_eq_order, PowerSeries.order_monomial]
      split_ifs <;> simp
  refine .trans (ENat.self_le_mul_left _ (zero_ne_one' _).symm) <|
    .trans (mul_le_mul (ENat.one_le_iff_ne_zero.mpr <| order_ne_zero_iff_constCoeff_eq_zero.mpr
      (constantCoeff_inv_add_RecurFun ..)) ?_ (zero_le _) (zero_le _))
        (PowerSeries.le_order_subst _ (HasSubst.inv_add_RecurFun ..) _)
  rw [← PowerSeries.smul_eq_C_mul]
  refine .trans le_aux₁ (.trans ?_ (PowerSeries.le_order_smul))
  rw [← order_eq_order]
  exact PowerSeries.le_order_map _

lemma tsum_to_finite₂ {n : Fin 2 →₀ ℕ} [UniformSpace K] [T2Space K]
    [DiscreteUniformity K] :
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    ∑' (i : ℕ), (coeff n) (PowerSeries.subst F (PowerSeries.C (s i)
    * (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) f))) =
    ∑ i ∈ range (n.degree + 1), (coeff n) (PowerSeries.subst F (PowerSeries.C (s i) *
    (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) f))) := by
  refine tsum_eq_sum ?_
  intro b hb
  simp at hb
  exact coeff_of_lt_order <| (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp
    (.trans (by norm_cast) (le_order₁ ..))

open PowerSeries in
include hs hp_mem hs₁ hs₂ in
/-- f(F(X,Y)) ≡ g(F(X,Y)) + f(X) + f(Y) - g(X) - g(Y) [MOD R]-/
lemma RModEq_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0):
    let f := (RecurFun ht hq σ s hg)
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    ∀ n, (g.subst F + f.subst X₀ + f.subst X₁ - g.subst X₀ - g.subst X₁
      - f.subst F).coeff n ∈ R  := by
  /- this need to use the equation we prove above. -/
  intro f F n
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  have has_subst_F : PowerSeries.HasSubst F := HasSubst.inv_add_RecurFun ht hq σ s hg hg_unit
  have has_subst_monomial (i : ℕ) := PowerSeries.HasSubst.monomial'
    (q_pow_neZero hq (x := i)) (1 : K)
  have le_q_pow {i : ℕ} : 1 ≤ q ^ i := Nat.one_le_pow i q (by positivity [q_neZero hq])
  by_cases hn₀ : n = 0
  ·
    /- all these terms are equal to zero. -/
    simp [hn₀]
    have coeff_zero₁: constantCoeff (g.subst F) = 0 :=
      constantCoeff_subst_zero (constantCoeff_inv_add_RecurFun ..) hg
    have coeff_zero_XY {x : Fin 2} : (f.subst (X x (R := K))).constantCoeff = 0 :=
      constantCoeff_subst_zero (constantCoeff_X x) (constantCoeff_RecurFun ..)
    have coeff_zero_XY' {x : Fin 2} : (g.subst (X x (R := K))).constantCoeff = 0 :=
      constantCoeff_subst_zero (constantCoeff_X x) hg
    have coeff_zero₂ : (f.subst F).constantCoeff = 0 :=
      constantCoeff_subst_zero (constantCoeff_inv_add_RecurFun ..) (constantCoeff_RecurFun ..)
    simp [coeff_zero₁, coeff_zero_XY, coeff_zero_XY', coeff_zero₂]

  have has_subst₁ (b : ℕ) : PowerSeries.HasSubst (MvPowerSeries.subst ![(X₀ (R := K)) ^ q ^ b,
    X₁ ^ q ^ b] ((MvPowerSeries.map (σ ^ b)) F)) := by
    refine HasSubst.of_constantCoeff_zero <| _root_.constantCoeff_subst_zero ?_ ?_
    intro x; fin_cases x <;> simp [zero_pow (q_pow_neZero hq)]
    rw [MvPowerSeries.constantCoeff_map, constantCoeff_inv_add_RecurFun, map_zero]
  have tsum_eq_subst {b : ℕ} : (∑' (n : ℕ), (σ ^ b) ((PowerSeries.coeff n) f) •
    (MvPowerSeries.map (σ ^ b)) (MvPowerSeries.subst ![X₀ ^ q ^ b, X₁ ^ q ^ b] F) ^ n) =
      (f.map (σ ^ b)).subst ((F.map (σ ^ b)).subst ![X₀ ^ q ^ b, X₁ ^ q ^ b]) := by
    rw [(f.map (σ ^ b)).as_tsum, tsum_subst _ (has_subst₁ _)]
    congr! 2 with i
    rw [PowerSeries.monomial_eq_C_mul_X_pow, ← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul
      (has_subst₁ _), PowerSeries.coeff_map, PowerSeries.subst_pow (has_subst₁ _),
        PowerSeries.subst_X (has_subst₁ b), ← MvPowerSeries.subst_map (has_subst_X_pow hq b)]
    congr! 4 with j
    fin_cases j <;> simp
    exact ⟨_, PowerSeries.hasSum_of_monomials_self _⟩
  have b_le_qb (b : ℕ) : (b : ENat) ≤ q ^ b := by
    exact_mod_cast (Nat.lt_pow_self (IsPrimePow.one_lt (isPrimePow_q ht hq))).le
  have le_order_aux {b : ℕ} : ↑b ≤ (s b • PowerSeries.subst (MvPowerSeries.subst
    ![(X₀ (R := K)) ^ q ^ b, X₁ ^ q ^ b] ((MvPowerSeries.map (σ ^ b)) F))
    ((PowerSeries.map (σ ^ b)) f)).order := by
    have le_aux : q ^ b ≤ ((F.map (σ ^ b)).subst ![(X₀ (R := K)) ^ q ^ b, X₁ ^ q ^ b]).order := by
      refine .trans ?_ (MvPowerSeries.le_order_subst (has_subst_X_pow hq b) (F.map (σ ^ b)))
      refine le_mul_of_le_of_one_le
        (le_iInf fun i => by fin_cases i <;> simpa using MvPowerSeries.order_X_pow_ge _)
          ((F.map (σ ^ b)).one_le_order ?_)
      rw [MvPowerSeries.constantCoeff_map, constantCoeff_inv_add_RecurFun, map_zero]
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
    rw [Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n), ]
    /- there should be a tsum to finite -/
    rw [tsum_eq_sum (s := range (n.degree + 1))]
    have eq_aux : (MvPowerSeries.coeff n) (PowerSeries.subst F ((MvPowerSeries.map (σ ^ i))
      (f.subst (PowerSeries.monomial (q ^ i) 1)))) = ∑ b ∈ range (n.degree + 1),
      MvPowerSeries.coeff n ((σ ^ i) ((PowerSeries.coeff b) f) • F ^ (q ^ i * b)) := by
      /- to finite-/
      have eq_aux₁ : (PowerSeries.subst F ((MvPowerSeries.map (σ ^ i))
        ((PowerSeries.monomial (q ^ i)) 1))) = F ^ (q ^ i) := by
        rw [PowerSeries.monomial, map_monomial, map_one]
        erw [PowerSeries.monomial_eq_C_mul_X_pow]
        rw [← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul has_subst_F,
          PowerSeries.subst_pow has_subst_F, PowerSeries.subst_X has_subst_F, one_smul]
      rw [← PowerSeries.subst_map (has_subst_monomial i), PowerSeries.subst_comp_subst_apply _ has_subst_F, eq_aux₁]
      rw [PowerSeries.coeff_subst (HasSubst.pow has_subst_F le_q_pow)]
      simp_rw [MvPowerSeries.coeff_smul, PowerSeries.coeff_map, smul_eq_mul, pow_mul]
      refine finsum_eq_finset_sum_of_support_subset _ (Function.support_subset_iff'.mpr ?_)
      intro d hd
      simp at hd
      have : (MvPowerSeries.coeff n) ((F ^ q ^ i) ^ d) = 0 := by
        refine MvPowerSeries.coeff_of_lt_order
          <| (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp ?_
        rw [← pow_mul]
        have aux : d ≤ (q ^ i * d) • (1 : ENat) := by
          simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_one]
          exact_mod_cast Nat.le_mul_of_pos_left d (Nat.pow_pos (q.pos_of_ne_zero (q_neZero hq)))
        refine .trans (.trans (.trans (by norm_cast) aux) (nsmul_le_nsmul_right (F.one_le_order
          (constantCoeff_inv_add_RecurFun ..)) _)) (MvPowerSeries.le_order_pow (q ^ i * d))
      simp [this]
      · refine HasSubst.of_constantCoeff_zero' ?_
        erw [PowerSeries.constantCoeff_map]
        rw [← PowerSeries.coeff_zero_eq_constantCoeff,
          PowerSeries.coeff_monomial, if_neg (q_pow_neZero hq).symm, map_zero]
    rw [eq_aux, ← sum_sub_distrib]
    simp_rw [MvPowerSeries.coeff_smul, ← mul_sub]
    apply mem_ideal_aux
    intro b hb
    have mem_aux : ((MvPowerSeries.coeff n) ((MvPowerSeries.map (σ ^ i))
      (MvPowerSeries.subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F) ^ b) - (MvPowerSeries.coeff n)
        (F ^ (q ^ i * b))) ∈ R.subtype '' ↑(I ^ (multiplicity q b + 1)) := by
      by_cases hi₀ : i = 0
      · have aux : (MvPowerSeries.coeff n) ((MvPowerSeries.map (1 : K →+* K)) (MvPowerSeries.subst ![X₀, X₁] F) ^ b) -
          (MvPowerSeries.coeff n) (F ^ b) = 0 := by
          have aux : MvPowerSeries.subst ![X₀, X₁] F = F := by
            have : ![X₀, X₁] = (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) K) := by
              funext s; fin_cases s <;> rfl
            rw [this, MvPowerSeries.subst_self, id]
          simp [MvPowerSeries.map, MvPowerSeries.coeff_apply, aux]
        simp [hi₀, aux]
      · obtain ⟨m, hm⟩ := pow_multiplicity_dvd q b
        obtain ⟨x, hx₁, hx₂⟩ := pow_ModEq ht hq σ hs hp_mem F hm (i.zero_lt_of_ne_zero hi₀) n
        rw [mul_comm b, map_sub] at hx₂
        have {a b : K} : a - b = - (b - a) := by ring
        rw [this, ← map_pow, ← hx₂]
        use -x
        rw [SetLike.mem_coe] at hx₁
        simpa using Submodule.neg_mem _ hx₁
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
      have le_aux : b ≤ ((MvPowerSeries.map (σ ^ i)) (MvPowerSeries.subst ![(X₀ (R := K)) ^ q ^ i,
        X₁ ^ q ^ i] F) ^ b).order := by
        refine .trans ?_ (MvPowerSeries.le_order_pow b)
        have le_aux' : 1 ≤ ((MvPowerSeries.map (σ ^ i)) (MvPowerSeries.subst
          ![X₀ (R := K) ^ q ^ i, X₁ ^ q ^ i] F)).order := by
          refine ENat.one_le_iff_ne_zero.mpr <|
            MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr ?_
          rw [MvPowerSeries.constantCoeff_map, constantCoeff_subst_zero
            (fun x => by fin_cases x <;> simp [zero_pow (q_pow_neZero hq)])
              (constantCoeff_inv_add_RecurFun ..), map_zero]
        exact .trans (by simp) (nsmul_le_nsmul_right le_aux' b)
      refine .trans (by norm_cast) (.trans le_aux (MvPowerSeries.le_order_smul))
    have summable_aux : ∀ n, (σ ^ i) ((PowerSeries.coeff n) f) • (MvPowerSeries.map (σ ^ i))
      (MvPowerSeries.subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F) ^ n = PowerSeries.subst
      (MvPowerSeries.subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] ((MvPowerSeries.map (σ ^ i)) F))
      ((PowerSeries.monomial n) ((PowerSeries.coeff n) ((PowerSeries.map (σ ^ i)) f))) := by
      intro n
      rw [PowerSeries.monomial_eq_C_mul_X_pow, ← PowerSeries.smul_eq_C_mul,
        PowerSeries.subst_smul (has_subst₁ _), subst_pow (has_subst₁ _), subst_X (has_subst₁ _),
        PowerSeries.coeff_map, ← MvPowerSeries.subst_map (has_subst_X_pow hq i)]
      congr! 4 with j
      fin_cases j <;> simp
    simp_rw [summable_aux]
    exact Summable.summable_of_subst ⟨_, PowerSeries.hasSum_of_monomials_self _⟩ (has_subst₁ i)
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
    rw [PowerSeries.order_eq_order]
  · intro b hb
    simp at hb
    rw [tsum_eq_subst]
    exact MvPowerSeries.coeff_of_lt_order <| (ENat.add_one_le_iff (ENat.coe_ne_top (n.degree))).mp
      (.trans (by norm_cast) le_order_aux)
  · exact MvPowerSeries.Summable.increase_order fun n =>
      (MvPowerSeries.smul_eq_C_mul _ (s n)) ▸ (le_order₁ ..)
  · exact MvPowerSeries.Summable.increase_order fun n => tsum_eq_subst ▸ le_order_aux
  · exact PowerSeries.Summable.increase_order fun n => by
      have le_aux : n ≤ ((MvPowerSeries.map (σ ^ n)) (PowerSeries.subst
        ((PowerSeries.monomial (q ^ n)) (1 : K)) (RecurFun ht hq σ s hg))).order := by
        refine .trans (le_mul_of_le_of_one_le ?_ ?_) (.trans (PowerSeries.le_order_subst _ (has_subst_monomial n) _)
          (MvPowerSeries.le_order_map _))
        rw [← PowerSeries.order_eq_order]
        refine .trans (b_le_qb n) (PowerSeries.le_order_monomial _ (1 : K))
        refine PowerSeries.one_le_order (constantCoeff_RecurFun ..)
      rw [PowerSeries.order_eq_order]
      exact .trans le_aux (MvPowerSeries.le_order_smul)


open AddMonoidHom PowerSeries in
lemma coeff_subst_X_mem_aux {n : Fin 2 →₀ ℕ} {x : Fin 2} :
    (g.subst (X x (R := K))).coeff n ∈ R := by
  have eq_aux : g.subst (X x (R := K)) = (g.subst (X x)).map R.subtype := by
    ext d
    rw [coeff_subst <| .X x, MvPowerSeries.coeff_map, coeff_subst <| .X x,
      R.subtype.eq_toAddMonoidHom, map_finsum _ <| coeff_subst_finite (.X x) g d, finsum_congr]
    intro m
    congr
    rw [MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X_pow]
    norm_cast
  simp [eq_aux]

include hs hp_mem hs₁ hs₂ in
/-- by above lemma we can deduce that all coefficient in g(F(X,Y)) is in `R`, since
  f(F(X,Y)) = f(X) + f(Y).-/
lemma RModEq_aux₂ [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0) :
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    ∀ n, (g.subst F).coeff n ∈ R := by
  intro F n
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  obtain h₀ := RModEq_aux ht hq σ hs hp_mem s hs₁ hs₂ hg hg_unit hs0 n
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

include hs hp_mem hs₁ hs₂ in
/-- `inv_add_aux` define to be `f_g⁻¹(f_g(X) + f_g(Y))`, the coeff of this multi variate
  power series are all in `R`.-/
lemma coeff_inv_add_mem_Subring [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0):
    ∀ n, (inv_add_RecurFun ht hq σ s hg hg_unit).coeff n ∈ R := by
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
        (RModEq_aux₂ ht hq σ hs hp_mem s hs₁ hs₂ hg hg_unit hs0 n))

end PartI

section PartII

variable {g' : PowerSeries R} (hg' : g'.constantCoeff = 0)
/- In this section, we denote $G(X) = f_g⁻¹(f_{g'} (X))$ for simplicity. -/

open PowerSeries HasSubst in
/-- f_g'(X) = f(G(X)). -/
lemma f_g'_eq_f_G :
    let f := RecurFun ht hq σ s hg
    let f_g' := (RecurFun ht hq σ s hg')
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    f_g' = f.subst G := by
  intro f f_g' G
  rw [← subst_comp_subst_apply (of_constantCoeff_zero' rfl) (.of_constantCoeff_zero'
    (constantCoeff_RecurFun ..)), inv_RecurFun, subst_inv_eq, subst_X
      (.of_constantCoeff_zero' (constantCoeff_RecurFun ..))]

include hs₁ hs₂ in
lemma coeff_g_G_mem [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0):
    ∀ n : ℕ, PowerSeries.coeff n (g.subst ((inv_RecurFun ht hq σ s hg hg_unit).subst
      (RecurFun ht hq σ s hg'))) ∈ R := by
  intro n

  sorry

lemma constantCoeff_G :
    ((inv_RecurFun ht hq σ s hg hg_unit).subst (RecurFun ht hq σ s hg')).constantCoeff = 0 :=
  PowerSeries.constantCoeff_subst_zero (constantCoeff_RecurFun ..) rfl

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

include hs₁ hs₂ in
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
        (coeff_g_G_mem ht hq σ s hs₁ hs₂ hg hg_unit hg' hs0 k))

end PartII

section PartIII

/- functional equaltion lemma III: let `h` be another power series with coefficient in `R`,
  then there exist a power series `h₁` over `R` such that `f(h(X)) = f_{h₁}(X)`, this is
  equivalent to say that `f₁(X) - ∑s_i σ^i(f₁(X^{q^i}))` is a power series in `R`, where
  `f₁(X) := f(h(X))` and `f(X) := f_g(X)` -/
lemma coeff_inv_RecurFun_g'_mem_Subring' [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) {h : PowerSeries R}:
    let f := (RecurFun ht hq σ s hg)
    let f₁ : PowerSeries K := f.subst (h.map R.subtype)
    ∀ n, (f₁ - ∑' i : ℕ, PowerSeries.C (s i) * f₁.subst (PowerSeries.monomial (q^i)
    (1 : K))).coeff n ∈ R := by
  sorry

end PartIII

end inv_add_RecurFun

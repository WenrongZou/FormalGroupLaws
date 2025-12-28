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
    HasSum (fun i ↦ s i • ((RecurFun ht hq σ s hg).expand (q^i) (q_pow_neZero hq)).map (σ^i))
      (RecurFun ht hq σ s hg - g.map R.subtype) := by
  classical
  let x := fun i ↦ s i • ((RecurFun ht hq σ s hg).expand (q^i) (q_pow_neZero hq)).map (σ^i)
  have eq_aux : (RecurFun ht hq σ s hg - g.map R.subtype) =
    .mk (fun n => ∑ i ∈ range (n + 1), (PowerSeries.coeff n (x i))) := by
    ext d
    rw [coeff_mk]
    by_cases hd₀ : d = 0
    · simp [hd₀, RecurFun, RecurFunAux, x, hg, hs₀]
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
    let f := (RecurFun ht hq σ s hg)
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

include hq hp_mem in
lemma p_pow_mod_p (G : MvPowerSeries (Fin 2) K) {l : ℕ} (l_pos : 0 < l) :
    ∀ d, ((G ^ (q ^ l)) - ((G.expand (q ^ l) (q_pow_neZero hq)).map (σ^l))).coeff d
      ∈ R.subtype '' I := by
  intro d
  have mem_aux : (G ^ (q ^ l) -
    ((G.expand (q ^l) (q_pow_neZero hq)).map (σ^l))).coeff d ∈ R := by
    /- this is by my theorem expand_char. -/
    sorry
  have pdvd : (p : R) ∣ ⟨_, mem_aux⟩ := by
    sorry
  obtain ⟨pk, hpk⟩ := pdvd
  use ⟨_, mem_aux⟩
  nth_rw 1 [hpk]
  exact ⟨Ideal.IsTwoSided.mul_mem_of_left pk hp_mem, (by simp)⟩


include ht hq hp_mem hs in
/- Second Technical lemma: Forall `n, l ∈ ℕ` and `G(X,Y) ∈ R⟦X,Y⟧`  with assumption that $n=q^r m$,
we have that $G^{q^r m q^l} ≡ (σ^l G(X^{q^l},Y^{q^l}))^n$. -/
theorem pow_ModEq (G : MvPowerSeries (Fin 2) R) {n r l m : ℕ} (hn : n = q ^ r * m) (hl : 0 < l) :
    ∀ d, ((((G.map (R.subtype)).expand (q ^ l) (q_pow_neZero hq))^n).map (σ^l) -
      (G ^ (q ^ l * n)).map (R.subtype)).coeff d ∈ R.subtype '' ↑(I^(r + 1)) := by
  sorry
  -- have mem_aux {r : ℕ} : ∀ d, (G ^ (q ^ r * q ^ l) - ((G.expand (q ^ l)
  --     (q_pow_neZero hq))^(q ^ r)).map (σ^l)).coeff d ∈ R.subtype '' ↑(I^(r + 1)) := by
  --   induction r  with
  --   | zero =>
  --     rw [pow_zero, one_mul, pow_one, pow_one]
  --     exact p_pow_mod_p hq σ hp_mem G hl
  --   | succ k ih =>
  --     intro d
  --     obtain ⟨H, hH₁, hH₂⟩ : ∃ H ∈ (I ^ (k + 1)).MvPowerSeries, G ^ (q ^ k * q ^ l) =
  --         ((G ^ q ^ k).expand (q ^ l) (q_pow_neZero hq)).map (σ ^ l) + H.map (R.subtype) := sorry
  --     have eq_aux : G ^ (q ^ (k + 1) * q ^ l) = (G ^ (q ^ k * q ^ l)) ^ (p ^ t) := by
  --       rw [hq]; ring
  --     rw [eq_aux, hH₂, add_pow_prime_pow_eq hp.out]


  --     sorry
  -- sorry

include ht hq hp_mem hs in
/- this is more general version for second technical lemma. -/
/- Second Technical lemma: Forall `n, l ∈ ℕ` and `G(X,Y) ∈ R⟦X,Y⟧`  with assumption that $n=q^r m$,
we have that $G^{q^r m q^l} ≡ (σ^l G(X^{q^l},Y^{q^l}))^n$. -/
theorem pow_ModEq' (G : MvPowerSeries τ R) [Finite τ] {n r l m : ℕ} (hn : n = q ^ r * m) (hl : 0 < l) :
    ∀ d, ((((G.map (R.subtype)).expand (q ^ l) (q_pow_neZero hq))^n).map (σ^l) -
      (G ^ (q ^ l * n)).map (R.subtype)).coeff d ∈ R.subtype '' ↑(I^(r + 1)) := by sorry

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

/- this can be replace by `HasSubst.expand`-/
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
    ((F.expand (q^i) (q_pow_neZero hq)).map (σ ^ i)) ^ n =
    (f.map (σ ^ i)).subst ((F.map (σ ^ i)).expand (q^i) (q_pow_neZero hq)) := by
  /- this lemma need to use tsum_subst. -/
  let f := (RecurFun ht hq σ s hg)
  let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
  have f_def : f = (RecurFun ht hq σ s hg) := rfl
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  simp_rw [←f_def, ←F_def]
  obtain has_subst := has_subst_X_pow hq (K := K)
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
      erw [PowerSeries.subst_map has_subst_aux]
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
    rw [PowerSeries.subst_smul (PowerSeries.HasSubst.X x), ← PowerSeries.subst_map
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
  obtain has_subst := has_subst_X_pow hq (K:=K)
  calc
    _ = ∑' i : ℕ, (s i) • (f.map (σ^i)).subst ((F.map (σ^i)).expand (q^i) (q_pow_neZero hq))
      := by
      apply tsum_congr <| fun i => by
        congr
        simp_rw [←f_def, ←F_def, ←PowerSeries.coeff_map]
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
include hs hp_mem hs₁ hs₂ in
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
        have aux : d ≤ (q ^ i * d) • (1 : ENat) := by
          simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_one]
          exact_mod_cast Nat.le_mul_of_pos_left d (Nat.pow_pos (q.pos_of_ne_zero (q_neZero hq)))
        refine .trans (.trans (.trans (by norm_cast) aux) (nsmul_le_nsmul_right (F.one_le_order
          (constantCoeff_inv_add_RecurFun ..)) _)) (MvPowerSeries.le_order_pow (q ^ i * d))
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
        obtain ⟨x, hx₁, hx₂⟩ := pow_ModEq ht hq σ hs hp_mem F₁ hm (i.zero_lt_of_ne_zero hi₀) n
        have eq_aux₁ : (MvPowerSeries.coeff n) ((MvPowerSeries.map (σ ^ i)) (F.expand (q ^ i)
          (q_pow_neZero hq)) ^ b) = (MvPowerSeries.coeff n) ((MvPowerSeries.map (σ ^ i))
            ((MvPowerSeries.expand (q ^ i) (q_pow_neZero hq)) (F₁.map (R.subtype))) ^ b) := by
          simp
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
        refine .trans ?_ (MvPowerSeries.le_order_pow b)
        exact .trans (by simp) (nsmul_le_nsmul_right (ENat.one_le_iff_ne_zero.mpr <|
          MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr <| by
            rw [MvPowerSeries.constantCoeff_map, MvPowerSeries.constantCoeff_expand,
              constantCoeff_inv_add_RecurFun, map_zero]) b)
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
      R.subtype.eq_toAddMonoidHom, map_finsum _ <| coeff_subst_finite (.X x) g d, finsum_congr]
    intro m
    congr
    rw [MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X_pow]
    norm_cast
  simp [eq_aux]

include hs hp_mem hs₁ hs₂ in
/-- by above lemma we can deduce that all coefficient in g(F(X,Y)) is in `R`, since
  f(F(X,Y)) = f(X) + f(Y).-/
lemma RModEq_aux₂ [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0)
    {n : Fin 2 →₀ ℕ} {k : ℕ} (h : n.degree = k) :
    let F := (inv_add_RecurFun ht hq σ s hg hg_unit)
    (h_ind : ∀ m < k, ∀ (n : Fin 2 →₀ ℕ), n.degree = m → F.coeff n ∈ R) → (g.subst F).coeff n ∈ R := by
  intro F h_ind
  have F_def : F = (inv_add_RecurFun ht hq σ s hg hg_unit) := rfl
  obtain h₀ := RModEq_aux ht hq σ hs hp_mem s hs₁ hs₂ hg hg_unit hs0 h h_ind
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
        (RModEq_aux₂ ht hq σ hs hp_mem s hs₁ hs₂ hg hg_unit hs0 h hk))

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
  PowerSeries.constantCoeff_subst_zero (constantCoeff_RecurFun ..) rfl

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

include ht hs hp_mem in
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
  obtain ⟨x, hx₁, hx₂⟩ := pow_ModEq' ht hq σ hs hp_mem G₁ hm (i.zero_lt_of_ne_zero hi)
    (Finsupp.single () n)
  use x
  rw [SetLike.mem_coe] at hx₁
  simp [hx₁, hx₂, ← map_expand]
  rw [← map_pow, ← map_pow,← map_pow ((MvPowerSeries.map R.subtype))]
  erw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  simp only [Subring.subtype_apply]
  congr! 2
  rw [pow_mul]

include hs hp_mem hs₁ hs₂ in
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
  have one_le_order_G : 1 ≤ PowerSeries.order G := PowerSeries.one_le_order (constantCoeff_G ..)
  have order_G_pow (b : ℕ) : b ≤ PowerSeries.order (G ^ b) := by
    refine .trans ?_ (PowerSeries.le_order_pow _ b)
    rw [nsmul_eq_mul]
    exact le_mul_of_one_le_right' one_le_order_G
  have has_subst_G : PowerSeries.HasSubst G :=
    PowerSeries.HasSubst.of_constantCoeff_zero <| constantCoeff_G ..
  have le_order_aux₁ (b : ℕ) : b ≤ ((PowerSeries.expand (q ^ b) (q_pow_neZero hq))
    (PowerSeries.subst G (RecurFun ht hq σ s hg))).order := by
    rw [PowerSeries.order_expand]
    have : b ≤ q ^ b := (Nat.lt_pow_self (one_lt_q ht hq)).le
    have aux : q ^ b ≤ q ^ b • PowerSeries.order (PowerSeries.subst G (RecurFun ht hq σ s hg)) := by
      simp
      exact le_mul_of_one_le_right' (PowerSeries.one_le_order <|
        PowerSeries.constantCoeff_subst_zero (constantCoeff_G .. ) (constantCoeff_RecurFun ..))
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
    (coeff_mem_aux ht hq σ hs hp_mem hi₀ (constantCoeff_G ..) h_ind)
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
    have : 1 ≤ PowerSeries.order (G ^ q ^ i) := PowerSeries.one_le_order <| by
      erw [map_pow, constantCoeff_G .., zero_pow (q_pow_neZero hq)]
    refine .trans ?_ (PowerSeries.le_order_pow _ b)
    have : b ≤ b • PowerSeries.order (G ^ q ^ i) := by
      simpa using le_mul_of_one_le_right' this
    refine .trans (by norm_cast) this
  · intro b hb
    simp at hb
    apply PowerSeries.coeff_of_lt_order
    rw [PowerSeries.expand_smul]
    refine (ENat.add_one_le_iff (ENat.coe_ne_top n)).mp (.trans ?_ (PowerSeries.le_order_smul))
    rw [PowerSeries.order_expand]
    exact .trans (.trans (by norm_cast) (le_self_nsmul b.cast_nonneg' (q_pow_neZero hq)))
      (nsmul_le_nsmul_right (order_G_pow _) _)
  · exact PowerSeries.Summable.increase_order fun n =>  .trans (.trans le_rfl
      (PowerSeries.le_order_pow_n _ (by erw [map_pow, constantCoeff_G, zero_pow
        (q_pow_neZero hq)]))) PowerSeries.le_order_smul
  · apply PowerSeries.Summable.increase_order fun b => by
      rw [PowerSeries.expand_smul]
      refine .trans ?_ PowerSeries.le_order_smul
      rw [PowerSeries.order_expand]
      refine .trans (le_self_nsmul (b.cast_nonneg') (q_pow_neZero hq))
        (nsmul_le_nsmul_right (order_G_pow b) (q ^ i))
  · exact PowerSeries.Summable.increase_order fun n =>
      .trans (PowerSeries.le_order_pow_n _ (constantCoeff_G ..)) PowerSeries.le_order_smul
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

include hs hp_mem hs₁ hs₂ in
lemma coeff_g_G_mem [UniformSpace K] [T2Space K] [DiscreteUniformity K] (hs0 : s 0 = 0) {n : ℕ}:
    let f_g' := RecurFun ht hq σ s hg'
    let G := (inv_RecurFun ht hq σ s hg hg_unit).subst f_g'
    (h_ind : ∀ m < n, (PowerSeries.coeff m) G ∈ R) → PowerSeries.coeff n (g.subst G) ∈ R := by
  intro f_g' G h_ind
  obtain h := coeff_g_G_mem_aux ht hq σ hs hp_mem s hs₁ hs₂ hg hg_unit hg' hs0 h_ind
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

include hs hp_mem hs₁ hs₂ in
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
        (coeff_g_G_mem ht hq σ hs hp_mem s hs₁ hs₂ hg hg_unit hg' hs0 hk))

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
    apply PowerSeries.constantCoeff_subst_zero
    simp [h₀]
    simp [zero_pow (q_pow_neZero hq)]

include ht hs hp_mem in
lemma PartIII.coeff_mem_aux {i b n : ℕ} {h : PowerSeries R} (hi : i ≠ 0):
    (σ ^ i) ((PowerSeries.coeff n) ((PowerSeries.map R.subtype) ((PowerSeries.expand (q ^ i)
      (q_pow_neZero hq)) h) ^ b)) - (PowerSeries.coeff n) ((PowerSeries.map R.subtype)
      h ^ (q ^ i * b)) ∈ ⇑R.subtype '' ↑(I ^ (multiplicity q b + 1)) := by
  simp_rw [← map_pow, PowerSeries.coeff_map]
  rw [Subring.subtype_apply, Subring.subtype_apply]
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd q b
  obtain ⟨x, hx₁, hx₂⟩ := pow_ModEq' ht hq σ hs hp_mem h hm (i.zero_lt_of_ne_zero hi)
    (Finsupp.single () n)
  use x
  rw [SetLike.mem_coe] at hx₁
  simp [hx₁, hx₂, ← map_expand]
  rw [← map_pow, ← map_pow,← map_pow ((MvPowerSeries.map R.subtype))]
  erw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  simp only [Subring.subtype_apply]
  congr

include hs hp_mem hs₁ hs₂ in
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
    refine .trans (.trans ?_ (PowerSeries.le_order_pow _ b)) (PowerSeries.le_order_map _)
    have : 1 ≤ ((PowerSeries.expand (q ^ i) (q_pow_neZero hq)) h).order := by
      apply PowerSeries.one_le_order
      rw [PowerSeries.constantCoeff_expand, h₀]
    refine .trans (by simp) (nsmul_le_nsmul_right this b)
  have le_order_aux₂ (i b : ℕ) : b ≤ PowerSeries.order
    ((PowerSeries.map R.subtype) h ^ (q ^ i * b)) := by
    rw [← map_pow]
    refine .trans (.trans ?_ (PowerSeries.le_order_pow _ _)) (PowerSeries.le_order_map _)
    have le_aux : b ≤ q ^ i * b :=
      Nat.le_mul_of_pos_left b <|  Nat.pow_pos (Nat.pos_of_ne_zero (q_neZero hq))
    refine .trans ?_ (nsmul_le_nsmul_right (PowerSeries.one_le_order h₀) (q ^ i * b))
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_one]
    norm_cast
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
    refine .trans (le_expand_aux b <| PowerSeries.constantCoeff_subst_zero (by simp [h₀])
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
    (PartIII.coeff_mem_aux ht hq σ hs hp_mem hi₀)
  · intro a ha
    have a_mem : ⟨a, image_of_incl_mem a ha⟩ ∈ I ^ (multiplicity q b + 1) := by
      obtain ⟨a', ha'₁, ha'₂⟩ := ha
      simp_rw [← ha'₂]
      simpa using ha'₁
    obtain h1 := coeff_RecurFun_mul_mem_i ht hq σ s hs₁ hs₂ hg b 1 ⟨a, image_of_incl_mem a ha⟩ a_mem
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
include hs hp_mem hs₁ hs₂ in
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
  refine Subring.sub_mem R ?_ (PartIII.coeff_tsum_mem ht hq σ hs hp_mem s hs₁ hs₂ hg h₀ n hs₀)
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

end inv_add_RecurFun

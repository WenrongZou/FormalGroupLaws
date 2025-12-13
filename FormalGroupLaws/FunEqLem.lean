import FormalGroupLaws.Basic
import FormalGroupLaws.BasicLem
import Mathlib.RingTheory.PowerSeries.PiTopology
import FormalGroupLaws.MvPowerSeries
import Mathlib.Algebra.CharP.Lemmas

noncomputable section

open MvPowerSeries Classical Finset FormalGroup
open scoped WithPiTopology


namespace FunctionalEquationIntegralityLemma

/- The basic ingredients in this section are `R ⊆ K, σ : K → K, I ⊆ R, p, q, s₁, s₂ ⋯`,
  where `R` is a subring of `K`, `σ` is a ring homomorphism of `K`, which stablize `A`,
  `I` is an ideal of `A`, `p` is a prime number and `q` is a power of `p`, `s_i` are
  elements of `K`. -/


variable {K : Type*} [CommRing K] {R : Subring K} {I : Ideal R} {τ : Type*}
  {p t q: ℕ} (hp_prime : Nat.Prime p) (hn : t ≠ 0) (hq : q = p ^ t)
  (σ : K →+* K)  (hs : ∀ (a : R), σ a ∈ R)
  (hs_mod : ∀ (a : R), (⟨σ a, hs a⟩) ≡  (a ^ q) [SMOD I])
  (hp : (p : R) ∈ I) (s : ℕ → K)
  (hs_i : ∀ i, ∀ (a : K), a ∈ (Set.image (algebraMap R K) I) → s i * a ∈ R)
  (hs_i' :∀ r : ℕ, ∀ b : K,
    (∀ a ∈ I ^ r, b * (algebraMap R K a) ∈ Set.image (algebraMap R K) I) →
    ∀ a ∈ I ^ r, (σ b) * (algebraMap R K a) ∈ Set.image (algebraMap R K) I)

  -- (hs_i1 : ∀ r : ℕ, ∀ b : K, (({b}) *  (I ^ r : Ideal R) : Set R)  ⊆ (I : Set R) →
  --    {(σ b)} * ((I ^ r : Ideal R) : Set R) ⊆ (I : Set R))

variable {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
  (hg_unit : IsUnit (g.coeff 1))

include hp_prime hq in
/-- under our assumption, `∀ x ∈ ℕ, q ^ x ≠ 0`-/
lemma q_pow_neZero {x : ℕ} : q ^ x ≠ 0 :=
  pow_ne_zero x (hq ▸ pow_ne_zero t <| Nat.Prime.ne_zero hp_prime)

lemma mem_image_aux {y : R} {I : Ideal R} (hy : ↑y ∈ Set.image (algebraMap R K) I) : y ∈ I := by
  simp at hy
  obtain ⟨t, ht, ht1, ht2⟩ := hy
  have eq_aux : ⟨t, ht⟩ = y := by
    exact SetLike.coe_eq_coe.mp ht2
  simp [←eq_aux, ht1]

lemma mem_image_aux₂ {y : K} {I : Ideal R} (hy : y ∈ Set.image (algebraMap R K) I) : y ∈ R := by
  simp at hy
  obtain ⟨t, ht, ht1, ht2⟩ := hy
  rw [←ht2]
  exact ht




-- the following is the coefficient of f_g
def RecurFunAux (hg : PowerSeries.constantCoeff g = 0): ℕ → K
  | 0 => 0
  -- | 1 => PowerSeries.coeff R 1 g
  | k + 1 =>
    PowerSeries.coeff (k + 1) g + ∑ j ∈ (Icc 1 (multiplicity q (k + 1))).attach,
      have aux : ((k + 1) / (q ^ (j : ℕ))) < k + 1 := by
        have hj1 : ↑j ≥ (1 : ℕ) := by
          obtain hj1 := j.property
          simp_all only [ge_iff_le, Subtype.forall, SubmonoidClass.mk_pow, Set.mem_image,
            SetLike.mem_coe, Subtype.exists, mem_Icc]
        have le_aux : q ^ (j : ℕ) > 1 := by
          have q_gt_one : q > 1 := by
            rw [hq]
            exact Nat.one_lt_pow hn (Nat.Prime.one_lt hp_prime)
          have j_ne : (j : ℕ) ≠ 0 := by
            linarith
          exact Nat.one_lt_pow j_ne q_gt_one
        exact Nat.div_lt_self (by linarith) le_aux
      (s j) * σ^[j] (RecurFunAux hg ((k + 1) / (q ^ (j : ℕ))))


-- This is f_g
def RecurFun : PowerSeries K := PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg)

/-- constant coefficient of `f_g` is zero-/
lemma constantCoeff_RecurFun_zero :
    PowerSeries.constantCoeff (RecurFun hp_prime hn hq σ s hg) = 0 := by
  simp [RecurFun, RecurFunAux]

/- First coefficient of `f_g` is equal to `coeff 1 g`. -/
lemma coeff_RecurFun_one : (RecurFun hp_prime hn hq σ s hg).coeff 1 = g.coeff 1 := by
  simp [RecurFun, RecurFunAux]
  have empty_aux : (multiplicity q 1) = 0 := by
    refine multiplicity_eq_zero.mpr ?_
    have q_ge : q ≥ 2 := by
      rw [hq]; exact le_trans (Nat.Prime.two_le hp_prime) <| Nat.le_self_pow hn p
    exact Nat.not_dvd_of_pos_of_lt (by linarith) q_ge
  rw [empty_aux, show Icc 1 0 = ∅ by rfl]
  simp


/-- First coefficient of `f_g` is unit-/
lemma coeff_RecurFun_unit (hg_unit : IsUnit ((PowerSeries.coeff 1) g)) :
    IsUnit ((RecurFun hp_prime hn hq σ s hg).coeff 1) := by
  rw [coeff_RecurFun_one]
  obtain ⟨b, hb₁, hb₂⟩ := isUnit_iff_exists.mp hg_unit
  exact isUnit_iff_exists.mpr ⟨b, by norm_cast⟩


/- Functional equation lemma.
  Let the notation defined as above, let `g(X) = ∑_{i=1}^∞ b_i X^i`, `g_bar (X) = ∑_{i=1}^∞ (b_bar i) X^i`.
  be two power series in one variable over `A`, and suppose that `b₁` is invertible in `A`. Then we have:
  (i) the power series F_g(X,Y)=f_g⁻¹(f_g(X)+f_g(Y)) has its coefficients in `A`.
  (ii) the power series `f_g⁻¹ (f_g_bar (X))` has its coefficient in `A`.
  (iii) if `h(X)=∑_{n=1}^∞ c_n X^n` is a power series with coefficients in `A`, then there is a
  power series `h^hat (X) = ∑_{n=1}^∞ c_n^hat X^n` with `c_n^hat ∈ A`, `n=1,2,…`, such that
  `f_g(h(X))=f_{h^hat}(X)`.
  (iv) if `α(X) ∈ A⟦X⟧, β(X) ∈ K⟦X⟧` are two power series, and `r ∈ ℕ, r ≥ 1`, then we have
  `α(X) ≡ β(X) [MOD I^r • A⟦X⟧] ↔ f_g(α(X)) ≡ f_g (β(X)) [MOD I^r • A⟦X⟧]`.

  If `f_g(X)` and `f_{g_bar}(X)` are power series obtained by the recursion equation with
  everything the same except possibly `g(X) ≠ g_bar(X)`, then we shall say that
  `f_g(X)` and `f_{g_bar}(X)` satisfy the same type of functional equation.-/

-- /-- If `f_g(X)` and `f_{g_bar}(X)` are power series obtained by the recursion equation with
--   everything the same except possibly `g(X) ≠ g_bar(X)`, then we shall say that
--   `f_g(X)` and `f_{g_bar}(X)` satisfy the same type of functional equation. -/


include I hs_i' in
lemma sigma_mem_aux : ∀ (r : ℕ), ∀ b : K,
  (∀ a ∈ I ^ r, b * (algebraMap R K a) ∈ Set.image (algebraMap R K) I) →
  (∀ j : ℕ, ∀ a ∈ I ^ r, ((σ^j) b) * (algebraMap R K a) ∈ Set.image (algebraMap R K) I) := by
  intro r b h₁ j
  induction j with
  | zero =>
    intro a a_mem
    simp
    obtain h₂ := h₁ a a_mem
    simp at h₂
    exact h₂
  | succ k hk =>
    intro a a_mem
    have eq_aux : (σ ^ (k + 1)) b * (algebraMap (↥R) K) a =
      σ ((σ ^ k) b) * (algebraMap (↥R) K) a := by
      simp [Function.iterate_succ_apply' (⇑σ) k b]
    rw [eq_aux]
    obtain h₂ := hs_i' r ((σ ^ k) b) hk a a_mem
    exact h₂



lemma ideal_pow_mem {I : Ideal R} {r : ℕ} {x : K} :  (∀ b ∈ I^r, x * b ∈ R)
    → (∀ c ∈ I^r * I, x * c ∈ Set.image (algebraMap R K) I) := fun h c hc => by
  refine Submodule.mul_induction_on hc ?_ ?_
  · intro m hm n hn
    obtain h1 := h m hm
    have aux : x * ↑(m * n) = x * (↑m) * n := by
      norm_num
      ring
    rw [aux]
    have aux2 : x * ↑m * ↑n ∈ R := by
      refine Subring.mul_mem R (h m hm) ?_
      exact SetLike.coe_mem n
    have aux3 : ⟨x * ↑m * ↑n, aux2⟩ ∈ I := by
      have eq_aux :  ⟨x * ↑m * ↑n, aux2⟩ = ⟨x * m, h1⟩ * n := rfl
      rw [eq_aux]
      exact Ideal.mul_mem_left I ⟨x * ↑m, h1⟩ hn
    refine (Set.mem_image (⇑(algebraMap (↥R) K)) (↑I) (x * ↑m * ↑n)).mpr ?_
    use ⟨x * ↑m * ↑n, aux2⟩
    exact ⟨aux3, rfl⟩
  · intro a b ha hb
    obtain ⟨y1, hy1, hy2⟩ := ha
    obtain ⟨z1, hz1, hz2⟩ := hb
    have eq_aux : x * ↑(a + b) = x * ↑a + x * ↑b := by
      norm_num; ring
    rw [eq_aux]
    simp
    use (y1 + z1)
    have mem_aux' : (y1 : K) + ↑z1 ∈ R := add_mem (SetLike.coe_mem y1) (SetLike.coe_mem z1)
    use mem_aux'
    constructor
    exact (Submodule.add_mem_iff_right I hy1).mpr hz1
    rw [←hy2, ←hz2]
    exact rfl



lemma ideal_pow_mem' {I : Ideal R} {r s: ℕ} {x : K} (hs : s > r):  (∀ b ∈ I^r, x * b ∈ R)
  → (∀ c ∈ I^s, x * c ∈ Set.image (algebraMap R K) I) :=
  fun h c hc => (ideal_pow_mem h) c ((Ideal.pow_le_pow_right hs) hc)


lemma multiplicity_aux (n i q: ℕ) (hq : q > 1)
  (hn : n > 0) (hi1 : i ≤ multiplicity q n) (hi2 : i ≥ 1) :
  multiplicity q (n / q ^ i) < multiplicity q n := by
  have eq_aux : multiplicity q (n / q ^ i) = multiplicity q n - i := by
    apply multiplicity_eq_of_dvd_of_not_dvd
    refine Nat.dvd_div_of_mul_dvd ?_
    rw [mul_comm, ←pow_add, show (multiplicity q n - i + i) = multiplicity q n by omega]
    exact pow_multiplicity_dvd q n
    by_contra hc
    have dvd_aux : q ^ i ∣ n := by
      exact pow_dvd_of_le_multiplicity hi1
    obtain h1 := Nat.mul_dvd_of_dvd_div dvd_aux hc
    rw [←pow_add, show (i + (multiplicity q n - i + 1)) = multiplicity q n + 1 by omega ] at h1
    have not_dvd : ¬ q ^ (multiplicity q n + 1) ∣ n := by
      refine FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt ?_ ?_
      refine Nat.finiteMultiplicity_iff.mpr ?_
      omega
      linarith
    contradiction
  rw [eq_aux]
  omega



include hs_i hs_i'  in
/-- Let a_n be the coefficient of f_g, then a_n * I^r ⊆ R, where r is the multiplicity of
  q in n. -/
lemma coeff_RecurFun_mul_mem (n : ℕ) :
  ∀ (x : R), x ∈ I ^ (multiplicity q n) →
    (PowerSeries.coeff n (RecurFun hp_prime hn hq σ s hg)) * x ∈ R := by
  generalize h : (multiplicity q n) = m
  induction m using Nat.strongRecOn generalizing n with
  | ind k hk =>
    intro x hx
    simp [RecurFun]
    unfold RecurFunAux
    by_cases hn0 : n = 0
    · -- prove the case for n = 0
      simp [hn0, Subring.zero_mem R]
    · -- the case for n ≥ 1
      have neq : n = n - 1 + 1 := by omega
      rw [neq]
      simp
      rw [←neq, add_mul]
      refine Subring.add_mem R ?_ ?_
      · -- prove the first component is in R
        exact Subring.mul_mem R (SetLike.coe_mem _) (SetLike.coe_mem _)
      · -- second component is in R
        have aux : (∑ i ∈ (Icc 1 (multiplicity q n)), s ↑i * (⇑σ)^[↑i]
          (RecurFunAux hp_prime hn hq σ s hg (n / q ^ ↑i))) * x ∈ R := by
          rw [sum_mul]
          refine Subring.sum_mem R ?_
          intro i hi
          rw [mul_assoc]
          have mem_aux2 : ((σ ^ i) (RecurFunAux hp_prime hn hq σ s hg (n / q ^ i)) * ↑x)
            ∈ Set.image (algebraMap R K) I := by
            have aux : ∀ b ∈ I ^ multiplicity q n, (RecurFunAux hp_prime hn hq σ s hg (n / q ^ i))
               * (algebraMap R K b)
              ∈ ⇑(algebraMap (↥R) K) '' ↑I := by
              intro b hb
              rw [h] at hb
              have lt_aux : multiplicity q (n / q ^ i) < k :=
                h.symm ▸  multiplicity_aux n i q (hq ▸ Nat.one_lt_pow hn <| Nat.Prime.one_lt hp_prime)
                  (by omega) (mem_Icc.mp hi).2 (mem_Icc.mp hi).1
              have le_aux : multiplicity q (n / q ^ i) ≤ k := by linarith
              have b_mem : b ∈ I ^ multiplicity q (n / q ^ i) :=
                SetLike.le_def.mp (Ideal.pow_le_pow_right le_aux (I := I)) hb
              obtain h2 := ideal_pow_mem' lt_aux (hk _ lt_aux (n / q ^ i) rfl) b hb
              rw [RecurFun, PowerSeries.coeff_mk, show ↑b = (algebraMap R K) b  by rfl] at h2
              exact h2
            rw [←h] at hx
            obtain h₁ := sigma_mem_aux σ hs_i' (multiplicity q n) _ aux i x hx
            have eq_aux : (algebraMap (↥R) K) x = (x : K) := rfl
            rw [eq_aux] at h₁
            exact h₁
          have mem_aux : ((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s hg (n / q ^ i)) * ↑x)
            ∈ R := mem_image_aux₂ mem_aux2
          have aux : ((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s hg (n / q ^ i)) * ↑x)
            ∈ Set.image (algebraMap R K) I := by
            simp at mem_aux2
            simp [mem_aux2]
          obtain h1 := hs_i i _ aux
          simp [h1]
        rw [←sum_attach] at aux
        exact aux

include hs_i hs_i' in
lemma coeff_RecurFun_mul_mem_i (n i: ℕ) :
  ∀ (x : R), x ∈ I ^ (multiplicity q n + i) →
    (PowerSeries.coeff n (RecurFun hp_prime hn hq σ s hg)) * x ∈ (algebraMap R K )'' ↑(I ^ i) := by
  intro x hx
  rw [pow_add] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  intro y hy z hz
  obtain h₁ := coeff_RecurFun_mul_mem hp_prime hn hq σ s hs_i hs_i' hg _ y hy
  rw [Subring.coe_mul, ←mul_assoc]


  sorry

  sorry

include hs_i hs_i'  in
/-- Let a_n be the coefficient of f_g, then a_n * I^r ⊆ R, where r is the multiplicity of
  q in n. -/
lemma coeff_RecurFun_mul_mem' (n i : ℕ) :
  ∀ (x : K), x ∈ (algebraMap R K) '' ↑(I ^ ((multiplicity q n) + i)) →
    (PowerSeries.coeff n (RecurFun hp_prime hn hq σ s hg)) * x ∈ ((algebraMap (↥R) K) '' ↑(I^i))
  := by
  intro x hx
  rw [pow_add] at hx
  simp at hx
  obtain ⟨a, ha, ha_mem, ha_eq⟩ := hx
  rw [← ha_eq]

  -- induction i with
  -- | zero =>
  --   rw [pow_zero]
  --   have aux : ⇑(algebraMap (↥R) K) '' ↑(1 : Ideal R) = R := by
  --     ext y
  --     simp
  --     constructor
  --     · intro h
  --       obtain ⟨a, ha, ha'⟩ := h
  --       rw [←ha']
  --       exact ha
  --     · intro hy
  --       use y, hy; rfl
  --   rw [aux]
  --   simp at hx
  --   obtain ⟨a, ha, ha_eq₁, ha_eq₂⟩ := hx
  --   obtain ha' := coeff_RecurFun_mul_mem hp_prime hn hq σ s hs_i hs_i' hg _ _ ha_eq₁
  --   rw [← ha_eq₂]
  --   exact ha'
  -- | succ k ih =>
  --   simp at hx
  --   obtain ⟨a, ha, ha_eq₁, ha_eq₂⟩ := hx
  --   rw [←ha_eq₂]

  --   sorry
  sorry



-- ask whether there is a way to define ∑' i start at 1. and the instance problem.
/- definition of recursion formula in the following sense.
  f_g (X) = g (X) + ∑ i = 0 to ∞, s (i + 1) * (σ ^ (i + 1)) f _g (X ^ (q ^ (i + 1)))
  -/

lemma coeff_infty_sum [TopologicalSpace K] [T2Space K]
  (f : ℕ → PowerSeries K) (hf : Summable f) (n : ℕ):
  PowerSeries.coeff n (∑' (i : ℕ), f i) = ∑' (i : ℕ), PowerSeries.coeff n (f i) :=
  Summable.map_tsum hf (PowerSeries.coeff n)
    <| PowerSeries.WithPiTopology.continuous_coeff K n



include hp_prime hn hq hg in
lemma HasSum_aux [TopologicalSpace K] (hs0 : s 0 = 0) :
    HasSum (fun i ↦ PowerSeries.C (s i) * (PowerSeries.map (σ ^ i))
    (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) (RecurFun hp_prime hn hq σ s hg)))
  (RecurFun hp_prime hn hq σ s hg - (PowerSeries.map (algebraMap (↥R) K)) g) := by
  have qneq : q ≠ 0 := hq ▸ pow_ne_zero t <| Nat.Prime.ne_zero hp_prime
  have qneq' : q ≠ 1 := by
    rw [hq]
    refine Ne.symm <| Nat.ne_of_lt <| Nat.one_lt_pow hn <| Nat.Prime.one_lt hp_prime
  obtain q_pow_ne := fun {x : ℕ} => pow_ne_zero x qneq
  rw [RecurFun]
  refine
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr
      <| fun d => by
    simp
    refine tendsto_atTop_nhds.mpr ?_
    intro U hU₁ hU₂
    use Icc 1 (multiplicity q d)
    intro N' hN'
    have eq_aux : ∑ x ∈ N', s x *  (⇑σ)^[x] ((PowerSeries.coeff d)
      (PowerSeries.subst ((PowerSeries.monomial (q ^ x)) 1)
      (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg))))
      = (PowerSeries.coeff d) ((RecurFun hp_prime hn hq σ s hg) -
      (PowerSeries.map (algebraMap R K) g)) := by
      simp [RecurFun]
      by_cases hd : d ≤ 1
      · if d_zero : d = 0 then
        conv => rhs; simp [d_zero, RecurFunAux, hg]
        apply Finset.sum_eq_zero
        intro x hx
        have zero_aux : (PowerSeries.coeff d) (PowerSeries.subst ((PowerSeries.monomial
          (q ^ x)) (1 : K)) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg)))
          = 0 := by
          rw [PowerSeries.coeff_subst']
          apply finsum_eq_zero_of_forall_eq_zero <| fun m => by
            if hm : m = 0 then simp [hm, RecurFunAux]
            else
            rw [PowerSeries.monomial_pow, PowerSeries.coeff_monomial, if_neg]
            simp
            · simp [d_zero, hm]
              intro hq
              aesop
          refine PowerSeries.HasSubst.monomial' q_pow_ne 1
        simp [zero_aux]
        else
        have deq : d = 1 := by grind
        conv =>
          rhs; simp [deq, RecurFunAux]
        have eq_aux : (multiplicity q 1) = 0 := by
          refine multiplicity_of_one_right ?_
          simp [hq]
          exact ⟨Nat.Prime.ne_one hp_prime, hn⟩
        have empty_aux : (Icc 1 0) = ∅ := rfl
        rw [eq_aux, empty_aux]
        simp
        rw [@Algebra.algebraMap_ofSubring_apply, sub_self]
        apply Finset.sum_eq_zero <| fun x hx => by
          if hx' : x = 0 then simp [hx', hs0]
          else
          have zero_aux : (PowerSeries.coeff d) (PowerSeries.subst ((PowerSeries.monomial
          (q ^ x)) (1 : K)) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg)))
          = 0 := by
            rw [PowerSeries.coeff_subst']
            apply finsum_eq_zero_of_forall_eq_zero <| fun m => by
              rw [PowerSeries.monomial_pow, PowerSeries.coeff_monomial, if_neg]
              simp
              simp [deq]
              if hm : m = 0 then simp [hm]
              else
              have aux : m * q ^ x > 1 :=
                Right.one_lt_mul_of_le_of_lt (by grind)
                  <| Nat.one_lt_pow hx' <| by grind
              exact Nat.ne_of_lt aux
            exact PowerSeries.HasSubst.monomial' q_pow_ne 1
          simp [zero_aux]
      · nth_rw 2 [show d = d - 1 + 1 by grind]
        rw [RecurFunAux]
        rw [Finset.sum_attach ((Icc 1 (multiplicity q (d - 1 + 1)))) (fun j =>
          s j * (⇑σ)^[j] (RecurFunAux hp_prime hn hq σ s hg ((d - 1 + 1) / q ^ j)))]
        rw [←show d = d - 1 + 1 by grind]
        have eq_aux' : ∑ x ∈ N', s x * (⇑σ)^[x] ((PowerSeries.coeff d)
          (PowerSeries.subst ((PowerSeries.monomial (q ^ x)) 1)
          (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg)))) =
          ∑ x ∈ Icc 1 (multiplicity q d), s x * (⇑σ)^[x] (RecurFunAux hp_prime hn hq σ s hg (d / q ^ x)) := by
          have disj_aux : Disjoint (Icc 1 (multiplicity q d))
            (N' \ (Icc 1 (multiplicity q d))) := disjoint_sdiff
          have N'_eq : N' = (Icc 1 (multiplicity q d)).disjUnion (N' \ (Icc 1 (multiplicity q d))) disj_aux := by
            simp at hN'
            simp [hN']
          have eq_aux₂ : ∑ x ∈ Icc 1 (multiplicity q d), s x * (⇑σ)^[x] ((PowerSeries.coeff d)
            (PowerSeries.subst ((PowerSeries.monomial (q ^ x)) 1)
              (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg))))
            = ∑ x ∈ Icc 1 (multiplicity q d), s x * (⇑σ)^[x] (RecurFunAux hp_prime hn hq σ s hg (d / q ^ x)) := by
            apply Finset.sum_congr rfl <| fun x hx => by
              congr
              have monomial_eq : ((PowerSeries.monomial (q ^ x)) (1 : K) ^ (d / q ^ x)) =
                ((PowerSeries.monomial d)) 1 := by
                rw [PowerSeries.monomial_pow]
                simp
                congr
                simp at hx
                refine (Nat.dvd_iff_div_mul_eq d (q ^ x)).mp
                  <| pow_dvd_of_le_multiplicity hx.2
              rw [PowerSeries.coeff_subst', finsum_eq_single _ (d / q^x), PowerSeries.coeff_mk,
                monomial_eq]
              simp
              intro m hm
              simp [PowerSeries.monomial_pow, PowerSeries.coeff_monomial]
              intro hc
              have aux : m * q ^ x / q ^ x = m := by
                refine Nat.mul_div_left m <| Nat.pow_pos <| Nat.zero_lt_of_ne_zero qneq
              rw [hc, aux] at hm
              simp at hm
              refine PowerSeries.HasSubst.monomial' q_pow_ne _
          rw [N'_eq, Finset.sum_disjUnion, eq_aux₂]
          apply add_eq_left.mpr
          apply Finset.sum_eq_zero
          intro x hx
          simp at hx
          if hx_zero : x = 0 then simp [hx_zero, hs0]
          else
          have xgt_aux : x > multiplicity q d := hx.2 <| Nat.one_le_iff_ne_zero.mpr hx_zero
          have zero_aux : (PowerSeries.coeff d) (PowerSeries.subst ((PowerSeries.monomial (q ^ x)) (1 : K))
            (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg))) = 0 := by
            rw [PowerSeries.coeff_subst']
            apply finsum_eq_zero_of_forall_eq_zero
            intro m
            simp
            rw [PowerSeries.monomial_pow, PowerSeries.coeff_monomial, if_neg, mul_zero]
            by_contra hc
            have aux : multiplicity q d > multiplicity q d := calc
              _ ≥ x := by
                apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
                refine Nat.finiteMultiplicity_iff.mpr ?_
                · omega
                · rw [hc]
                  exact Nat.dvd_mul_left (q ^ x) m
              _ > _ := by
                linarith
            linarith
            refine PowerSeries.HasSubst.monomial' q_pow_ne 1
          simp [zero_aux]
        rw [eq_aux']
        exact Eq.symm <| add_sub_cancel_left _ _
    simp [eq_aux, RecurFun, PowerSeries.coeff_mk, hU₁]


include hp_prime hn hq hg in
lemma summable_aux [TopologicalSpace K] (hs0 : s 0 = 0) : Summable
  (fun i ↦
    PowerSeries.C (s i) *
      (PowerSeries.map (σ ^ i))
        (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s hg))))
  := by
  use (RecurFun hp_prime hn hq σ s hg - (PowerSeries.map (algebraMap (↥R) K)) g)
  exact HasSum_aux hp_prime hn hq σ s hg hs0

include hp_prime hn hq hg in
lemma summable_X₀ [TopologicalSpace K] (hs0 : s 0 = 0):
    let f := (RecurFun hp_prime hn hq σ s hg)
    Summable (fun i ↦ (s i • ((PowerSeries.subst (X₀ ^ q ^ i) f).map (σ ^ i)))) := sorry

include hp_prime hn hq hg in
lemma summable_X₁ [TopologicalSpace K] (hs0 : s 0 = 0):
    let f := (RecurFun hp_prime hn hq σ s hg)
    Summable (fun i ↦ (s i • ((PowerSeries.subst (X₁ ^ q ^ i) f).map (σ ^ i)))) := sorry

/- this is the function equation that `f_g` satisfies, namely
  $f_g(X) = g(X) + ∑' s_i * σ^i f(X^{q^i})$-/
theorem Fun_eq_of_RecurFun [TopologicalSpace K] [T2Space K] (hs0 : s 0 = 0) :
    let f := (RecurFun hp_prime hn hq σ s hg)
    f = (PowerSeries.map (algebraMap R K) g) +
    ∑' (i : ℕ), ((PowerSeries.C (s i)) * (PowerSeries.map (σ^i)
    (f.subst (PowerSeries.monomial (q ^ (i)) 1) ))) := by
  intro f
  rw [HasSum.tsum_eq <| HasSum_aux hp_prime hn hq σ s hg hs0]
  ring

theorem Fun_eq_of_RecurFun_XY [UniformSpace K] [T2Space K] [DiscreteUniformity K]
  (hs0 : s 0 = 0) {x : Fin 2} :
    let f := (RecurFun hp_prime hn hq σ s hg)
    f.subst (X x) = g.subst (X x) + ∑' (i : ℕ), (s i • ((PowerSeries.subst ((X x) ^ q ^ i) f).map (σ ^ i)))
    := by
  /- this should be easy using the theorem tsum_subst-/
  intro f
  have f_def : f = (RecurFun hp_prime hn hq σ s hg) := rfl
  obtain has_subst_aux := PowerSeries.HasSubst.X (x : Fin 2) (S := K)
  nth_rw 1 [f_def, Fun_eq_of_RecurFun hp_prime hn hq σ s hg hs0]
  rw [PowerSeries.subst_add has_subst_aux, tsum_subst _ has_subst_aux]
  congr! 1
  · rw [PowerSeries.map, @map_algebraMap_eq_subst_X, PowerSeries.subst, subst_comp_subst_apply
      HasSubst.X <| PowerSeries.HasSubst.const has_subst_aux, PowerSeries.subst]
    congr
    funext s
    rw [subst_X <| PowerSeries.HasSubst.const has_subst_aux]
  · apply tsum_congr <| fun i => by
      rw [←PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul has_subst_aux,
        ←f_def, ←PowerSeries.subst_map has_subst_aux]
      congr! 2
      rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.monomial' (q_pow_neZero hp_prime hq) 1)
        has_subst_aux]
      apply subst_congr
      funext d
      rw [←PowerSeries.X_pow_eq, PowerSeries.subst_pow has_subst_aux,
        PowerSeries.subst_X has_subst_aux ]
  exact summable_aux hp_prime hn hq σ s hg hs0


include hs in
lemma sigma_pow_mem : ∀ (j : ℕ), ∀ (a : R), (σ ^ j) a ∈ R := fun j => by
  induction j with
  | zero =>
    simp
  | succ k ih =>
    intro a
    rw [RingHom.coe_pow, Function.iterate_succ_apply']
    exact hs ⟨_, ih _⟩

include hs in
lemma coeff_aux_mem {G : MvPowerSeries τ R} : ∀ (j : ℕ), ∀ (n : τ →₀ ℕ),
  (MvPowerSeries.map (σ ^ j)) (G.ofSubring _) n ∈ R := fun j n => sigma_pow_mem σ hs j (G n)

-- include hs in
-- theorem pow_ModEq {G : MvPowerSeries (Fin 2) R} {n l m: ℕ} (hl : l > 0) :
--   G ^ (n * q ^ l) ≡ (((subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)] G) ^ n).ofSubring.map (σ^l)).toSubring _
--   (coeff_aux_mem σ hs l) [SMOD (I^((multiplicity q n) + 1)).MvPowerSeries] := by
--   generalize h : multiplicity q n = r
--   induction r using Nat.strongRecOn generalizing n with
--   | ind k hk =>

--     sorry

include hp in
lemma p_pow_mod_p {G : MvPowerSeries (Fin 2) R} {l : ℕ} (l_pos : 0 < l) :
    G ^ (q ^ l) ≡ ((subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)] G).ofSubring.map (σ^l)).toSubring _
    (coeff_aux_mem σ hs l) [SMOD I.MvPowerSeries] := by
  apply SModEq.sub_mem.mpr
  simp [Ideal.MvPowerSeries]
  intro n
  have aux {f g : MvPowerSeries (Fin 2) R} {n : Fin 2 →₀ ℕ} :
      (f - g) n = coeff n f - coeff n g := by rfl
  rw [aux]
  -- have eq_aux : (coeff n) (((MvPowerSeries.map (σ ^ l)) (ofSubring R
  --   (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l] G))).toSubring R (coeff_aux_mem σ hs l))
  --   = ⟨(σ ^ l) (coeff n (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l] G)), sigma_pow_mem σ hs l
  --     ((coeff n) (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l] G))⟩ := sorry
  sorry

include hs hp hq hp_prime hn in
/-- Forall `r m ∈ ℕ` and `G(X,Y) ∈ R⟦X,Y⟧`, we have that
  $G^{q^r m q^l} ≡ (σ^l G(X^{q^l},Y^{q^l}))^n$. -/
theorem pow_ModEq {G : MvPowerSeries (Fin 2) R} {r l m: ℕ} (hl : l > 0) :
    G ^ ((q ^ r * m) * q ^ l) ≡ (((subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)] G) ^ (q ^ r * m)).ofSubring.map (σ^l)).toSubring _
    (coeff_aux_mem σ hs l) [SMOD (I^(r + 1)).MvPowerSeries] := by
  have mod_aux : G ^ (q ^ r * q ^ l) ≡ (((subst ![X₀ ^ (q ^ l), X₁ ^ (q ^ l)] G) ^ (q ^ r)).ofSubring.map (σ^l)).toSubring _
    (coeff_aux_mem σ hs l) [SMOD (I^(r + 1)).MvPowerSeries] := by
    induction r with
    | zero =>
      simp
      refine SModEq.trans (p_pow_mod_p σ hs hp hl) (by congr; simp)
    | succ k ih =>
      obtain ⟨a, a_mem, ha⟩ := exists_eq_right'.mpr <| SModEq.sub_mem.mp ih
      have eq_aux : G ^ (q ^ k * q ^ l) =
        ((MvPowerSeries.map (σ ^ l)) (ofSubring R (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l] G ^ q ^ k))).toSubring
        R (coeff_aux_mem σ hs l) + a := by rw [←ha]; ring
      have mod_eq_aux :
        (G ^ (q ^ k * q ^ l)) ^ q ≡
        ((MvPowerSeries.map (σ ^ l)) (ofSubring R (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l]
        G ^ q ^ (k + 1)))).toSubring R (coeff_aux_mem σ hs l) [SMOD (I ^(k + 1 + 1)).MvPowerSeries]
        := by
        apply SModEq.sub_mem.mpr
        obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp_prime (((MvPowerSeries.map (σ ^ l))
          (ofSubring R (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l] G ^ q ^ k))).toSubring R
          (coeff_aux_mem σ hs l)) a t
        nth_rw 3 [hq]
        rw [eq_aux, hr]
        have eq_aux' : ((MvPowerSeries.map (σ ^ l)) (ofSubring R (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l]
          G ^ q ^ k))).toSubring R (σ := Fin 2) (coeff_aux_mem σ hs l) ^ p ^ t =
          ((MvPowerSeries.map (σ ^ l)) (ofSubring R (subst ![X₀ ^ q ^ l, X₁ ^ q ^ l]
          G ^ q ^ (k + 1)))).toSubring R (coeff_aux_mem σ hs l) := by
          rw [←hq]
          ext n
          rw [coeff_pow]
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, AddSubmonoidClass.coe_finset_sum,
            SubmonoidClass.coe_finset_prod, coeff_toSubring, coeff_map, coeff_ofSubring]
          simp [pow_add, pow_mul, coeff_pow]
        rw [eq_aux']
        ring_nf
        refine Submodule.add_mem Ideal.MvPowerSeries ?_ ?_
        · rw [mul_assoc _ _ r, ←pow_add]
          have mem_aux : a * ↑p ∈ (I ^ (2 + k)).MvPowerSeries := by
            rw [show I ^ (2 + k) = I ^ (k + 1) * I by ring]
            apply MvPowerSeries.mul_mem_mul a_mem
            unfold Ideal.MvPowerSeries
            simp
            have aux : (p : MvPowerSeries (Fin 2) R) = C (p : R) := rfl
            intro n
            rw [aux, show C (p : R) n = coeff n (C (p : R)) by rfl, coeff_C]
            if hn : n = 0 then simp [if_pos hn, hp]
            else simp [if_neg hn]
          exact Ideal.IsTwoSided.mul_mem_of_left _ mem_aux
        · have aux : p ^ t = 1 + 1 + (p ^ t - 2) := by
            have ge_aux : p ^ t ≥ 2 :=
              le_trans (Nat.Prime.two_le hp_prime) <| Nat.le_self_pow hn p
            omega
          rw [aux, pow_add, pow_add, show I ^ 2 * I ^ k = I ^ (k + 1) * I by ring]
          simp
          have mem_aux : a * a ∈ (I ^ (k + 1) * I).MvPowerSeries := by
            apply MvPowerSeries.mul_mem_mul a_mem
            unfold Ideal.MvPowerSeries
            simp
            intro n
            obtain h1 := a_mem n
            have subset_aux : I ^ (k + 1) ≤ I :=
              Ideal.pow_le_self <| Ne.symm (Nat.zero_ne_add_one k)
            exact subset_aux (a_mem n)
          exact Ideal.IsTwoSided.mul_mem_of_left _ mem_aux
      refine SModEq.trans ?_ mod_eq_aux
      rw [←pow_mul]
      congr! 1
      ring
  calc
    _ ≡ (G ^ (q ^ r * q ^ l)) ^ m [SMOD (I^(r + 1)).MvPowerSeries] := by
      rw [←pow_mul]; congr! 1; ring
    _ ≡ _ [SMOD (I^(r + 1)).MvPowerSeries] := by
      refine .trans (SModEq.pow _ mod_aux) ?_
      congr
      ext n
      rw [coeff_pow]
      simp only [AddSubmonoidClass.coe_finset_sum,
        SubmonoidClass.coe_finset_prod, coeff_toSubring, coeff_map, coeff_ofSubring]
      simp [pow_mul, coeff_pow]


def inv_RecurFun :=
  PowerSeries.subst_inv _ (coeff_RecurFun_unit hp_prime hn hq σ s hg hg_unit)
  (constantCoeff_RecurFun_zero ..)


lemma coeff_inv_RecurFun_one :
    (inv_RecurFun hp_prime hn hq σ s hg hg_unit).coeff 1 = hg_unit.unit⁻¹ := by
  rw [inv_RecurFun, PowerSeries.subst_inv]
  simp [PowerSeries.invFun_aux, coeff_RecurFun_one]
  refine Units.inv_eq_of_mul_eq_one_left ?_
  simp
  exact_mod_cast IsUnit.val_inv_mul hg_unit

-- lemma coeff_inv_RecurFun_zero (hg_unit : IsUnit ((PowerSeries.coeff 1) g)) :
--     PowerSeries.constantCoeff (inv_RecurFun hp_prime hn hq σ s g hg hg_unit) := by

--   sorry

lemma coeff_inv_RecurFun_zero :
    (inv_RecurFun hp_prime hn hq σ s hg hg_unit).constantCoeff = 0 := by
  simp [inv_RecurFun, PowerSeries.subst_inv, PowerSeries.invFun_aux]


/-- `inv_add_aux` define to be `f_g⁻¹(f_g(X) + f_g(Y))`, and we will prove this to be
  a formal group law over coefficient ring `R`. -/
def inv_add_aux  :=
    PowerSeries.subst ((PowerSeries.subst (X₀ (R := K)) (RecurFun hp_prime hn hq σ s hg)) +
    (PowerSeries.subst X₁ (RecurFun hp_prime hn hq σ s hg)))
    (inv_RecurFun hp_prime hn hq σ s hg hg_unit)


/- Now we denote `F(X,Y) = f_g⁻¹(f_g(X) + f_g(Y))` and `f (X) = f_g (X)` for convention. -/

lemma constantCoeff_aux : constantCoeff ((RecurFun hp_prime hn hq σ s hg).subst (X₀ (R := K)) +
    (RecurFun hp_prime hn hq σ s hg).subst X₁) = 0 := by
  rw [@RingHom.map_add, PowerSeries.constantCoeff_subst_X
    <| constantCoeff_RecurFun_zero hp_prime ..,
    PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun_zero hp_prime .., add_zero]


lemma coeff_inv_add_aux_X :
    (coeff (Finsupp.single 0 1)) (inv_add_aux hp_prime hn hq σ s hg hg_unit) = 1 := by
  rw [inv_add_aux, PowerSeries.coeff_subst <|
    PowerSeries.HasSubst.of_constantCoeff_zero <| constantCoeff_aux .., finsum_eq_single _ 1]
  simp
  rw [PowerSeries.coeff_subst <| PowerSeries.HasSubst.X _, finsum_eq_single _ 1,
    coeff_RecurFun_one]
  simp [coeff_inv_RecurFun_one]
  have eq_aux : ↑↑hg_unit.unit⁻¹ * (((PowerSeries.coeff 1) g : R) : K) = 1 := by
    exact_mod_cast IsUnit.val_inv_mul hg_unit
  simp [mul_add, eq_aux]
  have eq_aux : (coeff (Finsupp.single 0 1)) (PowerSeries.subst (X₁ (R := K))
    (RecurFun hp_prime hn hq σ s hg)) = 0 := by
    rw [PowerSeries.coeff_subst <| PowerSeries.HasSubst.X 1]
    apply finsum_eq_zero_of_forall_eq_zero <| fun d => by
      if hd : d = 0 then simp [hd, constantCoeff_RecurFun_zero]
      else
      rw [X, monomial_pow, coeff_monomial, if_neg _]
      simp
      exact Finsupp.ne_iff.mpr ⟨0, by simp⟩
  simp [eq_aux]
  intro x hx
  rw [X, monomial_pow, coeff_monomial, if_neg <| Finsupp.ne_iff.mpr ⟨0, by simp [Ne.symm hx]⟩,
    MulActionWithZero.smul_zero]
  intro x hx
  if hx' : x = 0 then simp [hx', coeff_inv_RecurFun_zero]
  else
  have eq_aux : (((RecurFun hp_prime hn hq σ s hg).subst (X₀ (R := K)) +
    (RecurFun hp_prime hn hq σ s hg).subst X₁) ^ x).coeff (Finsupp.single 0 1) = 0 := by
    rw [coeff_pow]
    apply Finset.sum_eq_zero <| fun d hd => by
      simp at hd
      have exist_aux : ∃ i ∈ range x, d i = 0 := by
        have xge : x ≥ 2 := by omega
        by_contra hc
        simp at hc
        have aux : ∀ x_1 < x, (d x_1).degree ≥ 1 := by
          intro t ht
          obtain ht' := hc t ht
          by_contra hc'
          simp at hc'
          exact ht' <| (Finsupp.degree_eq_zero_iff _).mp hc'
        have eq_aux : ((range x).sum ⇑d).degree = (Finsupp.single (0 : Fin 2) 1).degree := by
          rw [hd.1]
        simp at eq_aux
        have contra : ((range x).sum ⇑d).degree ≥ 2 := calc
          _ ≥ (range x).sum 1 := by
            rw [sum_range, sum_range,  @Fin.sum_univ_eq_sum_range, @Fin.sum_univ_eq_sum_range,
              map_sum]
            exact sum_le_sum <| by simpa
          _ ≥ 2 := by
            simp [xge]
        simp at contra
        linarith
      obtain ⟨i, hi, hi'⟩ := exist_aux
      apply Finset.prod_eq_zero hi
      simp [hi']
      rw [PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun_zero ..,
        PowerSeries.constantCoeff_subst_X <| constantCoeff_RecurFun_zero .., add_zero]
  simp [eq_aux]

/- the proof of this should be similar as above `coeff_inv_add_aux_X`-/
lemma coeff_inv_add_aux_Y :
    (coeff (Finsupp.single 1 1)) (inv_add_aux hp_prime hn hq σ s hg hg_unit) = 1 := by

  sorry

open PowerSeries HasSubst in
/-- `f(F(X,Y)) = f (X) + f(Y)`-/
lemma comp_aux :
    (RecurFun hp_prime hn hq σ s hg).subst (inv_add_aux hp_prime hn hq σ s hg hg_unit) =
    (RecurFun hp_prime hn hq σ s hg).subst X₀ + (RecurFun hp_prime hn hq σ s hg).subst X₁ := by
  rw [inv_add_aux, ←subst_comp_subst_apply (of_constantCoeff_zero' rfl)
    <| of_constantCoeff_zero <| constantCoeff_aux hp_prime .., inv_RecurFun,
    subst_inv_eq, subst_X <| of_constantCoeff_zero <| constantCoeff_aux hp_prime ..]

/- constant coefficient of `F` is zero. -/
lemma constantCoeff_inv_add_aux :
    constantCoeff (inv_add_aux hp_prime hn hq σ s hg hg_unit) = 0 := by
  rw [inv_add_aux, PowerSeries.constantCoeff_subst <|
    PowerSeries.HasSubst.of_constantCoeff_zero <| constantCoeff_aux ..]
  apply finsum_eq_zero_of_forall_eq_zero <| fun d => by
    if hd : d = 0 then
    simp [hd]
    simp [inv_RecurFun, PowerSeries.subst_inv]; rfl
    else
    simp [constantCoeff_aux, zero_pow hd]


lemma HasSubst.inv_add_aux :
    PowerSeries.HasSubst (inv_add_aux hp_prime hn hq σ s hg hg_unit) :=
  PowerSeries.HasSubst.of_constantCoeff_zero <| constantCoeff_inv_add_aux ..


open AddMonoidHom PowerSeries in
/- for any natural number `i`, we have `σⁱ_* f( σⁱ_* F(X, Y)) = σⁱ_* f(X) + σⁱ_* f(Y)`. -/
lemma sigma_map_distrib (i : ℕ) :
    let f := (RecurFun hp_prime hn hq σ s hg)
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    (f.map (σ ^ i)).subst (F.map (σ ^ i)) =
    ((f.subst X₀).map (σ ^ i)) + ((f.subst X₁).map (σ ^ i)) := calc
  _ = ((RecurFun hp_prime hn hq σ s hg).subst (inv_add_aux hp_prime hn hq σ s hg hg_unit)).map
    (σ ^ i) := by
    ext n
    have aux {x : K}: (σ ^ i) x = (σ ^ i).toAddMonoidHom x := rfl
    rw [MvPowerSeries.coeff_map, coeff_subst <| HasSubst.of_constantCoeff_zero
      (by simp [constantCoeff_inv_add_aux]), coeff_subst <| HasSubst.inv_add_aux ..,
      aux, map_finsum _ <| coeff_subst_finite (HasSubst.inv_add_aux ..) _ _]
    apply finsum_congr <| fun d => by
      simp [smul_eq_mul, smul_eq_mul, PowerSeries.coeff_map, RingHom.map_mul,
        MvPowerSeries.coeff_pow]
  _ = _ := by
    rw [comp_aux, map_add]

lemma constantCoeff_frobnius_F_zero (i : ℕ):
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    constantCoeff (subst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i] F) = 0 := by
  have qneq : q ≠ 0 := hq ▸ pow_ne_zero t <| Nat.Prime.ne_zero hp_prime
  have neq : q ^ i ≠ 0 :=  pow_ne_zero i qneq
  simp
  rw [constantCoeff_subst_zero] <;> simp [zero_pow <| neq, constantCoeff_inv_add_aux]

include hp_prime hq in
lemma has_subst_X_pow (i : ℕ): HasSubst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i] := by
  have qneq : q ≠ 0 := hq ▸ pow_ne_zero t <| Nat.Prime.ne_zero hp_prime
  refine HasSubst.FinPairing ?_ ?_
  · rw [X₀, X, monomial_pow, ←coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
    refine Finsupp.ne_iff.mpr ⟨0, by simp [Ne.symm <| pow_ne_zero i qneq]⟩
  · rw [X₁, X, monomial_pow, ←coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
    refine Finsupp.ne_iff.mpr ⟨1, by simp [Ne.symm <| pow_ne_zero i qneq]⟩

/-- $σ^i f (F(X^{q^i}, Y^{q^i})) = ∑'(n ∈ ℕ), σ^i (a_n) * F(X^{q^i}, Y^{q^i})^n. $-/
lemma decomp_f (i : ℕ) [UniformSpace K] [T2Space K] [DiscreteUniformity K]:
    let f := (RecurFun hp_prime hn hq σ s hg)
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    ∑' (n : ℕ), ((f.map (σ ^ i)).coeff n) •
    ((subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F).map (σ ^ i)) ^ n =
    (f.map (σ ^ i)).subst ((F.map (σ ^ i)).subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] ) := by
  /- this lemma need to use tsum_subst. -/
  let f := (RecurFun hp_prime hn hq σ s hg)
  let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
  have f_def : f = (RecurFun hp_prime hn hq σ s hg) := rfl
  have F_def : F = (inv_add_aux hp_prime hn hq σ s hg hg_unit) := rfl
  simp_rw [←f_def, ←F_def]
  obtain h1 := PowerSeries.as_tsum (f.map (σ^i))
  obtain has_subst := has_subst_X_pow hp_prime hq (K:=K)
  have has_subst_aux : PowerSeries.HasSubst (subst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i]
    ((MvPowerSeries.map (σ ^ i)) F)) := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero <| ?_
    rw [←subst_map <| has_subst i, constantCoeff_map, constantCoeff_frobnius_F_zero, map_zero]
  nth_rw 2 [h1]
  rw [tsum_subst _ has_subst_aux]
  apply tsum_congr
  intro n
  ext d
  simp only [PowerSeries.coeff_map, Nat.succ_eq_add_one, Nat.reduceAdd, map_smul,
    smul_eq_mul]
  rw [←map_pow, coeff_map, PowerSeries.monomial_eq_C_mul_X_pow, ←PowerSeries.smul_eq_C_mul,
    PowerSeries.subst_smul has_subst_aux, PowerSeries.subst_pow has_subst_aux,
    PowerSeries.subst_X has_subst_aux]
  simp only [map_smul, smul_eq_mul]
  congr! 1
  rw [←subst_pow <|has_subst i, ←subst_pow <|has_subst i, ←map_pow, ←subst_map <|has_subst i, coeff_map]
  · obtain HasSum_aux := PowerSeries.hasSum_of_monomials_self (f.map (σ ^i))
    unfold Summable
    use ((PowerSeries.map (σ ^ i)) f)


open AddMonoidHom in
/-- this auxiliary lemma shows that $∑ s_i ∑ σ^i_*(a_n)(σ^i_*F(X^{q^i}, Y^{q^i}))^n =
  f(X) + f(Y) - g(X) - g(Y)$. ref: 2.4.12 in Page 14. -/
lemma tsum_eq_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0):
    let f := (RecurFun hp_prime hn hq σ s hg)
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    ∑' i : ℕ, (s i) • ∑' n : ℕ, ((σ ^ i) (f.coeff n)) •
    ((F.subst ![X₀^(q ^ i), X₁^(q^i)]).map (σ^i)) ^ n
    = f.subst X₀ + f.subst X₁ - g.subst X₀ - g.subst X₁ := by
  let f := (RecurFun hp_prime hn hq σ s hg)
  let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
  have f_def : f = (RecurFun hp_prime hn hq σ s hg) := rfl
  have F_def : F = (inv_add_aux hp_prime hn hq σ s hg hg_unit) := rfl
  have aux {x : K} {i : ℕ}: (σ ^ i) x = (σ ^ i).toAddMonoidHom x := rfl
  obtain has_subst := has_subst_X_pow hp_prime hq (K:=K)
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
        rw [←sigma_map_distrib hp_prime hn hq σ s hg hg_unit i, ←F_def, ←f_def]
        have eq_aux : subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] (PowerSeries.subst
          ((MvPowerSeries.map (σ ^ i)) F) ((PowerSeries.map (σ ^ i)) f)) =
          ((PowerSeries.map (σ ^ i)) f).subst ((MvPowerSeries.map (σ ^ i))
          (subst ![(X₀ (R := K)) ^ q ^ i, X₁ ^ q ^ i] F)):= by
          rw [PowerSeries.subst, PowerSeries.subst, subst_comp_subst_apply _ <|has_subst i]
          apply subst_congr
          funext s
          rw [subst_map <|has_subst i]
          refine PowerSeries.HasSubst.const <| PowerSeries.HasSubst.of_constantCoeff_zero ?_
          rw [constantCoeff_map, constantCoeff_inv_add_aux, map_zero]
        ext n
        rw [eq_aux, PowerSeries.coeff_subst, PowerSeries.coeff_subst]
        apply finsum_congr <| fun d => (subst_map <|has_subst i) ▸ rfl
        refine PowerSeries.HasSubst.of_constantCoeff_zero <| by rw [constantCoeff_map,
          constantCoeff_frobnius_F_zero, map_zero]
        refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
        rw [←subst_map <|has_subst i, constantCoeff_map, constantCoeff_frobnius_F_zero, map_zero]
    _ = ∑' i : ℕ, ((s i) • (((f.subst (X₀ ^ (q ^ i))).map (σ ^ i)) +
      ((f.subst (X₁ ^ (q ^ i))).map (σ ^ i)))) :=
      tsum_congr <| fun i => by
        rw [subst_add <|has_subst i, ←subst_map <|has_subst i, ←subst_map <|has_subst i]
        congr! 3
        · rw [PowerSeries.subst, subst_comp_subst_apply
          (PowerSeries.HasSubst.const <| PowerSeries.HasSubst.X _) <|has_subst i]
          apply subst_congr
          funext s
          simp [subst_X <|has_subst i]
        · rw [PowerSeries.subst, subst_comp_subst_apply
          (PowerSeries.HasSubst.const <| PowerSeries.HasSubst.X _) <|has_subst i]
          apply subst_congr
          funext s
          simp [subst_X <|has_subst i]
    _ = _ := by
      simp_rw [←f_def, smul_add]
      rw [Fun_eq_of_RecurFun_XY hp_prime hn hq σ s hg hs0,
        Fun_eq_of_RecurFun_XY hp_prime hn hq σ s hg hs0,
        Summable.tsum_add (summable_X₀ hp_prime hn hq σ s hg hs0)
        (summable_X₁ hp_prime hn hq σ s hg hs0)]
      ring

lemma nat_inequality {i q: ℕ} (lt_q : 1 < q) : i ≤ q ^ i :=
  (Nat.lt_pow_self lt_q).le


lemma tsum_to_finite₁ {n : Fin 2 →₀ ℕ} (hn₀ : n ≠ 0) [UniformSpace K] [T2Space K]
    [DiscreteUniformity K] :
    let f := (RecurFun hp_prime hn hq σ s hg)
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
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
          rw [←subst_pow <| has_subst_X_pow hp_prime hq b,
            coeff_subst <| has_subst_X_pow hp_prime hq b]
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
                nlinarith [Nat.le_self_pow hn p, Nat.Prime.two_le hp_prime]
              exact nat_inequality qge_aux
            linarith
          rw [if_neg aux, mul_zero]
        simp [aux']
      simp_rw [aux]
      exact tsum_zero
    rw [eqZero_aux, mul_zero]
  /- if not summable then equal to zero, but in fact it is summable-/
  else
  rw [tsum_eq_zero_of_not_summable hsum, coeff_zero, mul_zero]

lemma tsum_to_finite₂ {n : Fin 2 →₀ ℕ} (hn₀ : n ≠ 0) [UniformSpace K] [T2Space K]
    [DiscreteUniformity K] :
    let f := (RecurFun hp_prime hn hq σ s hg)
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
     ∑' (i : ℕ), (coeff n) (PowerSeries.subst F (PowerSeries.C (s i)
    * (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) f))) =
    ∑ i ∈ range (n.degree + 1), (coeff n) (PowerSeries.subst F (PowerSeries.C (s i) *
    (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) f))) := by
  refine tsum_eq_sum ?_

  sorry

lemma mem_ideal_aux {m : ℕ} {α : ℕ → K} (h : ∀ i, α i ∈ ⇑(algebraMap (↥R) K) '' ↑I) :
    ∑ i ∈ range m, α i ∈ ⇑(algebraMap (↥R) K) '' ↑I := by
  induction m with
  | zero => simp
  | succ k ih =>
    -- have aux : ∀ i ∈ range k, α i ∈ ⇑(algebraMap (↥R) K) '' ↑I := fun i hi => by
    --   refine h i <| mem_range.mpr <| by nlinarith [mem_range.mp hi]
    rw [range_add_one, sum_insert (by simp)]
    -- obtain ih' := ih aux
    obtain hk := h k
    simp at ih hk ⊢
    obtain ⟨a, ha₀, ha₁, ha₂⟩ := ih
    obtain ⟨b, hb₀, hb₁, hb₂⟩ := hk
    have eq_aux : (⟨a + b, Subring.add_mem R ha₀ hb₀⟩ : R) = ⟨a, ha₀⟩ + ⟨b, hb₀⟩ := rfl
    use (a + b), Subring.add_mem R ha₀ hb₀, ((Submodule.add_mem_iff_right I ha₁).mpr hb₁)
    rw [←hb₂, ←ha₂, eq_aux, map_add]
    ring_nf

include hs_i hs_i' in
/- using the second technical lemma we can get the following result. -/
lemma forall_coeff_mem_aux (n : Fin 2 →₀ ℕ) (i : ℕ) :
    let f := (RecurFun hp_prime hn hq σ s hg)
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    ∀ x : ℕ, (coeff n) ((σ ^ i) (f.coeff x) •
    ((MvPowerSeries.map (σ ^ i)) (subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F) ^ x -
    (MvPowerSeries.map (σ ^ i)) (F ^ (x * q ^ i)))) ∈ ⇑(algebraMap (↥R) K) '' ↑I := by
  intro f F x
  rw [← map_pow, ←map_sub, map_smul, coeff_map, smul_eq_mul]
  -- coeff_RecurFun_mul_mem'
  have mem_aux : (coeff n) (subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F ^ x - F ^ (x * q ^ i)) ∈
    (algebraMap R K) '' ↑(I^((multiplicity q x) + 1)) := sorry
  -- obtain h' := sigma_mem_aux σ hs_i' i _  mem_aux
  -- sigma_mem_aux

  sorry

include hs_i hs_i' in
/-- f(F(X,Y)) ≡ g(F(X,Y)) + f(X) + f(Y) - g(X) - g(Y) [MOD R]-/
lemma RModEq_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0):
    let f := (RecurFun hp_prime hn hq σ s hg)
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    ∀ n, (g.subst F + f.subst X₀ + f.subst X₁ - g.subst X₀ - g.subst X₁
      - f.subst F).coeff n ∈ R  := by
  /- this need to use the equation we prove above. -/
  intro f F n
  have f_def : f = (RecurFun hp_prime hn hq σ s hg) := rfl
  have F_def : F = (inv_add_aux hp_prime hn hq σ s hg hg_unit) := rfl
  have has_subst_F : PowerSeries.HasSubst F := HasSubst.inv_add_aux hp_prime hn hq σ s hg hg_unit
  have has_subst_monomial {i : ℕ} := PowerSeries.HasSubst.monomial'
    (q_pow_neZero hp_prime hq (x := i)) (1 : K)
  if hn₀ : n = 0 then
    /- all these terms are equal to zero. -/
    simp [hn₀]
    have coeff_zero₁: constantCoeff (g.subst F) = 0 :=
      PowerSeries.constantCoeff_subst_zero (constantCoeff_inv_add_aux ..) hg
    have coeff_zero_XY {x : Fin 2} : constantCoeff (PowerSeries.subst (X x (R := K)) f) = 0 :=
      PowerSeries.constantCoeff_subst_zero (constantCoeff_X x)
      <| constantCoeff_RecurFun_zero ..
    have coeff_zero_XY' {x : Fin 2} :(g.subst (X x (R := K))).constantCoeff = 0 :=
      PowerSeries.constantCoeff_subst_zero (constantCoeff_X x) hg
    have coeff_zero₆ : (f.subst F).constantCoeff = 0 :=
      PowerSeries.constantCoeff_subst_zero (constantCoeff_inv_add_aux ..)
        <| constantCoeff_RecurFun_zero ..
    simp [coeff_zero₁, coeff_zero_XY, coeff_zero_XY', coeff_zero₆]
  else
  have eq_aux {a₀ a₁ a₂ b₀ b₁ b₂ : MvPowerSeries (Fin 2) K}: a₀ + a₁ + a₂ - b₀ - b₁ - b₂ =
    a₀ + (a₁ + a₂ - b₀ - b₁) - b₂ := by ring
  rw [eq_aux, ←tsum_eq_aux hp_prime hn hq σ s hg hg_unit hs0, f_def]
  nth_rw 2 [Fun_eq_of_RecurFun hp_prime hn hq σ s hg hs0]
  rw [PowerSeries.subst_add has_subst_F]
  have eq_aux₁ : ((PowerSeries.map (algebraMap (↥R) K)) g).subst F =
    g.subst F := by
    rw [@PowerSeries.map_algebraMap_eq_subst_X, PowerSeries.subst_comp_subst_apply
       PowerSeries.HasSubst.X' has_subst_F ]
    congr! 1
    rw [PowerSeries.subst_X has_subst_F]
  have eq_aux₂ {i_1 i : ℕ}: ((PowerSeries.monomial i_1) ((PowerSeries.coeff i_1) f)).subst
    ((PowerSeries.monomial (q ^ i) (R := K)) 1) =
    PowerSeries.monomial (i_1 * q ^ i) (R := K) ((PowerSeries.coeff i_1) f):= by
    nth_rw 2 [PowerSeries.monomial_eq_C_mul_X_pow]
    rw [←PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul has_subst_monomial,
      PowerSeries.subst_pow has_subst_monomial, PowerSeries.subst_X has_subst_monomial,
      PowerSeries.monomial_pow, PowerSeries.monomial_eq_C_mul_X_pow,
      PowerSeries.monomial_eq_C_mul_X_pow, PowerSeries.smul_eq_C_mul]
    simp
  rw [eq_aux₁]
  ring_nf
  rw [tsum_subst _ has_subst_F, map_sub, ←F_def, ←f_def,
    Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n),
    Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n)]
  /- here need to use the second technical lemma! It is the equation 2.4.11 in Hazewinkel. -/
  rw [tsum_to_finite₁ hp_prime hn hq σ s hg hg_unit hn₀, tsum_to_finite₂ hp_prime hn hq σ s
    hg hg_unit hn₀, ←sum_sub_distrib, ←F_def, ←f_def]
  refine Subring.sum_mem R <| fun i hi => by
    simp_rw [←PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul has_subst_F, coeff_smul, ←mul_sub]
    refine hs_i i _ ?_
    rw [Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n)]
    have tsum_to_finite₃ : ∑' (j : ℕ), (coeff n) ((σ ^ i) ((PowerSeries.coeff j) f) •
      (MvPowerSeries.map (σ ^ i)) (subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F) ^ j) =
      ∑ j ∈ range (n.degree + 1), (coeff n) ((σ ^ i) ((PowerSeries.coeff j) f) •
      (MvPowerSeries.map (σ ^ i)) (subst ![X₀ ^ q ^ i, X₁ ^ q ^ i] F) ^ j) := sorry
    nth_rw 2 [f.as_tsum]
    rw [tsum_subst ⟨f, PowerSeries.hasSum_of_monomials_self f⟩ (PowerSeries.HasSubst.monomial' (q_pow_neZero hp_prime hq) 1),
      ←PowerSeries.subst_map has_subst_F, tsum_subst _ has_subst_F, coeff_map,
      Summable.map_tsum _ _ (WithPiTopology.continuous_coeff K n)]
    have eq_aux₃ {i_1 : ℕ}: ((PowerSeries.monomial (i_1 * q ^ i))
      (f.coeff i_1)).subst F = f.coeff i_1 • F ^ (i_1 * q ^ i) := by
      rw [PowerSeries.monomial_eq_C_mul_X_pow, ←PowerSeries.smul_eq_C_mul,
        PowerSeries.subst_smul has_subst_F, PowerSeries.subst_pow has_subst_F,
        PowerSeries.subst_X has_subst_F]
    have eq_aux₄ {x : ℕ}: (MvPowerSeries.map (σ ^ i)) ((PowerSeries.coeff x) f •
      F ^ (x * q ^ i)) = (σ^i) ((PowerSeries.coeff x) f) • (F ^ (x * q ^ i)).map (σ^i) := by
      rw [smul_eq_C_mul, map_mul, map_C, ←smul_eq_C_mul]
    simp_rw [eq_aux₂, eq_aux₃]
    have tsum_to_finite₄ : ∑' (i_1 : ℕ), (coeff n) ((PowerSeries.coeff i_1) f • F ^ (i_1 * q ^ i))
      = ∑ j ∈ range (n.degree + 1), (coeff n) ((PowerSeries.coeff j) f • F ^ (j * q ^ i)) := sorry
    rw [tsum_to_finite₃, tsum_to_finite₄, map_sum, ←sum_sub_distrib]
    simp_rw [←coeff_map, ←map_sub, eq_aux₄, ←smul_sub]
    exact mem_ideal_aux (forall_coeff_mem_aux hp_prime hn hq σ s hs_i hs_i' hg hg_unit n i)
    simp_rw [eq_aux₂]
    apply MvPowerSeries.Summable.increase_order <| fun n => nat_le_order <| fun d hd => by
      rw [PowerSeries.coeff_subst has_subst_F, finsum_eq_zero_of_forall_eq_zero]
      intro m
      rw [PowerSeries.coeff_monomial]
      by_cases hm : m = n * q ^ i
      · rw [if_pos hm]
        have aux : (coeff d) (F ^ m) = 0 := by
          rw [coeff_pow, sum_eq_zero]
          intro l hl
          have h_aux : ∃ i ∈ range m, l i = 0 := by
            by_contra hc
            simp only [not_exists, not_and, mem_finsuppAntidiag] at hc hl
            have h_aux' : ∀ i ∈ range m, 1 ≤ (l i).degree := by
              intro i hi
              by_contra hc'
              simp only [not_le, Nat.lt_one_iff] at hc'
              exact hc i hi <| (Finsupp.degree_eq_zero_iff _).mp hc'
            have eq_aux : ∑ i ∈ range m, (l i).degree = d.degree := by
              simp [←hl.1]
            have ineq_aux : d.degree ≥ m := by
              simp [←hl.1]
              calc
                _ = ∑ i ∈ range m, 1 := Eq.symm
                  (sum_range_induction (fun k ↦ 1) (fun m ↦ m) rfl m fun k ↦ congrFun rfl)
                _ ≤ _ := sum_le_sum h_aux'
            have ineq_aux' : m ≥ n := hm ▸ Nat.le_mul_of_pos_right n
              <| Nat.zero_lt_of_ne_zero <| q_pow_neZero hp_prime hq (x := i)
            linarith
          obtain ⟨i, hi₁, hi₂⟩ := h_aux
          rw [prod_eq_zero hi₁]
          simpa [hi₂] using (constantCoeff_inv_add_aux hp_prime hn hq σ s hg hg_unit)
        rw [aux, smul_zero]
      · rw [if_neg hm, zero_smul]



    -- use f.subst F^(q^i)
    -- have eq_aux :∑' (i_1 : ℕ), PowerSeries.subst F ((PowerSeries.monomial (i_1 * q ^ i))
    --   ((PowerSeries.coeff i_1) f)) = f.subst F^(q^i) := sorry


    /- some summable result-/
    sorry
    sorry


  /- summable result-/
  sorry
  sorry
  sorry





lemma coeff_subst_X_mem_aux {n : Fin 2 →₀ ℕ} {x : Fin 2} :
    (g.subst (X x (R := K))).coeff n ∈ R := by
  have aux {a : R} : R.subtype a = R.subtype.toAddMonoidHom a := rfl
  have eq_aux : g.subst (X x (R := K)) = (g.subst (X x)).map R.subtype := by
    ext d
    rw [PowerSeries.coeff_subst <| PowerSeries.HasSubst.X x, coeff_map, PowerSeries.coeff_subst <| PowerSeries.HasSubst.X x, aux,
      AddMonoidHom.map_finsum _ <| PowerSeries.coeff_subst_finite (PowerSeries.HasSubst.X x) g d]
    apply finsum_congr
    intro m
    congr
    rw [coeff_X_pow, coeff_X_pow]
    split_ifs <;> simp
  rw [eq_aux]
  simp only [coeff_map, Subring.subtype_apply, SetLike.coe_mem]


include hs_i hs_i' in
/-- by above lemma we can deduce that all coefficient in g(F(X,Y)) is in `R`, since
  f(F(X,Y)) = f(X) + f(Y).-/
lemma RModEq_aux₂ [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) :
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    ∀ n, (g.subst F).coeff n ∈ R := by
  intro F n
  have F_def : F = (inv_add_aux hp_prime hn hq σ s hg hg_unit) := rfl
  obtain h₀ := RModEq_aux hp_prime hn hq σ s hs_i hs_i' hg hg_unit hs0 n
  rw [comp_aux, ←F_def] at h₀
  ring_nf at h₀
  simp at h₀
  have mem_aux : (-(coeff n) (PowerSeries.subst X₀ g) - (coeff n) (PowerSeries.subst X₁ g)) ∈ R
    :=
    Subring.sub_mem R (Subring.neg_mem R <| coeff_subst_X_mem_aux) <| coeff_subst_X_mem_aux
  exact (add_mem_cancel_right mem_aux).mp h₀


lemma coeffEq_aux [UniformSpace K] [T2Space K] [DiscreteUniformity K]
     {n : Fin 2 →₀ ℕ} {k : ℕ} (h : n.degree = k) :
    let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
    (h_ind : ∀ m < k, ∀ (n : Fin 2 →₀ ℕ), n.degree = m → F n ∈ R) →
    (g.coeff 1) * F.coeff n - (g.subst F).coeff n ∈ R := by
  intro  F h_ind
  have F_def : F = (inv_add_aux hp_prime hn hq σ s hg hg_unit) := rfl
  rw [PowerSeries.coeff_subst <| HasSubst.inv_add_aux ..]
  obtain h₁ := PowerSeries.coeff_subst_finite (HasSubst.inv_add_aux
    hp_prime hn hq σ s hg hg_unit) g n
  rw [finsum_eq_sum _ h₁]
  have eq_aux : ↑((PowerSeries.coeff 1) g) * (coeff n) F =
    ∑ i ∈ h₁.toFinset, if i = 1 then ↑((PowerSeries.coeff 1) g) * (coeff n) F else 0 := by
    if hd : (coeff n) F = 0 then simp [hd]
    else
      refine Eq.symm <| sum_eq_single 1 (fun b _ hb' => if_neg hb') ?_
      simp
      tauto
  rw [eq_aux, ←sum_sub_distrib]
  apply Subring.sum_mem R
  intro i hi
  if hi₀ : i = 0 then
    simp [hi₀, hg]
  else
  if hi' : i = 1 then
    simp [hi', Subring.smul_def, F]
  else
    simp [if_neg hi', Subring.smul_def]
    refine Subring.mul_mem R (SetLike.coe_mem _) ?_
    rw [coeff_pow]
    refine Subring.sum_mem R <| fun l hl => by
      if h_neZero : ∃ j ∈ range i, l j = 0 then
        obtain ⟨j, hj, hj'⟩ := h_neZero
        have eq_zero : ∏ i ∈ range i, (coeff (l i)) F = 0 := by
          refine prod_eq_zero hj ?_
          simpa [hj'] using constantCoeff_inv_add_aux ..
        rw [eq_zero]
        exact Subring.zero_mem R
      else
      simp at h_neZero
      have aux : ∀ t ∈ range i, (l t).degree ≥ 0 := fun t ht => by simp
      refine Subring.prod_mem R <| fun j hj => by
        simp at hl
        have le_aux : (l j).degree ≤ n.degree := by
          rw [←hl.1, map_sum]
          exact Finset.single_le_sum aux hj
        if hlj : (l j).degree < n.degree then
          rw [h] at hlj
          exact h_ind _ hlj _ rfl
        else
          have eq_aux : (l j).degree = n.degree := by linarith
          have neq_aux :∀ b ∈ range i, b ≠ j → l b = 0 := by
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
          have i_ge : i ≥ 2 := by omega
          have exist_b : ∃ b ∈ range i, b ≠ j := by
            if hj₀ : j = 0 then use 1; simpa [hj₀]
            else
            use 0; simp [Ne.symm hj₀]; linarith
          obtain ⟨b, hb, hb'⟩ := exist_b
          exfalso
          exact (h_neZero b (mem_range.mp hb)) (neq_aux b hb hb')

include hs_i hs_i' in
/-- `inv_add_aux` define to be `f_g⁻¹(f_g(X) + f_g(Y))`, the coeff of this multi variate
  power series are all in `R`.-/
lemma coeff_inv_add_mem_Subring [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0):
    ∀ n, (inv_add_aux hp_prime hn hq σ s hg hg_unit) n ∈ R := by
  let f := (RecurFun hp_prime hn hq σ s hg)
  let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
  have f_def : f = (RecurFun hp_prime hn hq σ s hg) := rfl
  have F_def : F = (inv_add_aux hp_prime hn hq σ s hg hg_unit) := rfl
  rw [←F_def]
  intro n
  generalize h : n.degree = d
  induction d using Nat.strongRecOn generalizing n with
  | ind k hk =>
    simp [← coeff_apply]
    obtain h₁ := coeffEq_aux hp_prime hn hq σ s hg hg_unit h hk
    obtain h₂ := RModEq_aux₂ hp_prime hn hq σ s hs_i hs_i' hg hg_unit hs0 n
    rw [←F_def] at h₁ h₂
    have mem_aux : ↑((PowerSeries.coeff 1) g) * (coeff n) F ∈ R := by
      simpa using (Subring.add_mem _ h₁ h₂)
    have eq_aux : F.coeff n = hg_unit.unit⁻¹ * ↑((PowerSeries.coeff 1) g) * (coeff n) F := by
      norm_cast; simp [IsUnit.val_inv_mul hg_unit]
    rw [eq_aux, mul_assoc]
    exact Subring.mul_mem R (SetLike.coe_mem _) mem_aux


def inv_add_K [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0): FormalGroup K :=
  let f := (RecurFun hp_prime hn hq σ s hg)
  let F := (inv_add_aux hp_prime hn hq σ s hg hg_unit)
  have f_def : f = (RecurFun hp_prime hn hq σ s hg) := rfl
  have F_def : F = (inv_add_aux hp_prime hn hq σ s hg hg_unit) := rfl
  { toFun := F
    zero_constantCoeff := constantCoeff_inv_add_aux ..
    lin_coeff_X := coeff_inv_add_aux_X ..
    lin_coeff_Y := coeff_inv_add_aux_Y ..
    assoc :=
      sorry
      }

-- def inv_add_R [UniformSpace K] [T2Space K] [DiscreteUniformity K]
--     (hs0 : s 0 = 0) : FormalGroup R :=
--   (inv_add_K hp_prime hn hq σ s g hg hg_unit ..).toSubring R
--   (coeff_inv_add_mem_Subring hp_prime hn hq σ s g hg hg_unit)

/- `inv_add` define to be `f_g⁻¹(f_g(X) + f_g(Y))`, this is a formal group law over `R`. -/
-- def inv_add : CommFormalGroup R where
--   toFun := toSubring (inv_add_aux hp_prime hn hq σ s g hg hg_unit) R
--     (coeff_inv_add_mem_Subring hp_prime hn hq σ s g hg hg_unit)
--   zero_constantCoeff := sorry
--   lin_coeff_X := sorry
--   lin_coeff_Y := sorry
--   assoc := sorry
--   comm := sorry


/-- functional equaltion lemma II: let `g'` be another power series with coefficient in `R`,
  then the coefficient of $f_g^{-1} (f_{g'} (X)) are all in `R`$. -/
lemma coeff_inv_RecurFun_g'_mem_Subring [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) {g' : PowerSeries R} (hg' : PowerSeries.constantCoeff g' = 0):
    let f_g_inv := inv_RecurFun hp_prime hn hq σ s hg hg_unit
    let f_g' := (RecurFun hp_prime hn hq σ s hg')
    ∀ n, (f_g_inv.subst f_g') n ∈ R := by
  let f := (RecurFun hp_prime hn hq σ s hg)
  sorry

/- functional equaltion lemma III: let `h` be another power series with coefficient in `R`,
  then there exist a power series `h₁` over `R` such that `f(h(X)) = f_{h₁}(X)`, this is
  equivalent to say that `f₁(X) - ∑s_i σ^i(f₁(X^{q^i}))` is a power series in `R`, where
  `f₁(X) := f(h(X))` and `f(X) := f_g(X)` -/
lemma coeff_inv_RecurFun_g'_mem_Subring' [UniformSpace K] [T2Space K] [DiscreteUniformity K]
    (hs0 : s 0 = 0) {h : PowerSeries R}:
    let f := (RecurFun hp_prime hn hq σ s hg)
    let f₁ := f.subst h.ofSubring
    ∀ n, (f₁ - ∑' i : ℕ, (PowerSeries.C (s i) * PowerSeries.subst (PowerSeries.monomial (q^i)
    (1 : K)) f₁)).coeff n ∈ R := by
  sorry

end FunctionalEquationIntegralityLemma

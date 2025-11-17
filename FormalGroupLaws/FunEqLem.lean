import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution
import FormalGroupLaws.Basic
import FormalGroupLaws.BasicLem
import FormalGroupLaws.SubstInv
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.ENNReal.Lemmas
import FormalGroupLaws.MvPowerSeries



noncomputable section

open MvPowerSeries Classical Finset
open scoped WithPiTopology


namespace FunctionalEquationIntegralityLemma

/- The basic ingredients in this section are `R ⊆ K, σ : K → K, I ⊆ R, p, q, s₁, s₂ ⋯`,
  where `R` is a subring of `K`, `σ` is a ring homomorphism of `K`, which stablize `A`,
  `I` is an ideal of `A`, `p` is a prime number and `q` is a power of `p`, `s_i` are
  elements of `K`. -/


variable {K : Type*} [CommRing K] {R : Subring K} {I : Ideal R} {τ : Type*}
  {p t q: ℕ} (hp_prime : Nat.Prime p) (hn : t ≠ 0) (hq : q = p ^ t)
  (σ : K →+* K)  (hs : ∀ (a : R), σ a ∈ R) {x : R}
  (hs_mod : ∀ (a : R), (⟨ σ a, hs a⟩) ≡  (a ^ q) [SMOD I])
  (hp : (p : R) ∈ I) (s : ℕ → K) (hs_i : ∀ i, ∀ a ∈ I, s i * a ∈ R)
  (hs_i' :∀ r : ℕ, ∀ b : K,
    (∀ a ∈ I ^ r, b * (algebraMap R K a) ∈ Set.image (algebraMap R K) I) →
    ∀ a ∈ I ^ r, (σ b) * (algebraMap R K a) ∈ Set.image (algebraMap R K) I)

  -- (hs_i1 : ∀ r : ℕ, ∀ b : K, (({b}) *  (I ^ r : Ideal R) : Set R)  ⊆ (I : Set R) →
  --    {(σ b)} * ((I ^ r : Ideal R) : Set R) ⊆ (I : Set R))

variable (g : PowerSeries R) (hg : PowerSeries.constantCoeff g = 0)


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
def RecurFunAux (hg : constantCoeff g = 0): ℕ → K
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

-- if you want to elimilate the attach here, use `sum_attach`.

-- This is f_g
def RecurFun : PowerSeries K :=
  PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg)


/- Functional equation lemma.
  Let the notation defined as above, let `g(X) = ∑_{i=1}^∞ b_i X^i`, `g_bar (X) = ∑_{i=1}^∞ (b_bar i) X^i`.
  be two power series in one variable over `A`, and suppose that `b₁` is invertible in `A`. Then we have:
  (i) the power series F_g(X,Y)=f_g⁻¹(f_g(X)+f_g(Y)) has its coefficients in `A`.
  (ii) the power series `f_g⁻¹ (f_g_bar (X))` has its coefficient in `A`.
  (iii) if `h(X)=∑_{n=1}^∞ c_n X^n` is a power series with coefficients in `A`, then there is a
  power series `h^hat (X) = ∑_{n=1}^∞ c_n^hat X^n` with `c_n^hat ∈ A`, `n=1,2,…`, such that
  `f_g(h(X))=f_{h^hat}(X)`.
  (iv) if `α(X) ∈ A⟦X⟧, β(X) ∈ K⟦X⟧` are two power series, and `r ∈ ℕ, r ≥ 1`, then we have
  `α(X) ≡ β(X) [MOD I^r • A⟦X⟧] ↔ f_g(α(X)) ≡ f_g (β(X) [MOD I^r • A⟦X⟧])`.

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



include I  hs_i hs_i'  in
/-- Let a_n be the coefficient of f_g, then a_n * I^r ⊆ R, where r is the multiplicity of
  q in n. -/
lemma coeff_RecurFun_mul_mem (n : ℕ) :
  ∀ (x : R), x ∈ I ^ (multiplicity q n) →
    (PowerSeries.coeff n (RecurFun hp_prime hn hq σ s g hg)) * x ∈ R := by
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
        refine Subring.mul_mem R ?_ ?_
        simp
        simp
      · -- second component is in R
        have aux : (∑ i ∈ (Icc 1 (multiplicity q n)), s ↑i * (⇑σ)^[↑i]
          (RecurFunAux hp_prime hn hq σ s g hg (n / q ^ ↑i))) * x ∈ R := by
          rw [sum_mul]
          refine Subring.sum_mem R ?_
          intro i hi
          rw [mul_assoc]
          have mem_aux2 : ((σ ^ i) (RecurFunAux hp_prime hn hq σ s g hg (n / q ^ i)) * ↑x)
            ∈ Set.image (algebraMap R K) I := by
            have aux : ∀ b ∈ I ^ multiplicity q n, (RecurFunAux hp_prime hn hq σ s g hg (n / q ^ i)) * (algebraMap R K b)
              ∈ ⇑(algebraMap (↥R) K) '' ↑I := by
              intro b hb
              rw [h] at hb
              have lt_aux : multiplicity q (n / q ^ i) < k := by
                rw [←h]
                simp at hi
                obtain ⟨hi1, hi2⟩ := hi
                have hq' : q > 1 := by
                  rw [hq]
                  exact Nat.one_lt_pow hn <| Nat.Prime.one_lt hp_prime
                exact multiplicity_aux n i q hq' (by omega) hi2 hi1
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
          have mem_aux : ((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s g hg (n / q ^ i)) * ↑x)
            ∈ R := mem_image_aux₂ mem_aux2
          have mem_aux1 : ⟨((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s g hg (n / q ^ i)) * ↑x), mem_aux⟩ ∈ I := by
            have aux : ((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s g hg (n / q ^ i)) * ↑x)
              ∈ Set.image (algebraMap R K) I := by
              simp at mem_aux2
              simp [mem_aux2]
            exact mem_image_aux aux
          obtain h1 := hs_i i _ mem_aux1
          simp [h1]
        rw [←sum_attach] at aux
        exact aux




-- ask whether there is a way to define ∑' i start at 1. and the instance problem.
/- definition of recursion formula in the following sense.
  f_g (X) = g (X) + ∑ i = 0 to ∞, s (i + 1) * (σ ^ (i + 1)) f _g (X ^ (q ^ (i + 1)))
  -/

lemma coeff_infty_sum [TopologicalSpace K] [T2Space K]
  (f : ℕ → PowerSeries K) (hf : Summable f) (n : ℕ):
  PowerSeries.coeff n (∑' (i : ℕ), f i) = ∑' (i : ℕ), PowerSeries.coeff n (f i) :=
  Summable.map_tsum hf (PowerSeries.coeff n)
    <| PowerSeries.WithPiTopology.continuous_coeff K n

-- lemma coeff_infty_sum' [TopologicalSpace K] [T2Space K]
--   (f : ℕ → PowerSeries K) (n : ℕ):
--   PowerSeries.coeff K n (∑' (i : ℕ), f i) = ∑' (i : ℕ), PowerSeries.coeff K n (f i) := by
--   by_cases hf : Summable f
--   · exact Summable.map_tsum hf (PowerSeries.coeff K n)
--       (PowerSeries.WithPiTopology.continuous_coeff K n)
--   ·
--     have aux : (∑' (i : ℕ), f i) = 0 := by
--       exact tsum_eq_zero_of_not_summable hf
--     simp [aux]
--     refine Eq.symm (tsum_eq_zero_of_not_summable ?_)


--     sorry


-- theorem tsum_to_finite_aux [TopologicalSpace K] (n : ℕ) (f : ℕ → K) (g' : K →ₗ[R] K)
--   (h : ∀ i, (¬ i ∈ range n) → f i ∈ LinearMap.ker g')
--   : ∑' (i : ℕ), f i - ∑ i ∈ range n, f i ∈ LinearMap.ker g' := by

--   sorry

-- theorem tsum_to_finite_aux' [TopologicalSpace K] (n : ℕ) (f : ℕ → K) (g' : K →ₗ[R] K)
--   (h : ∀ i, (¬ i ∈ range n) → g' (f i) = 0)
--   : g' (∑' (i : ℕ), f i) = g' (∑ i ∈ range n, f i) := by

--   sorry



-- theorem tsum_to_finite [TopologicalSpace K][T2Space K] (n : ℕ) :
--   (PowerSeries.coeff n) (∑' (i : ℕ), (PowerSeries.C) (s i) *
--     (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1)
--     (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g))))
--     = (PowerSeries.coeff n) (∑ i ∈ range (n + 1), PowerSeries.C (s i) *
--       (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1)
--       (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g)))):= by
--   refine LinearMap.sub_mem_ker_iff.mp ?_
--   have eq_zero : ∀ i, (¬ i ∈ range (n + 1)) → PowerSeries.C (s i) *
--     (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g))) ∈
--     LinearMap.ker (PowerSeries.coeff n) := by
--     intro i hi
--     simp
--     have has_subst : PowerSeries.HasSubst ((PowerSeries.monomial (q ^ i)) (1 : K)) := by
--       sorry
--     have eq_aux : (PowerSeries.coeff n) (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) (1 : K))
--       (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g))) = 0 := by
--       rw [PowerSeries.coeff_subst' has_subst]
--       refine finsum_eq_zero_of_forall_eq_zero ?_
--       intro d
--       by_cases hd0 : d = 0
--       · simp [hd0, RecurFunAux]
--       ·
--         have dge : d ≥ 1 := by omega
--         have eq_zero :(PowerSeries.coeff n) ((PowerSeries.monomial (q ^ i)) (1 : K) ^ d) = 0:= by
--           -- have eq_aux : ((PowerSeries.monomial K (q ^ i)) 1 ^ d) =
--           --   PowerSeries.monomial K (q ^ i ^ d) 1 := by
--           --   sorry

--           sorry
--         simp [eq_zero]
--     simp [eq_aux]

--   sorry

include hp_prime hn hq hg in
lemma HasSum_aux [TopologicalSpace K] (hs0 : s 0 = 0) : HasSum
  (fun i ↦
    PowerSeries.C (s i) *
      (PowerSeries.map (σ ^ i))
        (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg))))
  (RecurFun hp_prime hn hq σ s g hg - (PowerSeries.map (algebraMap (↥R) K)) g) := by
  have qneq : q ≠ 0 := by
    rw [hq]
    refine pow_ne_zero t <| Nat.Prime.ne_zero hp_prime
  have qneq' : q ≠ 1 := by
    rw [hq]
    refine Ne.symm <| Nat.ne_of_lt <| Nat.one_lt_pow hn <| Nat.Prime.one_lt hp_prime
  obtain q_pow_ne := fun {x : ℕ} => pow_ne_zero x qneq
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
      (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg))))
      = (PowerSeries.coeff d) ((RecurFun hp_prime hn hq σ s g hg) -
      (PowerSeries.map (algebraMap R K) g)) := by
      simp [RecurFun]
      by_cases hd : d ≤ 1
      · if d_zero : d = 0 then
        conv => rhs; simp [d_zero, RecurFunAux, hg]
        apply Finset.sum_eq_zero
        intro x hx
        have zero_aux : (PowerSeries.coeff d) (PowerSeries.subst ((PowerSeries.monomial
          (q ^ x)) (1 : K)) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg)))
          = 0 := by
          rw [PowerSeries.coeff_subst']
          apply finsum_eq_zero_of_forall_eq_zero <| fun m => by
            if hm : m = 0 then simp [hm, RecurFunAux]
            else
            rw [PowerSeries.monmial_pow, PowerSeries.coeff_monomial, if_neg]
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
          (q ^ x)) (1 : K)) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg)))
          = 0 := by
            rw [PowerSeries.coeff_subst']
            apply finsum_eq_zero_of_forall_eq_zero <| fun m => by
              rw [PowerSeries.monmial_pow, PowerSeries.coeff_monomial, if_neg]
              simp
              simp [deq]
              if hm : m = 0 then simp [hm]
              else
              have aux : m * q ^ x > 1 := by
                refine Right.one_lt_mul_of_le_of_lt (by grind)
                  <| Nat.one_lt_pow hx' <| by grind
              exact Nat.ne_of_lt aux
            exact PowerSeries.HasSubst.monomial' q_pow_ne 1
          simp [zero_aux]
      · nth_rw 2 [show d = d - 1 + 1 by grind]
        rw [RecurFunAux]
        rw [Finset.sum_attach ((Icc 1 (multiplicity q (d - 1 + 1)))) (fun j =>
          s j * (⇑σ)^[j] (RecurFunAux hp_prime hn hq σ s g hg ((d - 1 + 1) / q ^ j)))]
        rw [←show d = d - 1 + 1 by grind]
        have eq_aux' : ∑ x ∈ N', s x * (⇑σ)^[x] ((PowerSeries.coeff d)
          (PowerSeries.subst ((PowerSeries.monomial (q ^ x)) 1)
          (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg)))) =
          ∑ x ∈ Icc 1 (multiplicity q d), s x * (⇑σ)^[x] (RecurFunAux hp_prime hn hq σ s g hg (d / q ^ x)) := by
          have disj_aux : Disjoint (Icc 1 (multiplicity q d))
            (N' \ (Icc 1 (multiplicity q d))) := disjoint_sdiff
          have N'_eq : N' = (Icc 1 (multiplicity q d)).disjUnion (N' \ (Icc 1 (multiplicity q d))) disj_aux := by
            simp at hN'
            simp [hN']
          have eq_aux₂ : ∑ x ∈ Icc 1 (multiplicity q d), s x * (⇑σ)^[x] ((PowerSeries.coeff d)
            (PowerSeries.subst ((PowerSeries.monomial (q ^ x)) 1)
              (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg))))
            = ∑ x ∈ Icc 1 (multiplicity q d), s x * (⇑σ)^[x] (RecurFunAux hp_prime hn hq σ s g hg (d / q ^ x)) := by
            apply Finset.sum_congr rfl <| fun x hx => by
              congr
              have monomial_eq : ((PowerSeries.monomial (q ^ x)) (1 : K) ^ (d / q ^ x)) =
                ((PowerSeries.monomial d)) 1 := by
                rw [PowerSeries.monmial_pow]
                simp
                congr
                simp at hx
                refine (Nat.dvd_iff_div_mul_eq d (q ^ x)).mp
                  <| pow_dvd_of_le_multiplicity hx.2
              rw [PowerSeries.coeff_subst', finsum_eq_single _ (d / q^x), PowerSeries.coeff_mk,
                monomial_eq]
              simp
              intro m hm
              simp [PowerSeries.monmial_pow, PowerSeries.coeff_monomial]
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
          have xge_one : x ≥ 1 := Nat.one_le_iff_ne_zero.mpr hx_zero
          have xgt_aux : x > multiplicity q d := hx.2 xge_one
          have zero_aux : (PowerSeries.coeff d) (PowerSeries.subst ((PowerSeries.monomial (q ^ x)) (1 : K))
            (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg))) = 0 := by
            rw [PowerSeries.coeff_subst']
            apply finsum_eq_zero_of_forall_eq_zero
            intro m
            simp
            rw [PowerSeries.monmial_pow, PowerSeries.coeff_monomial, if_neg, mul_zero]
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
    simp [eq_aux, hU₁]


include hp_prime hn hq hg in
lemma summable_aux [TopologicalSpace K] (hs0 : s 0 = 0) : Summable
  (fun i ↦
    PowerSeries.C (s i) *
      (PowerSeries.map (σ ^ i))
        (PowerSeries.subst ((PowerSeries.monomial (q ^ i)) 1) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g hg))))
  := by
  use (RecurFun hp_prime hn hq σ s g hg - (PowerSeries.map (algebraMap (↥R) K)) g)
  exact HasSum_aux hp_prime hn hq σ s g hg hs0

include hg in
theorem Fun_eq_of_RecurFun [TopologicalSpace K] [T2Space K] (hs0 : s 0 = 0) :
  (RecurFun hp_prime hn hq σ s g hg) = (PowerSeries.map (algebraMap R K) g) +
    ∑' (i : ℕ), ((PowerSeries.C (s i)) * (PowerSeries.map (σ^i)
    (PowerSeries.subst (PowerSeries.monomial (q ^ (i)) 1) (RecurFun hp_prime hn hq σ s g hg)))) := by
  have eq_aux : ∑' (i : ℕ), ((PowerSeries.C (s i)) * (PowerSeries.map (σ^(i))
    (PowerSeries.subst (PowerSeries.monomial (q ^ (i)) 1) (RecurFun hp_prime hn hq σ s g hg))))
    = (RecurFun hp_prime hn hq σ s g hg - (PowerSeries.map (algebraMap (↥R) K)) g) := by
    rw [HasSum.tsum_eq]
    exact HasSum_aux hp_prime hn hq σ s g hg hs0
  rw [eq_aux]
  ring

-- include hp_prime hn hq in
-- theorem exist_of_RecurFun [TopologicalSpace K] [T2Space K] (hs0 : s 0 = 0) :
--   ∃ (f : PowerSeries K),
--   f = (PowerSeries.map (algebraMap R K) g) +  ∑' (i : ℕ), ((PowerSeries.C (s i))
--     * (PowerSeries.map (σ^(i)) (PowerSeries.subst (PowerSeries.monomial (q ^ (i)) 1) f))) := by
--   use (RecurFun hp_prime hn hq σ s g)
--   refine PowerSeries.ext ?_
--   intro n

--   sorry


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
  (coeff_aux_mem σ hs l) [SMOD I.MvPowerSeries] := sorry

include hs hp in
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

      sorry
  sorry



lemma finst_attach {t : Finset ℕ} (f : ℕ → R) : ∑ i ∈ t.attach, f i = ∑ i ∈ t, f i := by
  exact sum_attach t f

end FunctionalEquationIntegralityLemma

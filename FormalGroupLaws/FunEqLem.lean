import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution
import FormalGroupLaws.Basic
import FormalGroupLaws.BasicLem
import FormalGroupLaws.SubstInv
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.ENNReal.Lemmas



noncomputable section

open MvPowerSeries Classical Finset
open scoped WithPiTopology


namespace FunctionalEquationIntegralityLemma

/- The basic ingredients in this section are `R ⊆ K, σ : K → K, 𝔞 ⊆ R, p, q, s₁, s₂ ⋯`,
  where `R` is a subring of `K`, `σ` is a ring homomorphism of `K`, which stablize `A`,
  `𝔞` is an ideal of `A`, `p` is a prime number and `q` is a power of `p`, `s_i` are
  elements of `K`. -/

-- `need ask` define a subring R of K as `[Algebra R K]` and `[FaithfulSMul R K]`
-- variable {K : Type*} [CommRing K] {R : Subring K} [CommRing R] {𝔞 : Ideal R}
-- variable {K : Type*} [CommRing K] {R : Type*} [CommRing R] [Algebra R K]
--   [FaithfulSMul R K] {𝔞 : Ideal R} {𝔞_K : Ideal K} (h_ideal : 𝔞_K = Ideal.map (algebraMap R K) 𝔞)

-- variable {p n q: ℕ} (hp : Nat.Prime p) (hn : n ≥ 1) (hq : q = p ^ n)

-- variable {σ : K →+* K}  (hs : ∀ (a : R), σ (algebraMap R K a) ∈ algebraMap R K '' Set.univ)
--   {x : R}
--   (hs_mod : ∀ (a : R), σ (algebraMap R K a) ≡ algebraMap R K (a ^ q) [SMOD 𝔞_K])

-- variable (hp : (p : R) ∈ 𝔞) {s : ℕ → K}
--   (hs_i : ∀ i, ∀ a ∈ 𝔞, s i * (algebraMap R K a) ∈ algebraMap R K '' Set.univ)
--   (hs_i' :
--   ∀ r : ℕ, ∀ b : K,
--     (∀ a ∈ 𝔞 ^ r, b • (algebraMap R K a) ∈ algebraMap R K '' Set.univ) →
--     ∀ a ∈ 𝔞 ^ r, (σ b) • (algebraMap R K a) ∈ algebraMap R K '' Set.univ)

variable {K : Type*} [CommRing K] {R : Subring K} {𝔞 : Ideal R}


variable {p t q: ℕ} (hp_prime : Nat.Prime p) (hn : t ≠ 0) (hq : q = p ^ t)

variable (σ : K →+* K)  (hs : ∀ (a : R), σ a ∈ R)
  {x : R}
  (hs_mod : ∀ (a : R), (⟨ σ a, hs a⟩) ≡  (a ^ q) [SMOD 𝔞])

variable (hp : (p : R) ∈ 𝔞) (s : ℕ → K)
  (hs_i : ∀ i, ∀ a ∈ 𝔞, s i * a ∈ R)
  (hs_i' :∀ r : ℕ, ∀ b : K,
    (∀ a ∈ 𝔞 ^ r, b * (algebraMap R K a) ∈ Set.image (algebraMap R K) 𝔞) →
    ∀ a ∈ 𝔞 ^ r, (σ b) * (algebraMap R K a) ∈ Set.image (algebraMap R K) 𝔞)

  -- (hs_i1 : ∀ r : ℕ, ∀ b : K, (({b}) *  (𝔞 ^ r : Ideal R) : Set R)  ⊆ (𝔞 : Set R) →
  --    {(σ b)} * ((𝔞 ^ r : Ideal R) : Set R) ⊆ (𝔞 : Set R))

variable (g : PowerSeries R) (hg : PowerSeries.constantCoeff R g = 0)


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
include hg in
def RecurFunAux : ℕ → K
  | 0 => 0
  -- | 1 => PowerSeries.coeff R 1 g
  | k + 1 =>
    PowerSeries.coeff R (k + 1) g + ∑ j ∈ (Icc 1 (multiplicity q (k + 1))).attach,
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
      (s j) * σ^[j] (RecurFunAux ((k + 1) / (q ^ (j : ℕ))))

-- if you want to elimilate the attach here, use `sum_attach`.

-- This is f_g
def RecurFun : PowerSeries K :=
  PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g)


/- Functional equation lemma.
  Let the notation defined as above, let `g(X) = ∑_{i=1}^∞ b_i X^i`, `g_bar (X) = ∑_{i=1}^∞ (b_bar i) X^i`.
  be two power series in one variable over `A`, and suppose that `b₁` is invertible in `A`. Then we have:
  (i) the power series F_g(X,Y)=f_g⁻¹(f_g(X)+f_g(Y)) has its coefficients in `A`.
  (ii) the power series `f_g⁻¹ (f_g_bar (X))` has its coefficient in `A`.
  (iii) if `h(X)=∑_{n=1}^∞ c_n X^n` is a power series with coefficients in `A`, then there is a
  power series `h^hat (X) = ∑_{n=1}^∞ c_n^hat X^n` with `c_n^hat ∈ A`, `n=1,2,…`, such that
  `f_g(h(X))=f_{h^hat}(X)`.
  (iv) if `α(X) ∈ A⟦X⟧, β(X) ∈ K⟦X⟧` are two power series, and `r ∈ ℕ, r ≥ 1`, then we have
  `α(X) ≡ β(X) [MOD 𝔞^r • A⟦X⟧] ↔ f_g(α(X)) ≡ f_g (β(X) [MOD 𝔞^r • A⟦X⟧])`.

  If `f_g(X)` and `f_{g_bar}(X)` are power series obtained by the recursion equation with
  everything the same except possibly `g(X) ≠ g_bar(X)`, then we shall say that
  `f_g(X)` and `f_{g_bar}(X)` satisfy the same type of functional equation.-/

-- /-- If `f_g(X)` and `f_{g_bar}(X)` are power series obtained by the recursion equation with
--   everything the same except possibly `g(X) ≠ g_bar(X)`, then we shall say that
--   `f_g(X)` and `f_{g_bar}(X)` satisfy the same type of functional equation. -/


include 𝔞 hs_i' in
lemma sigma_mem_aux : ∀ (r : ℕ), ∀ b : K,
  (∀ a ∈ 𝔞 ^ r, b * (algebraMap R K a) ∈ Set.image (algebraMap R K) 𝔞) →
  (∀ j : ℕ, ∀ a ∈ 𝔞 ^ r, ((σ^j) b) * (algebraMap R K a) ∈ Set.image (algebraMap R K) 𝔞) := by
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
  → (∀ c ∈ I^r * I, x * c ∈ Set.image (algebraMap R K) I) := by
  intro h
  intro c hc
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
    have mem_aux : y1 + z1 ∈ I := by
      exact (Submodule.add_mem_iff_right I hy1).mpr hz1
    have mem_aux' : (y1 : K) + ↑z1 ∈ R := by
      refine add_mem ?_ ?_
      exact SetLike.coe_mem y1
      exact SetLike.coe_mem z1
    use mem_aux'
    constructor
    exact mem_aux
    rw [←hy2, ←hz2]
    exact rfl



lemma ideal_pow_mem' {I : Ideal R} {r s: ℕ} {x : K} (hs : s > r):  (∀ b ∈ I^r, x * b ∈ R)
  → (∀ c ∈ I^s, x * c ∈ Set.image (algebraMap R K) I) := by
  intro h
  obtain h1 := ideal_pow_mem h
  have eq_aux : I ^ r * I = I ^ (r + 1) := rfl
  rw [eq_aux] at h1
  have subset_aux : I ^ s ≤ I ^ (r + 1) := by
    exact Ideal.pow_le_pow_right hs
  intro c hc
  have c_mem : c ∈ I ^ (r + 1) := by
    exact subset_aux hc
  exact h1 c (subset_aux hc)


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



include 𝔞  hs_i hs_i'  in
/-- Let a_n be the coefficient of f_g, then a_n * 𝔞^r ⊆ R, where r is the multiplicity of
  q in n. -/
lemma coeff_RecurFun_mul_mem (n : ℕ) :
  ∀ (x : R), x ∈ 𝔞 ^ (multiplicity q n) →
    (PowerSeries.coeff K n (RecurFun hp_prime hn hq σ s g)) * x ∈ R := by
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
          (RecurFunAux hp_prime hn hq σ s g (n / q ^ ↑i))) * x ∈ R := by
          rw [sum_mul]
          refine Subring.sum_mem R ?_
          intro i hi
          rw [mul_assoc]
          have mem_aux2 : ((σ ^ i) (RecurFunAux hp_prime hn hq σ s g (n / q ^ i)) * ↑x)
            ∈ Set.image (algebraMap R K) 𝔞 := by
            have aux : ∀ b ∈ 𝔞 ^ multiplicity q n, (RecurFunAux hp_prime hn hq σ s g (n / q ^ i)) * (algebraMap R K b)
              ∈ ⇑(algebraMap (↥R) K) '' ↑𝔞 := by
              intro b hb
              rw [h] at hb
              have lt_aux : multiplicity q (n / q ^ i) < k := by
                rw [←h]
                simp at hi
                obtain ⟨hi1, hi2⟩ := hi
                have hq' : q > 1 := by
                  rw [hq]
                  have pge : p > 1 := Nat.Prime.one_lt hp_prime
                  exact Nat.one_lt_pow hn pge
                exact multiplicity_aux n i q hq' (by omega) hi2 hi1
              have le_aux : multiplicity q (n / q ^ i) ≤ k := by linarith
              have b_mem : b ∈ 𝔞 ^ multiplicity q (n / q ^ i) := by
                exact SetLike.le_def.mp (Ideal.pow_le_pow_right le_aux (I := 𝔞)) hb
              obtain h1 := hk _ lt_aux (n / q ^ i) rfl
              obtain h2 := ideal_pow_mem' lt_aux h1 b hb
              rw [RecurFun, PowerSeries.coeff_mk, show ↑b = (algebraMap R K) b  by rfl] at h2
              exact h2
            rw [←h] at hx
            obtain h₁ := sigma_mem_aux σ hs_i' (multiplicity q n) _ aux i x hx
            have eq_aux : (algebraMap (↥R) K) x = (x : K) := rfl
            rw [eq_aux] at h₁
            exact h₁
          have mem_aux : ((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s g (n / q ^ i)) * ↑x)
            ∈ R := mem_image_aux₂ mem_aux2
          have mem_aux1 : ⟨((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s g (n / q ^ i)) * ↑x), mem_aux⟩ ∈ 𝔞 := by
            have aux : ((⇑σ)^[i] (RecurFunAux hp_prime hn hq σ s g (n / q ^ i)) * ↑x)
              ∈ Set.image (algebraMap R K) 𝔞 := by
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

lemma coeff_infty_sum [TopologicalSpace K]
  -- [Preorder (PowerSeries K)] [Preorder K]
  -- [OrderClosedTopology K] [OrderClosedTopology (PowerSeries K)]
  (f : ℕ → PowerSeries K) (n : ℕ):
  PowerSeries.coeff K n (∑' (i : ℕ), f i) = ∑' (i : ℕ), PowerSeries.coeff K n (f i) := by
  sorry
  -- refine Summable.map_tsum hf (PowerSeries.coeff K n) ?_
  -- exact PowerSeries.WithPiTopology.continuous_coeff K n

theorem tsum_to_finite_aux [TopologicalSpace K] (n : ℕ) (f : ℕ → K) (g' : K →ₗ[R] K)
  (h : ∀ i, (¬ i ∈ range n) → f i ∈ LinearMap.ker g')
  : ∑' (i : ℕ), f i - ∑ i ∈ range n, f i ∈ LinearMap.ker g' := by

  sorry

theorem tsum_to_finite_aux' [TopologicalSpace K] (n : ℕ) (f : ℕ → K) (g' : K →ₗ[R] K)
  (h : ∀ i, (¬ i ∈ range n) → g' (f i) = 0)
  : g' (∑' (i : ℕ), f i) = g' (∑ i ∈ range n, f i) := by

  sorry



theorem tsum_to_finite [TopologicalSpace K] (n : ℕ) :
  (PowerSeries.coeff K n) (∑' (i : ℕ), (PowerSeries.C K) (s i) *
    (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial K (q ^ i)) 1)
    (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g))))
    = (PowerSeries.coeff K n) (∑ i ∈ range (n + 1), (PowerSeries.C K) (s i) *
      (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial K (q ^ i)) 1)
      (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g)))):= by
  refine LinearMap.sub_mem_ker_iff.mp ?_
  have eq_zero : ∀ i, (¬ i ∈ range (n + 1)) → (PowerSeries.C K) (s i) *
    (PowerSeries.map (σ ^ i)) (PowerSeries.subst ((PowerSeries.monomial K (q ^ i)) 1) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g))) ∈
    LinearMap.ker (PowerSeries.coeff K n) := by
    intro i hi
    simp
    have has_subst : PowerSeries.HasSubst ((PowerSeries.monomial K (q ^ i)) 1) := by
      sorry
    have eq_aux : (PowerSeries.coeff K n) (PowerSeries.subst ((PowerSeries.monomial K (q ^ i)) 1) (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g))) = 0 := by
      rw [PowerSeries.coeff_subst' has_subst]
      refine finsum_eq_zero_of_forall_eq_zero ?_
      intro d
      by_cases hd0 : d = 0
      · simp [hd0, RecurFunAux]
      ·
        have dge : d ≥ 1 := by omega
        have eq_zero :(PowerSeries.coeff K n) ((PowerSeries.monomial K (q ^ i)) 1 ^ d) = 0:= by
          -- have eq_aux : ((PowerSeries.monomial K (q ^ i)) 1 ^ d) =
          --   PowerSeries.monomial K (q ^ i ^ d) 1 := by
          --   sorry

          sorry
        simp [eq_zero]
    simp [eq_aux]

  sorry

include hp_prime hn hq hg in
theorem Fun_eq_of_RecurFun [TopologicalSpace K]
  -- [Preorder K] [PartialOrder K] [IsOrderedAddMonoid K]
  -- [CanonicallyOrderedAdd K]
  -- [OrderClosedTopology K]
  (hs0 : s 0 = 0) :
  (RecurFun hp_prime hn hq σ s g) = (PowerSeries.map (algebraMap R K) g) +
    ∑' (i : ℕ), ((PowerSeries.C K (s i)) * (PowerSeries.map (σ^(i))
    (PowerSeries.subst (PowerSeries.monomial K (q ^ (i)) 1) (RecurFun hp_prime hn hq σ s g)))) := by
  refine PowerSeries.ext ?_
  intro n
  by_cases hn0 : n = 0
  ·
    simp [RecurFun]
    rw [coeff_infty_sum, hn0]
    conv =>
      lhs; rw [RecurFunAux]
    simp [hg]
    apply Eq.symm
    have eq_aux :∀ (i : ℕ),  s i * (⇑σ)^[i] ((PowerSeries.constantCoeff K)
      (PowerSeries.subst ((PowerSeries.monomial K (q ^ i)) 1)
      (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g)))) = 0 := by
      intro i
      by_cases hi0 : i = 0
      · simp [hi0, hs0]
      · have ipos : i > 0 := Nat.zero_lt_of_ne_zero hi0
        have pos_aux : q ^ i > 0 := by
          refine Nat.pow_pos ?_
          rw [hq]
          exact Nat.pow_pos (Nat.Prime.pos hp_prime)
        have eq_aux₂ : (PowerSeries.constantCoeff K)
          (PowerSeries.subst ((PowerSeries.monomial K (q ^ i)) 1)
          (PowerSeries.mk (RecurFunAux hp_prime hn hq σ s g))) = 0 := by
          have has_subst₁ : PowerSeries.HasSubst ((PowerSeries.monomial K (q ^ i)) 1) :=
            PowerSeries.HasSubst.monomial' (by linarith) 1
          rw [PowerSeries.constantCoeff, PowerSeries.constantCoeff_subst has_subst₁]
          simp
          refine finsum_eq_zero_of_forall_eq_zero ?_
          intro d
          by_cases hd0 : d = 0
          · simp [hd0, RecurFunAux]
          ·
            have eq_zero : PowerSeries.constantCoeff K ((PowerSeries.monomial K (q ^ i)) 1) = 0 := by
              rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_monomial, if_neg]

              linarith
            simp [eq_zero, zero_pow hd0]
        simp [eq_aux₂]
    simp_rw [eq_aux, tsum_zero]
  by_cases hn_coprime : multiplicity q n = 0
  · simp [RecurFun, PowerSeries.coeff_mk, coeff_infty_sum]
    conv =>
      lhs

    sorry
  · sorry

include hp_prime hn hq in
theorem exist_of_RecurFun [TopologicalSpace K] (hs0 : s 0 = 0) :
  ∃ (f : PowerSeries K),
  f = (PowerSeries.map (algebraMap R K) g) +  ∑' (i : ℕ), ((PowerSeries.C K (s i))
    * (PowerSeries.map (σ^(i)) (PowerSeries.subst (PowerSeries.monomial K (q ^ (i)) 1) f))) := by
  use (RecurFun hp_prime hn hq σ s g)
  refine PowerSeries.ext ?_
  intro n

  sorry



lemma finst_attach {t : Finset ℕ} (f : ℕ → R) : ∑ i ∈ t.attach, f i = ∑ i ∈ t, f i := by
  exact sum_attach t f

end FunctionalEquationIntegralityLemma

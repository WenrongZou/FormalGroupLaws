module

public import FormalGroupLaws.Basic
public import FormalGroupLaws.ForMathlib.Trunc
public import FormalGroupLaws.ForMathlib.MvPowerSeries
-- public import FormalGroupLaws.ForMathlib.FiniteField
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

@[expose] public section

noncomputable section

open ValuativeRel MvPowerSeries Classical

variable {K σ : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (π : (valuation K).Uniformizer)

instance : Fintype 𝓀[K] := Fintype.ofFinite 𝓀[K]

local notation "q" => Fintype.card (IsLocalRing.ResidueField (Valuation.integer (valuation K)))

namespace FormalGroup.LubinTate

-- variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- For a nonarchimedean local field, we have that valuation of `K` is
rank one discrete. -/
instance : (valuation K).IsRankOneDiscrete := inferInstance

structure 𝓕 where
  toPowerSeries : PowerSeries 𝒪[K]
  trunc_two : toPowerSeries.trunc 2 = Polynomial.C π.val * Polynomial.X
  mod_pi : toPowerSeries ≡ PowerSeries.X ^ q [SMOD (𝓂[K]).map PowerSeries.C]

/-- Constant coefficient fo `f : 𝓕 π` is zero. -/
lemma constanceCoeff_F {f : 𝓕 π} : f.toPowerSeries.constantCoeff = 0 := by
  calc
    _ = (f.toPowerSeries.trunc 2).constantCoeff := by
      simp [Polynomial.constantCoeff_apply, PowerSeries.coeff_trunc]
    _ = _ := by simp [f.trunc_two]

lemma coeff_one_F {f : 𝓕 π} : (PowerSeries.coeff 1) f.toPowerSeries = π.val := by
  calc
    _ = (f.toPowerSeries.trunc 2).coeff 1 := by
      rw [PowerSeries.coeff_trunc, if_pos Nat.one_lt_two]
    _ = _  := by
      simp [f.trunc_two]

end LubinTate

end FormalGroup

namespace MvPowerSeries

open FormalGroup LubinTate

variable {R σ : Type*} [CommRing R]

lemma C_dvd_iff_forall_dvd_coeff (c : R) (p : MvPowerSeries σ R) :
  C c ∣ p ↔ ∀ n, c ∣ (coeff n) p := by
  constructor <;> intro hp
  · intro n
    obtain ⟨d, rfl⟩ := hp
    simp
  · use fun n ↦ Classical.choose (hp n)
    ext n
    simp
    rw [Classical.choose_spec (hp n)]
    rfl

lemma dvd_prod_pow_sub_prod_pow_of_dvd_sub {d : R} {a b : σ → R}
    (h : ∀ i : σ, d ∣ a i - b i)
    (i : σ →₀ ℕ) :
    d ∣ (i.prod fun j e ↦ a j ^ e) - (i.prod fun j e ↦ b j ^ e) := by
  induction i using Finsupp.induction₂ with
  | zero => simp
  | add_single i e f ha hb₀ ih =>
    classical
    rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_add_index_of_disjoint,
      Finsupp.prod_single_index, Finsupp.prod_single_index]
    · obtain ⟨q', hq⟩ := ih
      rw [sub_eq_iff_eq_add] at hq
      rw [hq, add_mul, add_sub_assoc, ← mul_sub, mul_assoc]
      apply dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right _ _)
      exact (h i).trans (sub_dvd_pow_sub_pow ..)
    · simp
    · simp
    · apply Finset.disjoint_iff_inter_eq_empty.mpr
      ext w
      simp [Finsupp.single, hb₀]
      contrapose!
      rintro rfl
      simpa using ha
    · apply Finset.disjoint_iff_inter_eq_empty.mpr
      ext w
      simp [Finsupp.single, hb₀]
      contrapose!
      rintro rfl
      simpa using ha

end MvPowerSeries

namespace FormalGroup

namespace LubinTate

instance Invertible.pi_sub_pi_pow {k : ℕ} [NeZero k] :
    Invertible (1 - π.val ^ k) := by
  have : π.val ^ k ∈ 𝓂[K] := by
    simp [Ideal.pow_mem_of_mem, π.valuation_gt_one.not_isUnit, Nat.pos_of_neZero]
  exact IsUnit.invertible <| IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ this

lemma pi_pow_ne_one {k : ℕ} (hk : k ≠ 0) :
    π.val ^ k ≠ 1 := by
  by_contra! hc
  haveI : NeZero k := ⟨hk⟩
  apply Invertible.ne_zero (1 - π.val ^ k)
  simp [hc]

-- variable {k : ℕ} [NeZero k] in
-- #check  ⅟(1 - π.val ^ k)

instance [Finite σ] : Fintype σ := Fintype.ofFinite σ

open Finset Fintype Finsupp

variable [Finite σ] (f g : 𝓕 π) (a : σ →₀ 𝒪[K])
  -- {L : MvPolynomial σ 𝒪[K]}
  -- (hL : ∀ i ∈ L.support, Finset.univ.sum i = 1)

abbrev L : MvPolynomial σ 𝒪[K] := MvPolynomial.sumSMulX a

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
lemma truncTotal_one_L : (L a).toMvPowerSeries.truncTotal 1 = 0 := by
  ext d
  simp +contextual [coeff_truncTotal_eq_ite, L,
    MvPolynomial.sumSMulX, linearCombination, Finsupp.sum, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_X']
  simp +contextual [Finset.sum_eq_zero, d.degree_eq_zero_iff.mp]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Finite σ] in
lemma coeff_L_eq_zero_of_one_lt_degree {d : σ →₀ ℕ} (hd : 1 < d.degree) :
    MvPolynomial.coeff d (L a) = 0 := by
  have {x : σ} : ¬ single x 1 = d := by
    by_contra! hc
    simp [← hc] at hd
  simp [L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_X', this]


def Ideal_aux : Ideal (MvPowerSeries σ 𝒪[K]) := 𝓂[K].map C

lemma qK_neZero : q ≠ 0 := card_ne_zero

example {i : σ} : C π.val * X i ∈ 𝓂[K].map C := by
  have : C π.val (σ := σ) ∈ C '' 𝓂[K] :=
    (Set.mem_image C 𝓂[K] (C π.val)).mpr ⟨π, π.valuation_gt_one.not_isUnit, rfl⟩
  exact Ideal.IsTwoSided.mul_mem_of_left (X i) (Submodule.mem_span_of_mem this)

lemma maximalIdeal_eq_span : 𝓂[K] = Ideal.span {π.val} := π.is_generator

omit [Finite σ] in
lemma frob_eq {f : MvPowerSeries σ 𝒪[K]} :
    f ^ q ≡ f.expand q card_ne_zero [SMOD 𝓂[K].map C] := by
  -- have : 𝒪[K] →+* 𝓀[K] := by exact IsLocalRing.residue ↥𝒪[K]
  let φ := IsLocalRing.residue 𝒪[K]
  have : (f ^ q).map φ = (f.expand q card_ne_zero).map φ := by
    simp [FiniteField.MvPowerSeries.expand_card]
  have : (f ^ q - (f.expand q card_ne_zero)) ∈ RingHom.ker (MvPowerSeries.map φ) := by
    exact (RingHom.sub_mem_ker_iff (MvPowerSeries.map φ)).mpr this
  refine SModEq.sub_mem.mpr ?_
  convert this
  rw [ker_map, IsLocalRing.ker_residue]

omit [Finite σ] in
lemma pi_dvd_sub_iff_smod_eq {F G : MvPowerSeries σ 𝒪[K]} :
    C π.val ∣ F - G ↔ F ≡ G [SMOD 𝓂[K].map C] := by
  constructor
  · intro ⟨a, ha⟩
    refine SModEq.sub_mem.mpr ?_
    rw [ha]
    have : C π.val (σ := σ) ∈ (C '' 𝓂[K]) := by
      simp [π.valuation_gt_one.not_isUnit]
    exact Ideal.IsTwoSided.mul_mem_of_left _ (Submodule.mem_span_of_mem this)
  · intro h
    obtain ha := SModEq.sub_mem.mp h
    simp only [maximalIdeal_eq_span π, Ideal.map_span, Set.image_singleton] at ha
    exact Ideal.mem_span_singleton.mp ha

lemma pi_dvd_sub (F : MvPowerSeries σ 𝒪[K]) {n : ℕ} (hn : n ≠ 0) :
    C π.val * C (1 - π.val ^ n) ∣ F.subst (g.toPowerSeries.toMvPowerSeries · ) -
      f.toPowerSeries.subst F := by
  haveI : NeZero n := { out := hn }
  have : C π.val * C (1 - π.val ^ n) * C (⅟(1 - π.val ^ n)) ∣
      F.subst (g.toPowerSeries.toMvPowerSeries · ) - f.toPowerSeries.subst F := by
    rw [mul_assoc, ← map_mul, Invertible.mul_invOf_self, map_one, mul_one]
    apply (pi_dvd_sub_iff_smod_eq _ ).mpr

    sorry
  exact dvd_of_mul_right_dvd this

-- variable (π f g) in
variable {π} in
def Phi_aux : ℕ → MvPowerSeries σ 𝒪[K]
  | 0 => 0
  -- | 1 => L a
  | n + 1 =>
    if h : n = 0 then L a else
    -- have : C π.val * C (1 - π.val ^ n) ∣ (Phi_aux n).subst (g.toPowerSeries.toMvPowerSeries · ) -
    --   f.toPowerSeries.subst (Phi_aux n) := pi_dvd_sub π f g (Phi_aux n) h
    Phi_aux n + homogeneousComponent (n + 1) (pi_dvd_sub π f g (Phi_aux n) h).choose

@[simp]
lemma Phi_aux_zero : Phi_aux f g a 0 = 0 := rfl

@[simp]
lemma Phi_aux_one : Phi_aux f g a 1 = L a := rfl

variable {n : ℕ}

lemma constantCoeff_Phi_aux : (Phi_aux f g a n).constantCoeff = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    by_cases! hk : k = 0
    · simp [hk, L, MvPolynomial.sumSMulX, ← coeff_zero_eq_constantCoeff, linearCombination,
        Finsupp.sum, MvPolynomial.coeff_sum]
    simp [Phi_aux, dif_neg hk, map_add, ih, ← coeff_zero_eq_constantCoeff,
      coeff_homogeneousComponent, _root_.add_zero]

lemma constantCoeff_choose (h : n ≠ 0) :
    (pi_dvd_sub π f g (Phi_aux f g a n) h).choose.constantCoeff = 0 := by
  obtain h_spec := (pi_dvd_sub π f g (Phi_aux f g a n) h).choose_spec
  have : (C π.val * C (1 - π.val ^ n) * (pi_dvd_sub π f g
      (Phi_aux f g a n) h).choose).constantCoeff = 0 := by
    rw [← h_spec, map_sub, constantCoeff_subst_eq_zero,
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_Phi_aux ..) _
        (constanceCoeff_F π), sub_zero]
    · exact hasSubst_of_constantCoeff_zero <| PowerSeries.constantCoeff_toMvPowerSeries
        (constanceCoeff_F π)
    · exact PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)
    exact constantCoeff_Phi_aux π f g a
  simp only [map_sub, map_one, map_pow, map_mul, constantCoeff_C, mul_eq_zero] at this
  obtain (h1 | h2) | h3 := this
  · absurd π.ne_zero
    simpa
  · absurd h2
    exact (sub_ne_zero.mpr (pi_pow_ne_one π h).symm)
  · simpa using h3

lemma coeff_Phi_aux_of_lt {d : σ →₀ ℕ} (h : n < d.degree) :
    (Phi_aux f g a n).coeff d = 0 := by
  induction n generalizing d with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · simp only [hk, _root_.zero_add, Phi_aux_one, MvPolynomial.coeff_coe] at ⊢ h
      exact coeff_L_eq_zero_of_one_lt_degree _ h
    have : d.degree ≠ k + 1 := by exact Nat.ne_of_lt' h
    simp [Phi_aux, dif_neg hk, ih (Nat.lt_of_succ_lt h),
      coeff_homogeneousComponent, (Nat.ne_of_lt' h)]

lemma homogenous_Phi_aux_of_lt {m : ℕ} (h : n < m) :
    homogeneousComponent m (Phi_aux f g a n) = 0 := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_zero, ZeroMemClass.coe_zero,
    ZeroMemClass.coe_eq_zero, ite_eq_right_iff]
  grind [coeff_Phi_aux_of_lt]

lemma homogeneous_Phi_aux (h : n ≠ 0) :
    (homogeneousComponent (n + 1)) (Phi_aux f g a n.succ) =
      ((pi_dvd_sub π f g (Phi_aux f g a n) h).choose).homogeneousComponent (n + 1) := by
  nth_rw 1 [Phi_aux, dif_neg h, map_add]
  rw [← isHomogeneous_iff_eq_homogeneousComponent.mp (isHomogeneous_homogeneousComponent _ _),
    add_eq_right]
  exact homogenous_Phi_aux_of_lt _ _ _ _ (lt_add_one _)
section

variable {π} in
/-- This is a unique solution in the constructive lemma. -/
def Phi : MvPowerSeries σ 𝒪[K] := fun d => (Phi_aux f g a d.degree).coeff d

@[simp]
lemma coeff_Phi {d : σ →₀ ℕ} : (Phi f g a).coeff d = (Phi_aux f g a d.degree).coeff d := rfl

end

@[simp]
lemma constantCoeff_Phi : (Phi f g a).constantCoeff = 0 := by rfl

@[simp]
lemma Phi_truncTotal_one : (Phi f g a).truncTotal 1 = 0 := by
  ext d
  simp [truncTotal_degree_one]

lemma Phi_truncTotal_two : (Phi f g a).truncTotal 2 = L a := by
  ext d
  norm_cast
  by_cases! h : d.degree < 2
  · rw [coeff_truncTotal _ h, coeff_Phi]
    by_cases hd₀ : d.degree = 0
    · simp [(degree_eq_zero_iff d).mp hd₀, L, MvPolynomial.sumSMulX,
        Finsupp.linearCombination_apply, Finsupp.sum, MvPolynomial.coeff_sum, Finset.sum_eq_zero]
    by_cases hd₁ : d.degree = 1
    · simp [hd₁]
    grind
  rw [coeff_truncTotal_eq_zero _ h, L, MvPolynomial.sumSMulX, Finsupp.linearCombination_apply,
    Finsupp.sum, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_X']
  have this {x : σ} {h1 : x ∈ a.support} : single x 1 ≠ d := by
    by_contra! hc
    simp [← hc] at h
  simp +contextual [Finset.sum_eq_zero, this]

lemma Phi_truncTotal {n : ℕ} :
    (Phi f g a).truncTotal (n + 1) = Phi_aux f g a n := by
  induction n with
  | zero => simp [Phi_truncTotal_one]
  | succ k ih =>
    by_cases! hk₀ : k = 0
    · simp [hk₀, Phi_truncTotal_two]
    ext d
    norm_cast
    by_cases hd₀ : d.degree < k + 1
    · rw [coeff_truncTotal _ (Nat.lt_add_right 1 hd₀)]
      simp [Phi_aux, dif_neg hk₀, coeff_Phi, ← ih,
        coeff_truncTotal _ hd₀, coeff_homogeneousComponent, if_neg (Nat.ne_of_lt hd₀)]
    by_cases hd₁ : k + 1 + 1 ≤ d.degree
    · simp [coeff_truncTotal_eq_zero _ hd₁, Phi_aux, dif_neg hk₀, coeff_homogeneousComponent,
        if_neg (Nat.ne_of_lt' hd₁), ← ih, coeff_truncTotal_eq_zero, Nat.le_of_succ_le hd₁]
    have hd : d.degree = k + 1 := by grind
    rw [coeff_truncTotal _ (Nat.lt_of_not_le hd₁), coeff_Phi, ← hd]

lemma Phi_aux_truncTotal_eq_self {n : ℕ} :
    (truncTotal (n + 1)) (Phi_aux f g a n) = Phi_aux f g a n := by
  ext d
  simp +contextual [coeff_truncTotal_eq_ite, coeff_Phi_aux_of_lt]

lemma Phi_aux_truncTotal_succ {n : ℕ} :
    (Phi_aux f g a n.succ).truncTotal n.succ = Phi_aux f g a n := by
  rw [Phi_aux]
  by_cases! hn : n = 0
  · simp [hn, truncTotal_one_L]
  · ext d
    simp only [Nat.succ_eq_add_one, map_sub, map_one, map_pow, dif_neg hn, map_add,
      MvPolynomial.coe_add, Phi_aux_truncTotal_eq_self, MvPolynomial.coeff_coe,
      coeff_truncTotal_eq_ite, Order.lt_add_one_iff, coeff_homogeneousComponent, Subring.coe_add,
      add_eq_left, ZeroMemClass.coe_eq_zero, ite_eq_right_iff]
    intro h1 h2
    linarith

/-- For any multivariate power series F, F is homogeneous of degree k, then
  $F(g(X_1, …, X_n)) ≡ π^k F(X_1, …, X_n)$. -/
-- lemma homogeneous_comp {k : ℕ} {F : MvPowerSeries σ 𝒪[K]} (hF : F.constantCoeff = 0)
--     (hF₁ : F.IsHomogeneous k) :
--     truncTotal (k + 1) (F.subst (g.toPowerSeries.toMvPowerSeries ·)) = π.val ^ k • F := by
--   /- use the truncTotal_subst lemma in the PR. -/

--   sorry

lemma homogeneous_subst_eq_homogeneous {k : ℕ} {F : MvPowerSeries σ 𝒪[K]}
    (hF : F.constantCoeff = 0) :
    homogeneousComponent k ((F.homogeneousComponent k).subst (g.toPowerSeries.toMvPowerSeries ·)) =
      π.val ^ k • homogeneousComponent k F := by
  sorry

lemma constructive_lemma_base :
    (truncTotal 2) (f.toPowerSeries.subst (L a)) =
      (truncTotal 2) (subst (fun x ↦ g.toPowerSeries.toMvPowerSeries x)
        (L a).toMvPowerSeries) := by
  ext d
  by_cases hd : d.degree < 2
  ·
    sorry
  simp [coeff_truncTotal_eq_ite, hd]


/-
lemma constructive_lemma : f.toPowerSeries.subst (Phi f g a) =
    (Phi f g a).subst (g.toPowerSeries.toMvPowerSeries · ) := by
  have hasSubst_aux : HasSubst fun (x : σ) ↦ (PowerSeries.toMvPowerSeries x)
    g.toPowerSeries := hasSubst_of_constantCoeff_zero
      <| PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)
  have eq_aux {n : ℕ} : (f.toPowerSeries.subst (Phi_aux f g a n)).truncTotal (n + 1) =
    ((Phi_aux f g a n).subst (g.toPowerSeries.toMvPowerSeries · )).truncTotal (n + 1) := by
    induction n using Nat.caseStrongRecOn with
    | zero =>
      simp
      rw [← substAlgHom_apply hasSubst_aux, map_zero,
        PowerSeries.subst_zero_of_constantCoeff_zero (constanceCoeff_F π)]
    | ind n ih =>
      by_cases! hn : n = 0
      · simp [hn, constructive_lemma_base π f g a]
      have {s t : MvPolynomial σ 𝒪[K]} : s.toMvPowerSeries = t.toMvPowerSeries → s = t :=
        fun a ↦ MvPolynomial.ext s t (congrFun a)
      apply this
      conv_rhs => rw [truncTotal_succ_eq, truncTotal_subst_eq_truncTotal_left
        (PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)),
        Phi_aux_truncTotal_succ]
      rw [truncTotal_succ_eq, PowerSeries.truncTotal_subst, Phi_aux_truncTotal_succ,
        ih _ (le_refl n), add_right_inj]
      conv_rhs => rw [Phi_aux, dif_neg hn, subst_add hasSubst_aux, map_add]
      nth_rw 1 [Phi_aux, dif_neg hn, PowerSeries.homogeneous_subst_add (constanceCoeff_F π)
        (constantCoeff_Phi_aux ..), coeff_one_F]
      rw [homogeneous_subst_eq_homogeneous _ _ (constantCoeff_choose π f g a hn)]
      obtain h1 := eq_add_of_sub_eq' (pi_dvd_sub π f g (Phi_aux f g a n) hn).choose_spec
      rw [← map_smul, ← map_smul, smul_eq_C_mul, smul_eq_C_mul, ← map_add, ← map_add]
      congr! 1
      have : C π.val * C (1 - π.val ^ n) (σ := σ) = C π.val - C (π.val ^ (n + 1)) := by
        rw [← map_mul, mul_sub, map_sub, mul_one]
        ring_nf
      nth_rw 2 [h1, this]
      ring
  apply eq_of_forall_truncTotal_eq.mpr
  intro n
  by_cases! hn : n = 0
  · simp [hn, truncTotal_zero]
  have : n = n - 1 + 1 := (Nat.succ_pred_eq_of_ne_zero hn).symm
  rw [this, PowerSeries.truncTotal_subst, Phi_truncTotal, eq_aux]
  conv_rhs => rw [truncTotal_subst_eq_truncTotal_left
    (PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)), Phi_truncTotal]

-/

lemma truncTotal_subst_aux {G : MvPowerSeries σ 𝒪[K]} (k : ℕ) (hG : G.constantCoeff = 0) :
    ((f.toPowerSeries.subst G).truncTotal (k.succ + 1)).toMvPowerSeries =
      ((f.toPowerSeries.subst (G.truncTotal k.succ).toMvPowerSeries).truncTotal
        (k.succ + 1)).toMvPowerSeries + C π.val * G.homogeneousComponent k.succ := by
  rw [PowerSeries.truncTotal_subst, truncTotal_succ_eq G, truncTotal_succ_eq,
    PowerSeries.homogeneous_subst_add (constanceCoeff_F π) _ , PowerSeries.truncTotal_subst, map_add,
      truncTotal_homogeneous_same, _root_.add_zero, coeff_one_F, smul_eq_C_mul,
      ← _root_.add_assoc, add_left_inj]
  · conv_rhs => rw [truncTotal_succ_eq]
    congr! 4
    ext d
    simp [coeff_truncTotal_eq_ite]
    grind
  · simp [← coeff_zero_eq_constantCoeff_apply, ← MvPolynomial.constantCoeff_eq,
    constantCoeff_truncTotal_eq_ite, hG]

/- $G(g) = G_k(g) + π^{k+1} • Δ_{k+1} (mod deg (k+2))$. -/
lemma truncTotal_subst_aux₂ {G : MvPowerSeries σ 𝒪[K]} (k : ℕ) (hG : G.constantCoeff = 0):
    ((G.subst (fun x ↦ (PowerSeries.toMvPowerSeries x) g.toPowerSeries)).truncTotal
      (k.succ + 1)).toMvPowerSeries =
    (((G.truncTotal k.succ).toMvPowerSeries.subst (fun x ↦ (PowerSeries.toMvPowerSeries x)
      g.toPowerSeries)).truncTotal (k.succ + 1)).toMvPowerSeries +
      C (π.val ^ k.succ) * G.homogeneousComponent k.succ := by
  have hasSubst_aux : HasSubst fun (i : σ) ↦ (PowerSeries.toMvPowerSeries i) g.toPowerSeries :=
    hasSubst_of_constantCoeff_zero (PowerSeries.constantCoeff_toMvPowerSeries
      (constanceCoeff_F π) )
  rw [truncTotal_subst_eq_truncTotal_left
    (PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)),
      truncTotal_succ_eq G, subst_add hasSubst_aux, map_add, MvPolynomial.coe_add]
  nth_rw 3 [truncTotal_succ_eq]
  nth_rw 2 [truncTotal_subst_eq_truncTotal_left
    (PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)),
      ← substAlgHom_apply hasSubst_aux]
  rw [truncTotal_homogeneous_same, MvPolynomial.coe_zero, map_zero, map_zero, MvPolynomial.coe_zero,
    _root_.zero_add, add_right_inj, homogeneous_subst_eq_homogeneous _ _ hG, smul_eq_C_mul]

lemma constructive_lemma : f.toPowerSeries.subst (Phi f g a) =
    (Phi f g a).subst (g.toPowerSeries.toMvPowerSeries · ) := by
  have hasSubst_aux : HasSubst fun (x : σ) ↦ (PowerSeries.toMvPowerSeries x)
    g.toPowerSeries := hasSubst_of_constantCoeff_zero
      <| PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)
  have eq_aux {n : ℕ} : (f.toPowerSeries.subst (Phi_aux f g a n)).truncTotal (n + 1) =
    ((Phi_aux f g a n).subst (g.toPowerSeries.toMvPowerSeries · )).truncTotal (n + 1) := by
    induction n with
    | zero =>
      simp
      rw [← substAlgHom_apply hasSubst_aux, map_zero,
        PowerSeries.subst_zero_of_constantCoeff_zero (constanceCoeff_F π)]
    | succ n ih =>
      by_cases! hn : n = 0
      · simp [hn, constructive_lemma_base π f g a]
      have {s t : MvPolynomial σ 𝒪[K]} : s.toMvPowerSeries = t.toMvPowerSeries → s = t :=
        fun a ↦ MvPolynomial.ext s t (congrFun a)
      apply this
      rw [truncTotal_subst_aux, truncTotal_subst_aux₂, Phi_aux_truncTotal_succ]
      obtain h1 := eq_add_of_sub_eq' (pi_dvd_sub π f g (Phi_aux f g a n) hn).choose_spec
      have : C π.val * C (1 - π.val ^ n) (σ := σ) = C (π.val - (π.val ^ (n + 1))) := by
        rw [← map_mul]
        ring_nf
      rw [truncTotal_succ_eq, ih, truncTotal_succ_eq (n := n.succ), _root_.add_assoc,
        _root_.add_assoc, add_right_inj, h1, map_add, homogeneous_Phi_aux _ _ _ _ hn,
        _root_.add_assoc, add_right_inj, ]
      nth_rw 2 [this]
      conv_rhs => rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul, map_sub, sub_mul]
      ring
      · exact constantCoeff_Phi_aux π f g a
      · exact constantCoeff_Phi_aux π f g a
  apply eq_of_forall_truncTotal_eq.mpr
  intro n
  by_cases! hn : n = 0
  · simp [hn, truncTotal_zero]
  have : n = n - 1 + 1 := (Nat.succ_pred_eq_of_ne_zero hn).symm
  rw [this, PowerSeries.truncTotal_subst, Phi_truncTotal, eq_aux]
  conv_rhs => rw [truncTotal_subst_eq_truncTotal_left
    (PowerSeries.constantCoeff_toMvPowerSeries (constanceCoeff_F π)), Phi_truncTotal]

lemma contructive_lemma_unique_aux (k : ℕ) {G : MvPowerSeries σ 𝒪[K]} (hG : G.constantCoeff = 0)
    (h_subst : f.toPowerSeries.subst G = G.subst (g.toPowerSeries.toMvPowerSeries ·)) :
    (C π.val - C (π.val ^ (k + 1))) * G.homogeneousComponent (k + 1) =
      (((G.truncTotal k.succ).toMvPowerSeries.subst (fun x ↦ (PowerSeries.toMvPowerSeries x)
        g.toPowerSeries)).truncTotal (k.succ + 1)).toMvPowerSeries -
          ((f.toPowerSeries.subst (G.truncTotal k.succ).toMvPowerSeries).truncTotal
          (k.succ + 1)).toMvPowerSeries := by
  rw [sub_mul, ← sub_eq_of_eq_add' (truncTotal_subst_aux π f k hG),
    ← sub_eq_of_eq_add' (truncTotal_subst_aux₂ π g k hG), h_subst]
  ring

instance : IsDomain 𝒪[K] := inferInstance

instance : NoZeroDivisors (MvPowerSeries σ 𝒪[K]) := inferInstance

-- instance : IsDomain (MvPowerSeries σ 𝒪[K]) := sorry

omit [Finite σ] in
lemma cancel_C_mul {R : Type*} [CommRing R] [IsDomain R] {a : R} (ha : a ≠ 0)
  {F G : MvPowerSeries σ R}
    (h : C a * F = C a * G) : F = G := by
  have : C a * (F - G) = 0 := by
    rw [mul_sub, sub_eq_zero, h]
  have ha' : C a (σ := σ) ≠ 0 := by
    by_contra! hc
    have : a = 0 := by
      apply C_injective
      rw [hc, map_zero]
    contradiction
  exact sub_eq_zero.mp <|  eq_zero_of_ne_zero_of_mul_left_eq_zero ha' this

lemma contructive_lemma_unique {G : MvPowerSeries σ 𝒪[K]}
    (h_trunc : G.truncTotal 2 = (Phi f g a).truncTotal 2)
      (h_subst : f.toPowerSeries.subst G = G.subst (g.toPowerSeries.toMvPowerSeries ·)) :
    G = Phi f g a := by
  have {n : ℕ} : G.truncTotal (n + 1) = (Phi f g a).truncTotal (n + 1) := by
    induction n using Nat.caseStrongRecOn with
    | zero =>
      simp [truncTotal_degree_one, constantCoeff_eq_of_truncTotal_two_eq _ h_trunc]
    | ind n ih =>
      by_cases! hn : n = 0
      · simp [hn, h_trunc]
      have {s t : MvPolynomial σ 𝒪[K]} : s.toMvPowerSeries = t.toMvPowerSeries → s = t :=
        fun a ↦ MvPolynomial.ext s t (congrFun a)
      apply this
      rw [truncTotal_succ_eq, truncTotal_succ_eq (Phi f g a), ih _ (le_refl n), add_right_inj]
      have constantCoeff_G : G.constantCoeff = 0 := by
        simp [constantCoeff_eq_of_truncTotal_two_eq _ h_trunc, constantCoeff_Phi]
      obtain eq_aux₁ := contructive_lemma_unique_aux π f g n constantCoeff_G h_subst
      obtain eq_aux₂ := contructive_lemma_unique_aux π f g n (constantCoeff_Phi π f g a)
        (constructive_lemma π f g a)
      rw [ih _ (refl n), ← eq_aux₂, ← map_sub] at eq_aux₁
      have neZero_aux : π.val - π.val ^ (n + 1) ≠ 0 := by
        have : π.val - π.val ^ (n + 1) = π.val * (1 - π.val ^ n) := by ring
        simpa [this, sub_ne_zero.mpr (pi_pow_ne_one π hn).symm] using
          Subtype.coe_ne_coe.mp π.ne_zero
      exact cancel_C_mul neZero_aux eq_aux₁
  ext d : 1
  rw [← coeff_truncTotal _ (lt_add_one _), this, coeff_truncTotal _ (lt_add_one _)]


-- lemma constructive_lemma_ind_hyp
--     (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
--     (hϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
--     {a : Fin n → 𝒪[K]} (f g : 𝓕 π) (r : ℕ) (hr : 2 ≤ r) :
--     ∃! ϕr : MvPolynomial (Fin n) 𝒪[K], ϕr.totalDegree < r
--         ∧ truncTotal 2 ϕr = ϕ₁
--           ∧ truncTotal r (f.toPowerSeries.subst ϕr.toMvPowerSeries)
--             = truncTotal r (ϕr.toMvPowerSeries.subst (g.toPowerSeries.toMvPowerSeries ·)) := by
--   induction r, hr using Nat.le_induction with
--   | base => sorry
--   | succ d hd ih =>

--     sorry


-- theorem constructive_lemma
--     (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
--     (h_ϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
--     (f g : 𝓕 π) :
--     ∃! ϕ : MvPowerSeries (Fin n) 𝒪[K],
--       truncTotal 2 ϕ = ϕ₁
--         ∧ PowerSeries.subst ϕ f.toPowerSeries = subst (g.toPowerSeries.toMvPowerSeries ·) ϕ := by

--   sorry



-- variable [DecidableEq σ] [Fintype σ] [DecidableEq τ] [Fintype τ]

-- -- Proposition 2.11
-- lemma constructive_lemma_ind_hyp
--     (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
--     (hϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
--     {a : Fin n → 𝒪[K]} (f g : LubinTateF π) (r : ℕ) (hr : 2 ≤ r) :
--     ∃! ϕr : MvPolynomial (Fin n) 𝒪[K], ϕr.totalDegree < r
--         ∧ truncTotal _ 2 ϕr = ϕ₁
--           ∧ truncTotal _ r (f.toPowerSeries.subst ϕr.toMvPowerSeries)
--             = truncTotal _ r (ϕr.toMvPowerSeries.subst (g.toPowerSeries.toMvPowerSeries ·)) := by
--   induction r, hr using Nat.le_induction with
--   | base => sorry
--   | succ d hd ih =>
--     obtain ⟨p, ⟨hp_deg, hp_trunc, hp_comm⟩, hp_unique⟩ := ih
--     simp only at hp_unique

--     -- f(X) = X^q mod π
--     have h₁ := f.toMvPowerSeries_mod_pi
--     -- f(X) = πX + ...
--     -- have h₂ := f.trunc_degree_two
--     -- wts: f ∘ p = p(x1, ..., xn)^q mod π
--     sorry
--     -- have hϕ₁_constantCoeff : ϕ₁.constantCoeff = 0 := by
--     --   contrapose! hϕ₁
--     --   use 0, ?_, by simp
--     --   simpa using hϕ₁
--     -- have hp_constantCoeff : p.constantCoeff = 0 := by
--     --   apply_fun MvPolynomial.coeff 0 at hp_trunc
--     --   rw [truncTotalDegHom_apply, coeff_truncTotalDeg_of_totalDeg_lt _ _ (by simp)] at hp_trunc
--     --   convert hp_trunc
--     --   exact hϕ₁_constantCoeff.symm
--     -- have hp_hasSubst : PowerSeries.HasSubst p.toMvPowerSeries := by
--     --   simpa using hp_constantCoeff
--     -- -- construction: (f ∘ p - p ∘ g) / (π^r - 1)π
--     -- have h_first_term : C π ∣ ((PowerSeries.substAlgHom hp_hasSubst) f.toPowerSeries - p.toMvPowerSeries ^ Fintype.card 𝓀[K]) := by
--     --   -- f(X) - X^q = π * u(X)
--     --   -- show f(p(x1, ..., xn)) - p(x1, ..., xn)^q = π * u(p(x1, ..., xn))
--     --   obtain ⟨u, hu⟩ := f.mod_pi
--     --   use (PowerSeries.substAlgHom hp_hasSubst) u
--     --   convert congrArg (PowerSeries.substAlgHom hp_hasSubst) hu
--     --   · rw [map_sub, map_pow, PowerSeries.substAlgHom_X]
--     --   · -- TODO: Add this (subst_C) to mathlib
--     --     rw [map_mul, ← Polynomial.coe_C, PowerSeries.substAlgHom_coe, Polynomial.aeval_C]
--     --     rfl
--     -- -- show p(g(x)) = p(x1^q, ..., xn^q) mod π
--     -- have h_second_term_inner {d : ℕ} (i : Fin d) : C π ∣ g.toPowerSeries.toMvPowerSeries i - X i ^ Fintype.card 𝓀[K] := by
--     --   obtain ⟨u, hu⟩ := g.mod_pi
--     --   use (PowerSeries.substAlgHom (PowerSeries.HasSubst.X i)) u
--     --   convert congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := 𝒪[K]) i)) hu
--     --   · rw [map_sub, map_pow, PowerSeries.substAlgHom_X, PowerSeries.toMvPowerSeries_apply,
--     --       PowerSeries.subst, PowerSeries.substAlgHom, substAlgHom_apply]
--     --   · rw [map_mul, ← Polynomial.coe_C, PowerSeries.substAlgHom_coe, Polynomial.aeval_C]
--     --     rfl
--     -- have h_second_term : C π ∣ p.toMvPowerSeries.subst (g.toPowerSeries.toMvPowerSeries · ) - p.toMvPowerSeries.subst (X · ^ Fintype.card 𝓀[K]) := by
--     --   -- p is a polynomial so we may use MvPolynomial
--     --   rw [subst_coe, subst_coe]
--     --   -- this means we can write stuff like p.sum!
--     --   -- In fact, p(g1(x),g2(x),...)-p(h1(x),h2(x),...) = sum(p_I (g(x)^I-h(x)^I))
--     --   rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.aeval_def,
--     --     MvPolynomial.eval₂_eq, ← Finset.sum_sub_distrib]
--     --   apply Finset.dvd_sum fun i hi ↦ ?_
--     --   simp_rw [← mul_sub]
--     --   apply dvd_mul_of_dvd_right
--     --   apply dvd_prod_pow_sub_prod_pow_of_dvd_sub h_second_term_inner
--     -- have h_diff_terms : C π ∣ p.toMvPowerSeries ^ Fintype.card 𝓀[K] - p.toMvPowerSeries.subst (X · ^ Fintype.card 𝓀[K]) := by
--     --   sorry
--     -- sorry
--     -- --   sorry
--     -- -- hav_mv : (C _ _) π ∣ f.toPowerSeries.subst p.toMvPowerSeries - p.toMvPowerSeries ^ residue_size K := by
--     -- --   sorry

--     -- -- have h₁ : (sMvPolynomial.C (Fin n) 𝒪[K]) π ∣ f.toPowerSeries.subst p.toMvPowerSeries - p.toMvPowerSeries.subst g.toPowerSeries.toMvPowerSeries

-- -- Proposition 2.11
-- theorem constructive_lemma
--     (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
--     (h_ϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
--     (f g : LubinTateF π) :
--     ∃! ϕ : MvPowerSeries (Fin n) 𝒪[K],
--       truncTotal _ 2 ϕ = ϕ₁
--         ∧ PowerSeries.subst ϕ f.toPowerSeries = subst (g.toPowerSeries.toMvPowerSeries ·) ϕ := by
--   sorry

-- /-- This is constructive lemma in two variable. More specific, given two `f, g ∈ F_π`,
--   then there exist unique `ϕ ∈ 𝒪[K]⟦X,Y⟧`, such that `ϕ ≡ X + Y mod (deg 2)` and
--   `g (ϕ (X, Y)) = ϕ (f(X), f(Y))`. -/
-- theorem constructive_lemma_two
--     (f g : LubinTateF π) :
--     ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), (truncTotalDegHom 2 ϕ)
--     = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) ∧
--     PowerSeries.subst ϕ g.toPowerSeries = subst (f.toPowerSeries.toMvPowerSeries · ) ϕ := by
--   let a := fun (x : Fin 2) => 1

--   sorry

-- /-- This is constructive lemma in two variable. More specific, given two `f, g ∈ F_π`,
--   then there exist unique `ϕ ∈ 𝒪[K]⟦X,Y⟧`, such that `ϕ ≡ X + Y mod (deg 2)` and
--   `g (ϕ (X, Y)) = ϕ (f(X), f(Y))`. -/
-- theorem constructive_lemma_two'
--     (f g : LubinTateF π) (a : 𝒪[K]):
--     ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), (truncTotalDegHom 2 ϕ)
--     = MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) + MvPolynomial.C a * MvPolynomial.X (1 : Fin 2) ∧
--     PowerSeries.subst ϕ g.toPowerSeries = subst (f.toPowerSeries.toMvPowerSeries · ) ϕ := by
--   let a := fun (x : Fin 2) => 1

--   sorry



-- end MvPowerSeries

-- end Prop_2_11

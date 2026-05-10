module

public import FormalGroupLaws.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

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

-- variable {k : ℕ} [NeZero k] in
-- #check  ⅟(1 - π.val ^ k)

instance [Finite σ] : Fintype σ := Fintype.ofFinite σ

open Finset Fintype Finsupp

variable [Finite σ] (f g : 𝓕 π) (a : σ →₀ 𝒪[K])
  -- {L : MvPolynomial σ 𝒪[K]}
  -- (hL : ∀ i ∈ L.support, Finset.univ.sum i = 1)

abbrev L : MvPolynomial σ 𝒪[K] := MvPolynomial.sumSMulX a

def Ideal_aux : Ideal (MvPowerSeries σ 𝒪[K]) := 𝓂[K].map C

lemma qK_neZero : q ≠ 0 := card_ne_zero

example {i : σ} : C π.val * X i ∈ 𝓂[K].map C := by
  have : C π.val (σ := σ) ∈ C '' 𝓂[K] :=
    (Set.mem_image C 𝓂[K] (C π.val)).mpr ⟨π, π.valuation_gt_one.not_isUnit, rfl⟩
  exact Ideal.IsTwoSided.mul_mem_of_left (X i) (Submodule.mem_span_of_mem this)

lemma frob_eq {f : MvPowerSeries σ 𝒪[K]} :
    f ^ q ≡ f.expand q card_ne_zero [SMOD 𝓂[K].map C] := sorry

lemma pi_dvd_sub (F : MvPowerSeries σ 𝒪[K]) {n : ℕ} (hn : n ≠ 0) :
    C π.val * C (1 - π.val ^ n) ∣ F.subst (g.toPowerSeries.toMvPowerSeries · ) -
      f.toPowerSeries.subst F := by
  haveI : NeZero n := { out := hn }
  have : C π.val * C (1 - π.val ^ n) * C (⅟(1 - π.val ^ n)) ∣
      F.subst (g.toPowerSeries.toMvPowerSeries · ) - f.toPowerSeries.subst F := by
    rw [mul_assoc, ← map_mul, Invertible.mul_invOf_self, map_one, mul_one]

    sorry
  exact dvd_of_mul_right_dvd this

-- variable (π f g) in
def Phi_aux : ℕ → MvPowerSeries σ 𝒪[K]
  | 0 => 0
  -- | 1 => L a
  | n + 1 =>
    if h : n = 0 then L a else
    -- have : C π.val * C (1 - π.val ^ n) ∣ (Phi_aux n).subst (g.toPowerSeries.toMvPowerSeries · ) -
    --   f.toPowerSeries.subst (Phi_aux n) := pi_dvd_sub π f g (Phi_aux n) h
    Phi_aux n + homogeneousComponent (n + 1) (pi_dvd_sub π f g (Phi_aux n) h).choose

section

-- omit [Finite σ]

@[simp]
lemma Phi_aux_zero : Phi_aux π f g a 0 = 0 := rfl

@[simp]
lemma Phi_aux_one : Phi_aux π f g a 1 = L a := rfl

/-- This is a unique solution in the constructive lemma. -/
def Phi : MvPowerSeries σ 𝒪[K] := fun d => (Phi_aux π f g a d.degree).coeff d

@[simp]
lemma coeff_Phi {d : σ →₀ ℕ} : (Phi π f g a).coeff d = (Phi_aux π f g a d.degree).coeff d := rfl

end

lemma Phi_truncTotal_one : (Phi π f g a).truncTotal 1 = 0 := sorry

lemma Phi_truncTotal_two : (Phi π f g a).truncTotal 2 = L a := by
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
    (Phi π f g a).truncTotal (n + 1) = Phi_aux π f g a n := by
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

/-- For any multivariate power series F, F is homogeneous of degree k, then
  $F(g(X_1, …, X_n)) ≡ π^k F(X_1, …, X_n)$. -/
lemma homogeneous_comp {k : ℕ} {F : MvPowerSeries σ 𝒪[K]} (hF : F.constantCoeff = 0)
    (hF₁ : F.IsHomogeneous k) :
    truncTotal (k + 1) (F.subst (g.toPowerSeries.toMvPowerSeries ·)) = π.val ^ k • F := by
  /- use the truncTotal_subst lemma in the PR. -/
  sorry

lemma constructive_lemma : f.toPowerSeries.subst (Phi π f g a) =
    (Phi π f g a).subst (g.toPowerSeries.toMvPowerSeries · ) := by

  sorry

lemma contructive_lemma_unique {G : MvPowerSeries σ 𝒪[K]}
    (h_trunc : (Phi π f g a).truncTotal 2 = G.truncTotal 2)
      (h_subst : f.toPowerSeries.subst G = G.subst (g.toPowerSeries.toMvPowerSeries ·)) :
    G = Phi π f g a := sorry

lemma constructive_lemma_ind_hyp
    (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
    (hϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
    {a : Fin n → 𝒪[K]} (f g : 𝓕 π) (r : ℕ) (hr : 2 ≤ r) :
    ∃! ϕr : MvPolynomial (Fin n) 𝒪[K], ϕr.totalDegree < r
        ∧ truncTotal 2 ϕr = ϕ₁
          ∧ truncTotal r (f.toPowerSeries.subst ϕr.toMvPowerSeries)
            = truncTotal r (ϕr.toMvPowerSeries.subst (g.toPowerSeries.toMvPowerSeries ·)) := by
  induction r, hr using Nat.le_induction with
  | base => sorry
  | succ d hd ih =>

    sorry


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

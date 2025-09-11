import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import FormalGroupLaws.Basic
import FormalGroupLaws.Trunc
import FormalGroupLaws.MvPowerSeries.TruncTotalDeg


open ValuativeRel MvPowerSeries Classical

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [UniformSpace K]
  (π : 𝒪[K]) {R : Type*} [CommRing R]

variable (K) in
class IsNonArchLF : Prop extends
  IsTopologicalDivisionRing K,
  LocallyCompactSpace K,
  CompleteSpace K,
  IsValuativeTopology K,
  ValuativeRel.IsNontrivial K,
  ValuativeRel.IsRankLeOne K,
  ValuativeRel.IsDiscrete K

variable [IsNonArchLF K]

instance : IsUniformAddGroup K where
  uniformContinuous_sub := sorry

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

noncomputable instance : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne where
  hom := IsRankLeOne.nonempty.some.emb
  strictMono' := IsRankLeOne.nonempty.some.strictMono

open scoped Valued in
instance : ProperSpace K :=
  ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

instance : IsDiscreteValuationRing 𝒪[K] :=
  (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp inferInstance).2.1


section LubinTateF

variable (π : 𝒪[K])

instance : Finite 𝓀[K] := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp inferInstance).2.2
noncomputable instance : Fintype 𝓀[K] := Fintype.ofFinite _

structure LubinTateF where
  toFun : PowerSeries 𝒪[K]
  trunc_degree_two : PowerSeries.trunc 2 toFun = Polynomial.C π * Polynomial.X
  mod_pi : PowerSeries.C _ π ∣ toFun - PowerSeries.X ^ Fintype.card 𝓀[K]

namespace LubinTateF

variable (F : LubinTateF π)

lemma toMvPowerSeries_trunc_degree_two :
    (F.toFun : MvPowerSeries Unit 𝒪[K]).truncTotalDeg 2
      = MvPolynomial.C π * MvPolynomial.X default := by
  rw [truncTotalDeg_powerSeries, (MvPolynomial.pUnitAlgEquiv _).symm_apply_eq]
  simpa using F.trunc_degree_two

lemma toMvPowerSeries_mod_pi :
    MvPowerSeries.C _ _ π ∣ F.toFun - MvPowerSeries.X default ^ Fintype.card 𝓀[K] :=
  F.mod_pi

/-- constant coefficient of `f` in Lubin Tate `F_π` is zero.-/
lemma constantCoeff_LubinTateF : PowerSeries.constantCoeff _ F.toFun = 0 := by
  sorry


end LubinTateF

end LubinTateF

noncomputable section

variable {σ : Type*} {R : Type*} [CommRing R] {τ : Type*}

section Prop_2_11

namespace MvPowerSeries

lemma C_dvd_iff_forall_dvd_coeff (c : R) (p : MvPowerSeries σ R) :
    (C _ _) c ∣ p ↔ ∀ n, c ∣ (coeff R n) p := by
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
    rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_add_index_of_disjoint,
      Finsupp.prod_single_index, Finsupp.prod_single_index]
    · obtain ⟨q, hq⟩ := ih
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

variable [DecidableEq σ] [Fintype σ] [DecidableEq τ] [Fintype τ]

-- Proposition 2.11
lemma constructive_lemma_ind_hyp
    (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
    (hϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
    {a : Fin n → 𝒪[K]} (f g : LubinTateF π) (r : ℕ) (hr : 2 ≤ r) : ∃! ϕr : MvPolynomial (Fin n) 𝒪[K], ϕr.totalDegree < r
        ∧ truncTotalDegHom 2 ϕr = ϕ₁
          ∧ truncTotalDegHom r (f.toFun.subst ϕr.toMvPowerSeries)
            = truncTotalDegHom r (ϕr.toMvPowerSeries.subst g.toFun.toMvPowerSeries) := by
  induction r, hr using Nat.le_induction with
  | base => sorry
  | succ d hd ih =>
    obtain ⟨p, ⟨hp_deg, hp_trunc, hp_comm⟩, hp_unique⟩ := ih
    simp only at hp_unique

    -- f(X) = X^q mod π
    have h₁ := f.toMvPowerSeries_mod_pi
    -- f(X) = πX + ...
    -- have h₂ := f.trunc_degree_two
    -- wts: f ∘ p = p(x1, ..., xn)^q mod π
    have hϕ₁_constantCoeff : ϕ₁.constantCoeff = 0 := by
      contrapose! hϕ₁
      use 0, ?_, by simp
      simpa using hϕ₁
    have hp_constantCoeff : p.constantCoeff = 0 := by
      apply_fun MvPolynomial.coeff 0 at hp_trunc
      rw [truncTotalDegHom_apply, coeff_truncTotalDeg_of_totalDeg_lt _ _ (by simp)] at hp_trunc
      convert hp_trunc
      exact hϕ₁_constantCoeff.symm
    have hp_hasSubst : PowerSeries.HasSubst p.toMvPowerSeries := by
      simpa using hp_constantCoeff
    -- construction: (f ∘ p - p ∘ g) / (π^r - 1)π
    have h_first_term : (C _ _) π ∣ ((PowerSeries.substAlgHom hp_hasSubst) f.toFun - p.toMvPowerSeries ^ Fintype.card 𝓀[K]) := by
      -- f(X) - X^q = π * u(X)
      -- show f(p(x1, ..., xn)) - p(x1, ..., xn)^q = π * u(p(x1, ..., xn))
      obtain ⟨u, hu⟩ := f.mod_pi
      use (PowerSeries.substAlgHom hp_hasSubst) u
      convert congrArg (PowerSeries.substAlgHom hp_hasSubst) hu
      · rw [map_sub, map_pow, PowerSeries.substAlgHom_X]
      · -- TODO: Add this (subst_C) to mathlib
        rw [map_mul, ← Polynomial.coe_C, PowerSeries.substAlgHom_coe, Polynomial.aeval_C]
        rfl
    -- show p(g(x)) = p(x1^q, ..., xn^q) mod π
    have h_second_term_inner {d : ℕ} (i : Fin d) : (C _ _) π ∣ g.toFun.toMvPowerSeries i - X i ^ Fintype.card 𝓀[K] := by
      obtain ⟨u, hu⟩ := g.mod_pi
      use (PowerSeries.substAlgHom (PowerSeries.HasSubst.X i)) u
      convert congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := 𝒪[K]) i)) hu
      · rw [map_sub, map_pow, PowerSeries.substAlgHom_X, PowerSeries.toMvPowerSeries,
          PowerSeries.subst, PowerSeries.substAlgHom, substAlgHom_apply]
      · rw [map_mul, ← Polynomial.coe_C, PowerSeries.substAlgHom_coe, Polynomial.aeval_C]
        rfl
    have h_second_term : (C _ _) π ∣ p.toMvPowerSeries.subst g.toFun.toMvPowerSeries - p.toMvPowerSeries.subst (X · ^ Fintype.card 𝓀[K]) := by
      -- p is a polynomial so we may use MvPolynomial
      rw [subst_coe, subst_coe]
      -- this means we can write stuff like p.sum!
      -- In fact, p(g1(x),g2(x),...)-p(h1(x),h2(x),...) = sum(p_I (g(x)^I-h(x)^I))
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.aeval_def,
        MvPolynomial.eval₂_eq, ← Finset.sum_sub_distrib]
      apply Finset.dvd_sum fun i hi ↦ ?_
      simp_rw [← mul_sub]
      apply dvd_mul_of_dvd_right
      apply dvd_prod_pow_sub_prod_pow_of_dvd_sub h_second_term_inner
    have h_diff_terms : (C _ _) π ∣ p.toMvPowerSeries ^ Fintype.card 𝓀[K] - p.toMvPowerSeries.subst (X · ^ Fintype.card 𝓀[K]) := by
      sorry
    sorry
    --   sorry
    -- hav_mv : (C _ _) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries ^ residue_size K := by
    --   sorry

    -- have h₁ : (sMvPolynomial.C (Fin n) 𝒪[K]) π ∣ f.toFun.subst p.toMvPowerSeries - p.toMvPowerSeries.subst g.toFun.toMvPowerSeries

-- Proposition 2.11
theorem constructive_lemma
    (n : ℕ) {ϕ₁ : MvPolynomial (Fin n) 𝒪[K]}
    (h_ϕ₁ : ∀ i ∈ ϕ₁.support, Finset.univ.sum i = 1)
    (f g : LubinTateF π) :
    ∃! ϕ : MvPowerSeries (Fin n) 𝒪[K],
      truncTotalDegHom 2 ϕ = ϕ₁
        ∧ PowerSeries.subst ϕ f.toFun = subst g.toFun.toMvPowerSeries ϕ := by
  sorry

/-- This is constructive lemma in two variable. More specific, given two `f, g ∈ F_π`,
  then there exist unique `ϕ ∈ 𝒪[K]⟦X,Y⟧`, such that `ϕ ≡ X + Y mod (deg 2)` and
  `g (ϕ (X, Y)) = ϕ (f(X), f(Y))`. -/
theorem constructive_lemma_two
    (f g : LubinTateF π) :
    ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), (truncTotalDegHom 2 ϕ)
    = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) ∧
    PowerSeries.subst ϕ g.toFun = subst f.toFun.toMvPowerSeries ϕ := by
  let a := fun (x : Fin 2) => 1

  sorry

/-- This is constructive lemma in two variable. More specific, given two `f, g ∈ F_π`,
  then there exist unique `ϕ ∈ 𝒪[K]⟦X,Y⟧`, such that `ϕ ≡ X + Y mod (deg 2)` and
  `g (ϕ (X, Y)) = ϕ (f(X), f(Y))`. -/
theorem constructive_lemma_two'
    (f g : LubinTateF π) (a : 𝒪[K]):
    ∃! (ϕ : MvPowerSeries (Fin 2) 𝒪[K]), (truncTotalDegHom 2 ϕ)
    = MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) + MvPolynomial.C a * MvPolynomial.X (1 : Fin 2) ∧
    PowerSeries.subst ϕ g.toFun = subst f.toFun.toMvPowerSeries ϕ := by
  let a := fun (x : Fin 2) => 1

  sorry



end MvPowerSeries

end Prop_2_11

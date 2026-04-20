import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic

universe u

open ValuativeRel Classical Valuation

-- /-- The value group of the canonical valuation on a field is the full group of units,
-- since the valuation is surjective. -/
-- lemma valueGroup_valuation_eq_top {K : Type u} [Field K] [ValuativeRel K] :
--     MonoidWithZeroHom.valueGroup (valuation K) = ⊤ := by
--   rw [eq_top_iff]
--   intro x _
--   exact MonoidWithZeroHom.mem_valueGroup _ (valuation_surjective _)

variable {K : Type u} [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

/-- The units of the value group of a nonarchimedean local field are cyclic,
since the value group is order-isomorphic to `ℤᵐ⁰`. -/
instance : IsCyclic (ValueGroupWithZero K)ˣ :=
  (Units.mapEquiv
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMulEquiv).isCyclic.mpr
    inferInstance

/-- The units of the value group of a nonarchimedean local field are nontrivial,
since the valuative relation is nontrivial. -/
instance : Nontrivial (ValueGroupWithZero K)ˣ :=
  ValuativeRel.isNontrivial_iff_nontrivial_units.mp inferInstance

/-- The canonical valuation on a nonarchimedean local field is rank one discrete.
This follows because the value group is isomorphic to `ℤᵐ⁰`, making the value group
of the valuation cyclic and nontrivial. -/
instance : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).IsRankOneDiscrete :=
  inferInstance

-- lemma aux {π : 𝒪[K]} (h : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).IsUniformizer π) :

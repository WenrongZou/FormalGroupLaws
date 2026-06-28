module

public import FormalGroupLaws.AddInverse
public import Mathlib.NumberTheory.LocalField.Basic

variable {R σ : Type*} [CommRing R] {F : FormalGroup R} {x y z : F.Point σ}

name_power_vars X, Y, Z over R

example [F.IsComm] : x + y + z = y + (x + z) := by
  abel

open ValuativeRel in
/-- For any commutative ring `K` carrying a valuative relation whose topology is valuative,
the topology on the ring of integers `𝒪[K]` is linear, with the `Valuation.ltIdeal` open balls
as a basis of `𝓝 0`. This generalizes the local-field case to arbitrary valuative rings. -/
instance {K : Type*} [CommRing K] [ValuativeRel K]
    [TopologicalSpace K] [IsValuativeTopology K] : IsLinearTopology 𝒪[K] 𝒪[K] := by
  refine IsLinearTopology.mk_of_hasBasis 𝒪[K]
    (p := fun _ : (ValueGroupWithZero K)ˣ ↦ True) (s := Valuation.ltIdeal (valuation K)) ?_
  rw [nhds_subtype_eq_comap]
  exact (IsValuativeTopology.hasBasis_nhds_zero K).comap _

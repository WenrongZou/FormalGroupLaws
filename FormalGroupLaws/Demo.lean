module

public import FormalGroupLaws.AddInverse
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Extension

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

open ValuativeRel in
/-- A `ValuativeExtension K L` makes the canonical valuation on `L` an extension (in the sense of
`Valuation.HasExtension`) of the one on `K`: both `valuation K` and the comap of `valuation L`
along `algebraMap K L` are compatible with `K`'s valuative relation, hence equivalent. This bridges
the relation-based (`ValuativeRel`) and valuation-based (`HasExtension`) frameworks, so that
Mathlib's `Algebra 𝒪[K] 𝒪[L]` instance (`Valuation.HasExtension.instAlgebraInteger`) applies. -/
instance {K L : Type*} [CommRing K] [CommRing L]
    [ValuativeRel K] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] :
    (valuation K).HasExtension (valuation L) where
  val_isEquiv_comap :=
    haveI := ValuativeExtension.compatible_comap K (valuation L)
    ValuativeRel.isEquiv (valuation K) ((valuation L).comap (algebraMap K L))

open ValuativeRel in
/-- For a valuative extension `L / K`, the (subspace) topology on `𝒪[L]` is `𝒪[K]`-linear:
the `Valuation.ltIdeal` balls of `L` form a basis of `𝓝 0` made of `𝒪[K]`-submodules.
The `Algebra 𝒪[K] 𝒪[L]` (hence `Module`) structure is the one from `Valuation.HasExtension`.
Taking `L = K` recovers the instance above. -/
instance {K L : Type*} [CommRing K] [CommRing L]
    [ValuativeRel K] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
    [TopologicalSpace L] [IsValuativeTopology L] : IsLinearTopology 𝒪[K] 𝒪[L] := by
  refine IsLinearTopology.mk_of_hasBasis' (R := 𝒪[K]) (S := Ideal 𝒪[L])
    (p := fun _ : (ValueGroupWithZero L)ˣ ↦ True)
    (s := Valuation.ltIdeal (valuation L)) ?_ ?_
  · -- The `ltIdeal` balls of `L` give a basis of `𝓝 (0 : 𝒪[L])` by pulling back from `L`.
    rw [nhds_subtype_eq_comap]
    exact (IsValuativeTopology.hasBasis_nhds_zero L).comap _
  · -- Each `ltIdeal (valuation L) γ` is closed under `𝒪[K]`-scalar multiplication:
    -- `r • m = algebraMap 𝒪[K] 𝒪[L] r * m` lies in the ideal `I` because `m ∈ I`.
    intro I r m hm
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hm

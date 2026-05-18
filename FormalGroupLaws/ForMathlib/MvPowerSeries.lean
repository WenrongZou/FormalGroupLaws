module

public import FormalGroupLaws.MvPowerSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] {σ τ: Type*} [Algebra R S]

section

open MvPowerSeries

namespace MvPowerSeries


variable {p m n : ℕ} (hp : p ≠ 0) (φ : MvPowerSeries σ R)

lemma one_le_order {F : MvPowerSeries σ R} (hF : F.constantCoeff = 0) :
    1 ≤ F.order :=
  ENat.one_le_iff_ne_zero.mpr <| order_ne_zero_iff_constCoeff_eq_zero.mpr hF

lemma homogeneousComponent_eq_ite :
    (φ.homogeneousComponent n).homogeneousComponent m = if m = n then
      (φ.homogeneousComponent n) else 0 := by
  ext d
  grind [coeff_homogeneousComponent]

#check MvPowerSeries.map

omit [Algebra R S] in
theorem ker_map (f : R →+* S) :
    RingHom.ker (map f (σ := σ)) = Ideal.map C (RingHom.ker f) := by
  -- ext
  -- rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
  -- simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]
  sorry

end MvPowerSeries

end

section

open PowerSeries
open scoped WithPiTopology

variable {p : ℕ} (hp : p ≠ 0) (φ : PowerSeries R)

lemma PowerSeries.one_le_order {f : PowerSeries R} (hf : f.constantCoeff = 0) : 1 ≤ f.order :=
  ENat.one_le_iff_ne_zero.mpr <| order_ne_zero_iff_constCoeff_eq_zero.mpr hf

theorem PowerSeries.expand_eq_expand :
    MvPowerSeries.expand p hp φ = PowerSeries.expand p hp φ := rfl

lemma PowerSeries.expand_tsum [UniformSpace R] [T2Space R] [DiscreteUniformity R]
    {x : ℕ → PowerSeries R} (hx : Summable x):
    expand p hp (∑' i, x i) = ∑' i, (x i).expand p hp := by
  simp_rw [expand_apply]
  rw [tsum_subst hx (HasSubst.X_pow hp)]

end

section

namespace FiniteField

open Fintype

variable {K σ : Type*} [Field K] [Fintype K]

local notation "q" => Fintype.card K

lemma MvPowerSeries.expand_card {f : MvPowerSeries σ K} :
    f.expand q card_ne_zero = f ^ q := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  simp_rw [hn]
  rw [← MvPowerSeries.map_iterateFrobenius_expand _ (NeZero.ne' p).symm, iterateFrobenius_eq_pow,
    frobenius_pow hn, RingHom.one_def, MvPowerSeries.map_id, RingHom.id_apply]

end FiniteField

end

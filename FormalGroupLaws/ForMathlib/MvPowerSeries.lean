import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

variable {R S : Type*} [CommRing R] [CommRing S] {σ τ: Type*} [Finite σ] [Finite τ]

section

open MvPowerSeries
open scoped WithPiTopology

variable {p : ℕ} (hp : p ≠ 0) (φ : MvPowerSeries σ R)

lemma MvPowerSeries.one_le_order {F : MvPowerSeries σ R} (hF : F.constantCoeff = 0) :
    1 ≤ F.order := sorry

theorem MvPowerSeries.constantCoeff_expand :
    (φ.expand p hp).constantCoeff = φ.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
  simp

theorem MvPowerSeries.order_expand : (φ.expand p hp).order = p • φ.order := by
  by_cases! hφ : φ = 0
  · simp [hφ]
    exact(ENat.mul_top (by norm_cast)).symm
  · sorry

omit [Finite σ] in
theorem MvPowerSeries.expand_subst {f : σ → MvPowerSeries τ R} (hf : HasSubst f)
    {φ : MvPowerSeries σ R} :
    expand p hp (subst f φ) = subst (fun i ↦ (f i).expand p hp) φ := by
  rw [← substAlgHom_apply hf, expand_substAlgHom, substAlgHom_apply]

theorem MvPowerSeries.constantCoeff_pow_zero (hφ : φ.constantCoeff = 0) {n : ℕ} (hn : n ≠ 0) :
    (φ ^ n).constantCoeff = 0 := by
  rw [map_pow]
  sorry

theorem MvPowerSeries.le_order_pow_n (hφ : φ.constantCoeff = 0) {n : ℕ} :
    n ≤ (φ ^ n).order := sorry

end

section

open PowerSeries
open scoped WithPiTopology

variable {p : ℕ} (hp : p ≠ 0) (φ : PowerSeries R)

lemma PowerSeries.one_le_order {f : PowerSeries R} (hf : f.constantCoeff = 0) : 1 ≤ f.order := by
  sorry

theorem PowerSeries.order_expand : (φ.expand p hp).order = p • φ.order := by
  by_cases! hφ : φ = 0
  · simp [hφ]
    exact(ENat.mul_top (by norm_cast)).symm
  · sorry

theorem PowerSeries.constantCoeff_expand : (φ.expand p hp).constantCoeff = φ.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← mul_zero p, coeff_expand_mul]
  simp

theorem PowerSeries.expand_subst {f : MvPowerSeries τ S} (hf : HasSubst f) (φ : PowerSeries S) :
    (subst f φ).expand p hp = subst (f.expand p hp) φ := by
  have : MvPowerSeries.HasSubst (fun (x : Unit) ↦ f) := by
    exact HasSubst.const hf
  rw [PowerSeries.subst, MvPowerSeries.expand_subst hp this (φ := φ)]
  rfl

theorem PowerSeries.le_order_pow_n (hφ : φ.constantCoeff = 0) {n : ℕ} :
    n ≤ PowerSeries.order (φ ^ n) := by
  refine .trans ?_ (le_order_pow _ n)
  obtain h := one_le_order hφ
  simp
  exact le_mul_of_one_le_right' h

theorem PowerSeries.expand_eq_expand :
    MvPowerSeries.expand p hp φ = PowerSeries.expand p hp φ := sorry

lemma PowerSeries.expand_smul (a : R):
    expand p hp (a • φ) = a • φ.expand p hp := by sorry

theorem PowerSeries.coeff_expand {f : PowerSeries R} {n : ℕ} :
    (f.expand p hp).coeff n = if p ∣ n then f.coeff (n / p) else 0 := sorry

lemma PowerSeries.expand_tsum [UniformSpace R] [T2Space R] [DiscreteUniformity R]
    {x : ℕ → PowerSeries R} (hx : Summable x):
    expand p hp (∑' i, x i) = ∑' i, (x i).expand p hp := by sorry

omit [Finite σ] in
theorem PowerSeries.subst_sub {a : MvPowerSeries σ R} (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f - g) = subst a f - subst a g := by
  rw [← coe_substAlgHom ha, map_sub]
end

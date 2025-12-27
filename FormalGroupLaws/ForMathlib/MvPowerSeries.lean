import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Expand

variable {R S : Type*} [CommRing R] [CommRing S] {σ τ: Type*} [Finite σ] [Finite τ]

section

variable {p : ℕ} (hp : p ≠ 0) (φ : MvPowerSeries σ R)

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
theorem MvPowerSeries.expand_subst {f : σ → MvPowerSeries τ S} (hf : HasSubst f)
    {φ : MvPowerSeries σ S} :
    expand p hp (subst f φ) = subst (fun i ↦ (f i).expand p hp) φ := by
  rw [← substAlgHom_apply hf, expand_substAlgHom, substAlgHom_apply]

end

section

variable {p : ℕ} (hp : p ≠ 0) (φ : PowerSeries R)

theorem PowerSeries.order_expand : (φ.expand p hp).order = p • φ.order := by
  by_cases! hφ : φ = 0
  · simp [hφ]
    exact(ENat.mul_top (by norm_cast)).symm
  · sorry

theorem PowerSeries.coeff_expand {f : PowerSeries R} {n : ℕ} :
    (f.expand p hp).coeff n = if p ∣ n then f.coeff (n / p) else 0 := sorry

end

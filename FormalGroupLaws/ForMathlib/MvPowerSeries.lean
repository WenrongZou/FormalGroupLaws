import Mathlib.RingTheory.MvPowerSeries.Expand

variable {R S : Type*} [CommRing R] [CommRing S] {σ τ: Type*} [Finite σ] [Finite τ]

section

variable{p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries σ R)

theorem MvPowerSeries.constantCoeff_expand :
    (f.expand p hp).constantCoeff = f.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
  simp

theorem MvPowerSeries.order_expand : (f.expand p hp).order = p • f.order := by
  by_cases! hf : f = 0
  · simp [hf]
    exact(ENat.mul_top (by norm_cast)).symm
  ·sorry

omit [Finite σ] in
theorem MvPowerSeries.expand_subst {f : σ → MvPowerSeries τ S} (hf : HasSubst f)
    {φ : MvPowerSeries σ S} :
    expand p hp (subst f φ) = subst (fun i ↦ (f i).expand p hp) φ := by
  rw [← substAlgHom_apply hf, expand_substAlgHom, substAlgHom_apply]

end

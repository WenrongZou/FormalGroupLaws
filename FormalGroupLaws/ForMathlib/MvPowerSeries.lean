import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import FormalGroupLaws.MvPowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] {σ τ: Type*} [Finite σ] [Finite τ]

section

open MvPowerSeries
open scoped WithPiTopology

variable {p : ℕ} (hp : p ≠ 0) (φ : MvPowerSeries σ R)

omit [Finite σ] in
lemma MvPowerSeries.one_le_order {F : MvPowerSeries σ R} (hF : F.constantCoeff = 0) :
    1 ≤ F.order :=
  ENat.one_le_iff_ne_zero.mpr <| order_ne_zero_iff_constCoeff_eq_zero.mpr hF

-- theorem MvPowerSeries.constantCoeff_expand :
--     (φ.expand p hp).constantCoeff = φ.constantCoeff := by
--   conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
--   simp

-- theorem MvPowerSeries.order_expand : (φ.expand p hp).order = p • φ.order := by
--   by_cases! hφ : φ = 0
--   · simpa [hφ] using (ENat.mul_top (by norm_cast)).symm
--   · apply eq_of_le_of_ge
--     · obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order (ne_zero_iff_order_finite.mp hφ)
--       have : p • φ.order = (p • d).degree := by simp [← hd₂]
--       rw [this]
--       exact order_le <| (coeff_expand_smul p hp φ _) ▸ hd₁
--     · refine MvPowerSeries.le_order fun d hd => by
--         by_cases! h : ∀ i, p ∣ d i
--         · obtain ⟨m, hm⟩ : ∃ m, d = p • m :=
--             ⟨Finsupp.equivFunOnFinite.symm fun i => d i / p,
--               by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
--           rw [hm, coeff_expand_smul, coeff_of_lt_order]
--           simp only [hm, map_nsmul, smul_eq_mul, Nat.cast_mul, nsmul_eq_mul] at hd
--           exact lt_of_mul_lt_mul_left' hd
--         · obtain ⟨i, hi⟩ := h
--           exact coeff_expand_of_not_dvd p hp φ hi

-- omit [Finite σ] in
-- theorem MvPowerSeries.expand_subst {f : σ → MvPowerSeries τ R} (hf : HasSubst f)
--     {φ : MvPowerSeries σ R} :
--     expand p hp (subst f φ) = subst (fun i ↦ (f i).expand p hp) φ := by
--   rw [← substAlgHom_apply hf, expand_substAlgHom, substAlgHom_apply]

-- omit [Finite σ] in
-- theorem MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (hφ : φ.constantCoeff = 0) {n : ℕ} :
--     n ≤ (φ ^ n).order := by
--   refine .trans ?_ (MvPowerSeries.le_order_pow n)
--   rw [nsmul_eq_mul]
--   refine ENat.self_le_mul_right _ <| order_ne_zero_iff_constCoeff_eq_zero.mpr hφ


end

section

open PowerSeries
open scoped WithPiTopology

variable {p : ℕ} (hp : p ≠ 0) (φ : PowerSeries R)

lemma PowerSeries.one_le_order {f : PowerSeries R} (hf : f.constantCoeff = 0) : 1 ≤ f.order :=
  ENat.one_le_iff_ne_zero.mpr <| order_ne_zero_iff_constCoeff_eq_zero.mpr hf

-- theorem PowerSeries.coeff_expand {f : PowerSeries R} {n : ℕ} :
--     (f.expand p hp).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
--   split_ifs with h
--   · obtain ⟨q, hq⟩ := h
--     rw [hq, coeff_expand_mul, Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
--   exact coeff_expand_of_not_dvd p hp f h

-- theorem PowerSeries.order_expand : (φ.expand p hp).order = p • φ.order := by
--   by_cases! hφ : φ = 0
--   · simp [hφ]
--     exact(ENat.mul_top (by norm_cast)).symm
--   · apply eq_of_le_of_ge
--     · have : p • φ.order = (p * φ.order.toNat : ℕ) := by
--         rw [nsmul_eq_mul, Nat.cast_mul, coe_toNat_order hφ]
--       rw [this]
--       exact order_le _ <| (coeff_expand_mul p hp φ _) ▸ coeff_order hφ
--     · refine PowerSeries.le_order _ _ fun i hi => by
--         rw [coeff_expand]
--         split_ifs with h
--         · obtain ⟨q, hq⟩ := h
--           rw [hq, Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
--           simp only [hq, Nat.cast_mul, nsmul_eq_mul] at hi
--           exact coeff_of_lt_order q (lt_of_mul_lt_mul_left' hi)
--         rfl

-- theorem PowerSeries.constantCoeff_expand : (φ.expand p hp).constantCoeff = φ.constantCoeff := by
--   conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← mul_zero p, coeff_expand_mul]
--   simp

-- theorem PowerSeries.expand_subst {f : MvPowerSeries τ S} (hf : HasSubst f) (φ : PowerSeries S) :
--     (subst f φ).expand p hp = subst (f.expand p hp) φ := by
--   rw [PowerSeries.subst, MvPowerSeries.expand_subst hp (HasSubst.const hf) (φ := φ)]
--   rfl

-- theorem PowerSeries.le_order_pow_n (hφ : φ.constantCoeff = 0) {n : ℕ} :
--     n ≤ PowerSeries.order (φ ^ n) := by
--   refine .trans ?_ (le_order_pow _ n)
--   obtain h := one_le_order hφ
--   simpa using le_mul_of_one_le_right' h

-- omit [Finite σ]
-- lemma PowerSeries.le_order_subst_left {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
--     φ.order ≤ (φ.subst f).order  :=
--   .trans (ENat.self_le_mul_left φ.order (f.order_ne_zero_iff_constCoeff_eq_zero.mpr hf))
--     (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

-- lemma PowerSeries.le_order_subst_right {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0)
--     (hφ : φ.constantCoeff = 0) : f.order ≤ (φ.subst f).order  :=
--   .trans (ENat.self_le_mul_right _ (order_ne_zero_iff_constCoeff_eq_zero.mpr hφ))
--     (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

-- lemma PowerSeries.le_order_subst_left' {f : PowerSeries R} (hf : f.constantCoeff = 0) :
--     φ.order ≤ PowerSeries.order (φ.subst f) := by
--   conv_rhs => rw [order_eq_order]
--   exact le_order_subst_left _ hf

-- lemma PowerSeries.le_order_subst_right' {f : PowerSeries R} (hf : f.constantCoeff = 0)
--     (hφ : φ.constantCoeff = 0) :
--     f.order ≤ PowerSeries.order (φ.subst f) := by
--   simp_rw [order_eq_order]
--   exact le_order_subst_right φ hf hφ

theorem PowerSeries.expand_eq_expand :
    MvPowerSeries.expand p hp φ = PowerSeries.expand p hp φ := rfl

-- lemma PowerSeries.expand_smul (a : R):
--     expand p hp (a • φ) = a • φ.expand p hp := AlgHom.map_smul_of_tower _ _ _

lemma PowerSeries.expand_tsum [UniformSpace R] [T2Space R] [DiscreteUniformity R]
    {x : ℕ → PowerSeries R} (hx : Summable x):
    expand p hp (∑' i, x i) = ∑' i, (x i).expand p hp := by
  simp_rw [expand_apply]
  rw [tsum_subst hx (HasSubst.X_pow hp)]

omit [Finite σ] in
theorem PowerSeries.subst_sub {a : MvPowerSeries σ R} (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f - g) = subst a f - subst a g := by
  rw [← coe_substAlgHom ha, map_sub]
end

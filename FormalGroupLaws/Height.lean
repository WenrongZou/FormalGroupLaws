import FormalGroupLaws.Basic
import Mathlib.Algebra.CharP.Invertible
import FormalGroupLaws.AuxLem

variable {R : Type*} [CommRing R] {σ τ : Type}

open PowerSeries Finsupp

namespace FormalGroup

variable (F G : FormalGroup R) [F.IsComm] (n : ℕ)

noncomputable
def series (F : FormalGroup R) [F.IsComm] : ℕ → PowerSeries R
| 0 => 0
| k + 1 => F.toFun.subst ![(series F k), X]

@[simp]
lemma zero_series : F.series 0 = 0 := by
  simp [series]

lemma series_ConstCoeff : (F.series n).constantCoeff = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [series, Nat.succ_eq_add_one, Nat.reduceAdd]
    rw [constantCoeff, MvPowerSeries.constantCoeff_subst_eq_zero
      (HasSubst.FinPairing ih (by simp)) (by simp [ih]) F.zero_constantCoeff]

lemma subst_zero_eq_zero {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    f.subst (0 : σ → MvPowerSeries τ R) = 0 := by
  ext n
  rw [MvPowerSeries.coeff_subst ((MvPowerSeries.hasSubst_def 0).mpr (by simp)),
    MvPowerSeries.coeff_zero, finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd, hf]
  · have : (d.prod fun s e ↦ (0 : σ → MvPowerSeries τ R) s ^ e) = 0 := by
      have ⟨i, hi⟩ : d.support.Nonempty := support_nonempty_iff.mpr hd
      rw [prod, Finset.prod_eq_zero hi]
      · rw [Pi.zero_apply, zero_pow (mem_support_iff.mp hi)]
    rw [this, MvPowerSeries.coeff_zero, smul_zero]

/- this can be proved by nsmul_add in the mathlib `F.Point σ`. -/
noncomputable
def _root_.FormalGroupHom.series : FormalGroupHom F F where
  toFun := F.series n
  zero_constantCoeff := series_ConstCoeff _ _
  hom := by
    induction n with
    | zero =>
      simp only [zero_series, map_zero]
      rw [← coe_substAlgHom <| HasSubst.of_constantCoeff_zero F.zero_constantCoeff,
        map_zero, ← Pi.zero_def,  subst_zero_eq_zero F.zero_constantCoeff]
    | succ k ih =>
      calc
        _ = F.toFun.subst ![(F.series k).subst F.toFun, F.toFun] := sorry
        _ = (F.series k).subst F.toFun +[F] F.toFun := rfl
        _ = (F.series k).toMvPowerSeries (0 : Fin 2) +[F] (F.series k).toMvPowerSeries 1 +[F]
          (MvPowerSeries.X 1 +[F] MvPowerSeries.X 0) := by
          simp_rw [ih]
          congr
          · exact List.ofFn_inj.mp rfl
          · -- easy sorry, use comm
            sorry
        _ = (F.series k).toMvPowerSeries (0 : Fin 2) +[F] ((F.series k).toMvPowerSeries 1 +[F]
            MvPowerSeries.X 1) +[F] MvPowerSeries.X 0 := sorry
        _ = (F.series k).toMvPowerSeries (0 : Fin 2) +[F] MvPowerSeries.X 0
            +[F] (F.series (k + 1)).toMvPowerSeries 1 := sorry
        _ = _ := by

          sorry

section Height

open Finset

variable {p : ℕ} [CharP R p] {hp : p ≠ 1}

lemma zero_of_coeff_prime_pow_zero :
    (∀ n, coeff (p ^ n) (F.series p) = 0) → F.series p = 0 := by
  contrapose!
  intro h
  let m := PowerSeries.order (F.series p)
  sorry

lemma FormalGroupHom.exists_coeff_ne_zero_of_ne_zero {f : FormalGroupHom F G}
    (hp : p.Prime) (hf : f.toFun ≠ 0) : ∃ n, coeff (p ^ n) f.toFun ≠ 0 := by
  let m := f.toFun.order.toNat
  have m_pos : 0 < m := by sorry
  have : ∀ n < m, f.toFun.coeff n = 0 := coeff_of_lt_order_toNat
  have eq_aux := f.hom
  have ne_zero : f.toFun.coeff m ≠ 0 := coeff_order hf
  have eq_aux₁ : ∀ i ∈ Icc 1 (m - 1), (f.toFun.subst F.toFun).coeff
      (single 0 i + single 1 (m - i)) = f.toFun.coeff m * m.choose i := by
    intro i hi
    rw [coeff_subst (HasSubst.of_constantCoeff_zero F.zero_constantCoeff), finsum_eq_single _ m]
    · rw [smul_eq_mul]
      congr
      rw [MvPowerSeries.coeff_pow]


      sorry


    · sorry
  have eq_aux₂ : ∀ i ∈ Icc 1 (m - 1), (G.toFun.subst (fun x ↦ f.toFun.toMvPowerSeries x)).coeff
      (single 0 i + single 1 (m - i)) = 0 := sorry
  have eq_aux₃ : ∀ i ∈ Icc 1 (m - 1), f.toFun.coeff m * m.choose i = 0 := by
    intro i hi
    rw [← eq_aux₁ i hi, f.hom, eq_aux₂ i hi]
  have dvd_aux : ∀ i ∈ Icc 1 (m - 1), p ∣ m.choose i := by
    intro i hi
    specialize eq_aux₃ i hi
    by_contra hc
    have : IsUnit (m.choose i : R) := (CharP.isUnit_natCast_iff hp).mpr hc
    have : f.toFun.coeff m = 0 := (IsUnit.mul_left_eq_zero this).mp eq_aux₃
    exact ne_zero this
  obtain ⟨n, hn⟩ : ∃ n, m = p ^ n := exists_pow_eq_of_prime_dvd_choose hp m_pos dvd_aux
  exact ⟨n, hn ▸ ne_zero⟩

lemma exist_coeff_pow_ne_zero_of_ne_zero (h : F.series p ≠ 0) :
    (∃ n, coeff (p ^ n) (F.series p) ≠ 0) := by

  let m := (F.series p).order.toNat
  have : ∀ n < m, (F.series p).coeff n = 0 := coeff_of_lt_order_toNat
  have eq_aux := (FormalGroupHom.series F p).hom

  -- have m_eq_pow :
  sorry

theorem exist_coeff_pow_ne_zero_iff_ne_zero :
    (∃ n, coeff (p ^ n) (F.series p) ≠ 0) ↔ F.series p ≠ 0 :=
  ⟨fun ⟨n, hn⟩ => ne_of_apply_ne (coeff (p ^ n)) (hn · ),
    exist_coeff_pow_ne_zero_of_ne_zero _⟩

noncomputable
def height : ℕ∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : F.series p = 0 then ⊤ else Nat.find ((F.exist_coeff_pow_ne_zero_iff_ne_zero).mpr h)

import FormalGroupLaws.Basic

variable {R : Type*} [CommRing R] {σ τ : Type}

open PowerSeries Finsupp

namespace FormalGroup

variable (F : FormalGroup R) [F.IsComm] (n : ℕ)

noncomputable
def nseries (F : FormalGroup R) [F.IsComm] : ℕ → PowerSeries R
| 0 => 0
| k + 1 => F.toFun.subst ![(nseries F k), X]

@[simp]
lemma zero_series : F.nseries 0 = 0 := by
  simp [nseries]

lemma nseries_ConstCoeff : (F.nseries n).constantCoeff = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [nseries, Nat.succ_eq_add_one, Nat.reduceAdd]
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

noncomputable
def _root_.FormalGroupHom.nseries : FormalGroupHom F F where
  toFun := F.nseries n
  zero_constantCoeff := nseries_ConstCoeff _ _
  hom := by
    induction n with
    | zero =>
      simp only [zero_series, map_zero]
      rw [← coe_substAlgHom <| HasSubst.of_constantCoeff_zero F.zero_constantCoeff,
        map_zero, ← Pi.zero_def,  subst_zero_eq_zero F.zero_constantCoeff]
    | succ k ih =>
      calc
        _ = F.toFun.subst ![(F.nseries k).subst F.toFun, F.toFun] := sorry
        _ = (F.nseries k).subst F.toFun +[F] F.toFun := rfl
        _ = (F.nseries k).toMvPowerSeries (0 : Fin 2) +[F] (F.nseries k).toMvPowerSeries 1 +[F]
          (MvPowerSeries.X 1 +[F] MvPowerSeries.X 0) := by
          simp_rw [ih]
          congr
          · exact List.ofFn_inj.mp rfl
          · -- easy sorry, use comm
            sorry
        _ = (F.nseries k).toMvPowerSeries (0 : Fin 2) +[F] ((F.nseries k).toMvPowerSeries 1 +[F]
            MvPowerSeries.X 1) +[F] MvPowerSeries.X 0 := sorry
        _ = (F.nseries k).toMvPowerSeries (0 : Fin 2) +[F] MvPowerSeries.X 0
            +[F] (F.nseries (k + 1)).toMvPowerSeries 1 := sorry
        _ = _ := by

          sorry

section Height

variable {p : ℕ} [ExpChar R p] {hp : p ≠ 1}

lemma zero_of_coeff_prime_pow_zero :
    (∀ n, coeff (p ^ n) (F.nseries p) = 0) → F.nseries p = 0 := by

  sorry

theorem exist_coeff_pow_ne_zero_iff_ne_zero :
    (∃ n, coeff (p ^ n) (F.nseries p) ≠ 0) ↔ F.nseries p ≠ 0 :=
  ⟨fun ⟨n, hn⟩ => ne_of_apply_ne (coeff (p ^ n)) (hn · ),
    by contrapose!; exact zero_of_coeff_prime_pow_zero _⟩

noncomputable
def height : ℕ∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : F.nseries p = 0 then ⊤ else Nat.find ((F.exist_coeff_pow_ne_zero_iff_ne_zero).mpr h)

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import FormalGroupLaws.Basic
import FormalGroupLaws.LubinTateTheory.ConstructiveLem
import FormalGroupLaws.LubinTateTheory.TruncTotalDegLem

open ValuativeRel MvPowerSeries Classical FormalGroup

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [UniformSpace K]
  (π : 𝒪[K]) {R : Type*} [CommRing R]

variable {σ : Type*} {τ : Type*}  [IsNonarchimedeanLocalField K]

variable [DecidableEq σ] [Fintype σ] [DecidableEq τ] [Fintype τ]

noncomputable section


open LubinTateF

variable (f g: LubinTateF π)

/-- Given a multi variate power series `f` with two variables, assume `f` satisfies the condition
  of Lubin Tate Formal Group condition with respect to `π`. -/
def LubinTateFormalGroup :  FormalGroup (𝒪[K]) :=
  let ϕ₁ : MvPolynomial (Fin 2) (𝒪[K]) :=
    MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)
  have phi_supp : ∀ i ∈ ϕ₁.support, Finset.univ.sum ⇑i = 1 := by
    intro i
    have supp_eq : ϕ₁.support =
      {(Finsupp.single 0 1), (Finsupp.single 1 1)} := by
      refine Finset.ext_iff.mpr ?_
      intro d
      constructor
      · intro hd
        simp [ϕ₁] at hd ⊢
        by_contra hc
        simp at hc
        obtain ⟨hc₁, hc₂⟩ := hc
        simp [MvPolynomial.coeff_X', Ne.symm hc₁, Ne.symm hc₂] at hd
      · simp
        intro h
        have neg_aux : ¬ Finsupp.single (1 : Fin 2) 1 = Finsupp.single 0 1 := by
          refine Finsupp.ne_iff.mpr ?_
          use 1
          simp
        obtain h1 | h2 := h
        · simp [ϕ₁, MvPolynomial.coeff_X', h1, neg_aux]
        · simp [ϕ₁, MvPolynomial.coeff_X', h2, Ne.symm neg_aux]
    simp [supp_eq]
    intro h
    obtain h1 | h2 := h
    simp [h1]
    simp [h2]
  have phi_eq : ϕ₁ = MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := rfl
  let F_f := choose (constructive_lemma π 2 phi_supp f f)
  have eq_aux : F_f = choose (constructive_lemma π 2 phi_supp f f) := rfl
  {
  toFun := choose (constructive_lemma π 2 phi_supp f f)
  zero_constantCoeff := by
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp  f f)
    obtain ⟨h₁, h_hom⟩ := h₁
    calc
      _ = constantCoeff (((truncTotalDegHom 2)
        (choose (constructive_lemma π 2 phi_supp f f))) : MvPowerSeries (Fin 2) ↥𝒪[K]) (R := ↥𝒪[K]) := by
        unfold truncTotalDegHom
        simp [←coeff_zero_eq_constantCoeff, coeff_truncTotalDeg]
      _ = 0 := by
        rw [h₁]
        simp [ϕ₁]
  lin_coeff_X := by
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨htrunc, hsubst⟩ := h₁
    rw [←eq_aux]  at htrunc ⊢
    have eq_aux₁ : (coeff (Finsupp.single 0 1)) F_f
      = (coeff (Finsupp.single 0 1)) ϕ₁.toMvPowerSeries := by
      rw [←htrunc]
      simp [truncTotalDegHom, coeff_truncTotalDeg]
    rw [eq_aux₁, phi_eq]
    simp
    rw [coeff_X, if_neg]
    refine Finsupp.ne_iff.mpr ?_
    use 0
    simp
  lin_coeff_Y := by
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨htrunc, hsubst⟩ := h₁
    rw [←eq_aux]  at htrunc ⊢
    have eq_aux₁ : (coeff (Finsupp.single 1 1)) F_f
      = (coeff (Finsupp.single 1 1)) ϕ₁.toMvPowerSeries := by
      simp [←htrunc, truncTotalDegHom, coeff_truncTotalDeg]
    rw [eq_aux₁, phi_eq]
    simp
    rw [coeff_X, if_neg]
    refine Finsupp.ne_iff.mpr ?_
    use 0
    simp
  assoc := by
    let hf := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨⟨hf₁, hf₂⟩, hf₃⟩ := hf
    rw [←eq_aux] at hf₂
    let G₁ := subst (subst_fir F_f) F_f
    let G₂ := subst (subst_sec F_f) F_f
    have G_eq₁ : G₁ = subst (subst_fir F_f) F_f := rfl
    have G_eq₂ : G₂ = subst (subst_sec F_f) F_f := rfl
    -- φ = X 0 + X 1 + X 2
    let φ : MvPolynomial (Fin 3) 𝒪[K] := MvPolynomial.X (0 : Fin 3) +
      MvPolynomial.X 1 + MvPolynomial.X 2
    have phi_eq' : φ = MvPolynomial.X (0 : Fin 3) +
      MvPolynomial.X 1 + MvPolynomial.X 2 := by rfl
    have h_Ff : constantCoeff F_f = 0 := by
      rw [constantCoeff_of_truncTotalDeg_ge_one _ (show 2 ≥ 1 by norm_num),
        hf₁, phi_eq]
      simp
    have hf_constant : PowerSeries.constantCoeff f.toFun = 0 := constantCoeff_LubinTateF _ _
    have phi_supp' : ∀ i ∈ φ.support, Finset.univ.sum ⇑i = 1 := by
      -- same as above
      intro i
      have supp_eq : φ.support =
      {(Finsupp.single 0 1), (Finsupp.single 1 1), (Finsupp.single 2 1)} := by
        refine Finset.ext_iff.mpr ?_
        intro d
        constructor
        · intro hd
          simp [φ] at hd ⊢
          by_contra hc
          simp at hc
          obtain ⟨hc₁, hc₂, hc₃⟩ := hc
          simp [MvPolynomial.coeff_X', Ne.symm hc₁, Ne.symm hc₂, Ne.symm hc₃] at hd
        · simp
          intro h
          obtain h | h | h := h
          all_goals simp [h, phi_eq']
      simp [supp_eq]
      intro hi
      obtain h | h | h := hi
      all_goals simp [h]
    have constantF_f : constantCoeff F_f = 0  := by
      rw [←eq_aux] at hf₁
      rw [constantCoeff_of_truncTotalDeg_ge_one _ (show 2 ≥ 1 by linarith), hf₁, phi_eq]
      simp
    obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 3 phi_supp' f f)
    obtain G₀ := choose (constructive_lemma π 3 phi_supp' f f)
    obtain ⟨h, hunique⟩ := choose_spec (constructive_lemma π 2 phi_supp f f)
    obtain ⟨htrunc, hsubst⟩ := h
    -- here prove `truncTotalDeg 2 G₁ = φ` and `f (G₁(X, Y, Z)) = G₁ (f(X), f(Y), f(Z))`.
    have aux₁ : ↑((truncTotalDegHom  2) G₁) = φ ∧
      PowerSeries.subst G₁ f.toFun = subst f.toFun.toMvPowerSeries G₁ := by
      constructor
      · rw [truncTotalDegHom_of_subst _ _ h_Ff, htrunc]
        unfold ϕ₁
        have eq_aux : (subst (subst_fir F_f)
          ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
            MvPolynomial (Fin 2) 𝒪[K]) : MvPowerSeries (Fin 2) 𝒪[K]) (R := 𝒪[K]) )
          = (subst (subst_fir_aux) F_f) + X (2 : Fin 3) := by
          simp
          have has_subst : (constantCoeff F_f) = 0 := by
            rw [←eq_aux] at hf₁
            simp [constantCoeff_of_truncTotalDeg_ge_one F_f (by linarith) (d := 2), hf₁, phi_eq]
          rw [subst_add (has_subst_fir _ has_subst), subst_X (has_subst_fir _ has_subst),
            subst_X (has_subst_fir _ has_subst)]
        rw [eq_aux]
        simp
        unfold φ
        have eq_aux₂ : ((truncTotalDegHom 2)
          (X (2 : Fin 3)))  = MvPolynomial.X (2 : Fin 3) (R := 𝒪[K]) := by
          simp [truncTotalDegHom]
          refine MvPolynomial.ext_iff.mpr ?_
          intro n
          simp [coeff_truncTotalDeg, MvPolynomial.coeff_X']
          by_cases h1 : Finsupp.single 2 1 = n
          · have haux : Finset.univ.sum ⇑n < 2 := by
              simp [←h1]
            simp [←h1, coeff_X]
          · simp [h1, coeff_X, Ne.symm h1]
        have eq_aux₃ : ((truncTotalDegHom 2) (subst subst_fir_aux F_f))
          = MvPolynomial.X (0 : Fin 3) + MvPolynomial.X (1 : Fin 3) (R := 𝒪[K]) := by
          have aux : ((truncTotalDegHom 2) (subst subst_fir_aux F_f)).toMvPowerSeries
          = (MvPolynomial.X (0 : Fin 3) + MvPolynomial.X (1 : Fin 3) (R := 𝒪[K])).toMvPowerSeries := by
            rw [truncTotalDegHom_of_subst' _ h_Ff, htrunc]
            unfold ϕ₁
            simp [subst_add has_subst_fir_aux (X 0) (X 1), subst_X has_subst_fir_aux]
            simp [subst_fir_aux, truncTotalDegHom, Y₀, Y₁, truncTotalDegTwo.X]
          norm_cast at aux
        rw [eq_aux₂, eq_aux₃]
      ·
        rw [G_eq₁]
        have eq_aux₁ : PowerSeries.subst (subst (subst_fir F_f) F_f) f.toFun
          = subst (subst_fir F_f) (PowerSeries.subst F_f f.toFun) := by
          simp [PowerSeries.subst]
          rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero constantF_f))
            (has_subst_fir F_f constantF_f)]
        rw [eq_aux₁, hf₂]
        let map_aux : Fin 2 → MvPowerSeries (Fin 3) (𝒪[K])
        | ⟨0, _⟩ => PowerSeries.subst (subst subst_fir_aux F_f) f.toFun
        | ⟨1, _⟩ => f.toFun.toMvPowerSeries 2
        have eq_aux₂ : subst (subst_fir F_f) (subst f.toFun.toMvPowerSeries F_f)
          = subst map_aux F_f := by
          rw [subst_comp_subst_apply]
          apply subst_congr
          funext s
          by_cases hs₀ : s = 0
          · unfold subst_fir
            simp [map_aux, hs₀, PowerSeries.toMvPowerSeries, PowerSeries.subst]
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 0))
              (has_subst_fir F_f constantF_f)]
            apply subst_congr
            funext t
            rw [subst_X (has_subst_fir F_f constantF_f)]
          · have hs₁ : s = 1 := by omega
            unfold subst_fir
            simp [map_aux, hs₁, PowerSeries.toMvPowerSeries, PowerSeries.subst]
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 1))
              (has_subst_fir F_f constantF_f)]
            apply subst_congr
            funext t
            rw [subst_X (has_subst_fir F_f constantF_f)]

          exact (has_subst_toMvPowerSeries hf_constant)
          exact (has_subst_fir F_f constantF_f)
        rw [eq_aux₂]
        unfold map_aux
        let map_aux' : Fin 2 → MvPowerSeries (Fin 3) (𝒪[K])
        | ⟨0, _⟩ => f.toFun.toMvPowerSeries 0
        | ⟨1, _⟩ => f.toFun.toMvPowerSeries 1
        have eq_aux₃ : PowerSeries.subst (subst subst_fir_aux F_f) f.toFun
          = subst map_aux' F_f := by
          have eq_aux : subst subst_fir_aux (PowerSeries.subst F_f f.toFun)
            = subst subst_fir_aux (subst f.toFun.toMvPowerSeries F_f) (S := 𝒪[K]) := by
            rw [hf₂]
          rw [PowerSeries.subst] at eq_aux
          rw [PowerSeries.subst, ←subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s ↦ constantF_f)
            has_subst_fir_aux , eq_aux, subst_comp_subst_apply (has_subst_toMvPowerSeries hf_constant) has_subst_fir_aux]
          apply subst_congr
          simp [map_aux']
          unfold subst_fir_aux PowerSeries.toMvPowerSeries
          funext s
          by_cases hs₀ : s = 0
          · simp [hs₀]
            unfold PowerSeries.subst
            rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 0)) has_subst_fir_aux]
            apply subst_congr
            funext t
            rw [subst_X has_subst_fir_aux]
          · have hs₁ : s = 1 := by omega
            simp [hs₁]
            rw [PowerSeries.subst, subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 1)) has_subst_fir_aux]
            apply subst_congr
            funext t
            rw [subst_X has_subst_fir_aux ]
        rw [eq_aux₃, subst_comp_subst_apply (has_subst_fir F_f constantF_f) (has_subst_toMvPowerSeries hf_constant)]
        apply subst_congr
        funext x t
        fin_cases x
        · -- the cases `x = 0`
          unfold map_aux' subst_fir subst_fir_aux
          simp
          rw [subst_comp_subst_apply has_subst_fir_aux (has_subst_toMvPowerSeries hf_constant)]
          congr
          funext x' t'
          fin_cases x'
          all_goals rw [subst_X (has_subst_toMvPowerSeries hf_constant)]
        · -- the case `x = 1`
          unfold subst_fir
          simp [Y₂]
          rw [subst_X (has_subst_toMvPowerSeries hf_constant)]

    -- here prove  `truncTotalDegHom 2 G₂ = φ` and `f (G₂ (X, Y, Z)) = G₂ (f (X), f (Y), f (Z))`.
    have aux₂ : ↑((truncTotalDegHom 2) G₂) = φ ∧
      PowerSeries.subst G₂ f.toFun = subst f.toFun.toMvPowerSeries G₂ := by

      constructor
      ·
        rw [truncTotalDegHom_of_subst₂ _ _ h_Ff, htrunc, phi_eq]
        have eq_aux : (subst (subst_sec F_f)
          ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
            MvPolynomial (Fin 2) 𝒪[K]) : MvPowerSeries (Fin 2) 𝒪[K]) (R := 𝒪[K]) )
          = X (0 : Fin 3) + (subst (subst_sec_aux) F_f)  := by
          simp
          have has_subst : (constantCoeff F_f) = 0 := by
            rw [←eq_aux] at hf₁
            simp [constantCoeff_of_truncTotalDeg_ge_one F_f (by linarith) (d := 2), hf₁, phi_eq]
          rw [subst_add (has_subst_sec _ has_subst), subst_X (has_subst_sec _ has_subst),
            subst_X (has_subst_sec _ has_subst)]
        rw [eq_aux]
        simp
        unfold φ
        have eq_aux₂ : ((truncTotalDegHom 2)
          (X (0 : Fin 3)))  = MvPolynomial.X (0 : Fin 3) (R := 𝒪[K]) := by
          simp [truncTotalDegHom]
          refine MvPolynomial.ext_iff.mpr ?_
          intro n
          simp [coeff_truncTotalDeg, MvPolynomial.coeff_X']
          by_cases h1 : Finsupp.single 0 1 = n
          · have haux : Finset.univ.sum ⇑n < 2 := by
              simp [←h1]
            simp [←h1, coeff_X]
          · simp [h1, coeff_X, Ne.symm h1]
        have eq_aux₃ : ((truncTotalDegHom 2) (subst subst_sec_aux F_f))
          = MvPolynomial.X (1 : Fin 3) + MvPolynomial.X (2 : Fin 3) (R := 𝒪[K]) := by
          have aux : ((truncTotalDegHom 2) (subst subst_sec_aux F_f)).toMvPowerSeries
          = (MvPolynomial.X (1 : Fin 3) + MvPolynomial.X (2 : Fin 3) (R := 𝒪[K])).toMvPowerSeries := by
            rw [truncTotalDegHom_of_subst₂' _ h_Ff, htrunc]
            unfold ϕ₁
            simp [subst_add has_subst_sec_aux (X 0) (X 1), subst_X has_subst_sec_aux]
            simp [subst_sec_aux, truncTotalDegHom, Y₁, truncTotalDegTwo.X]
          norm_cast at aux
        rw [eq_aux₂, eq_aux₃]
        ring_nf
      ·
        rw [G_eq₂]
        have eq_aux₁ : PowerSeries.subst (subst (subst_sec F_f) F_f) f.toFun
          = subst (subst_sec F_f) (PowerSeries.subst F_f f.toFun) := by
          simp [PowerSeries.subst]
          rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero constantF_f))
            (has_subst_sec F_f constantF_f)]
        rw [eq_aux₁, hf₂, subst_comp_subst_apply (has_subst_sec F_f constantF_f)
          (has_subst_toMvPowerSeries hf_constant), subst_comp_subst_apply
          (has_subst_toMvPowerSeries hf_constant) (has_subst_sec F_f constantF_f)]
        apply subst_congr
        funext x
        fin_cases x
        · -- the case `x = 0`
          simp [subst_sec, Y₀]
          rw [subst_X]
          rw [PowerSeries.toMvPowerSeries, PowerSeries.toMvPowerSeries,
            PowerSeries.subst, subst_comp_subst_apply , PowerSeries.subst]
          apply subst_congr
          funext t
          unfold subst_sec
          rw [subst_X]
          exact has_subst_sec F_f constantF_f
          refine hasSubst_of_constantCoeff_zero ?_
          simp
          exact has_subst_sec F_f constantF_f
          exact has_subst_toMvPowerSeries hf_constant
        · -- the case `x = 1`
          simp [subst_sec]
          unfold subst_sec PowerSeries.toMvPowerSeries PowerSeries.subst
          rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
            (fun s ↦ constantCoeff_X 1)) (has_subst_sec F_f constantF_f),
            subst_X (has_subst_sec F_f constantF_f)]
          have eq_aux : subst subst_sec_aux (PowerSeries.subst F_f f.toFun) =
            subst subst_sec_aux (subst f.toFun.toMvPowerSeries F_f) (S := 𝒪[K])  := by
            rw [hf₂]
          rw [PowerSeries.subst, subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero fun s ↦ constantF_f)
            has_subst_sec_aux ] at eq_aux
          rw [eq_aux]
          rw [subst_comp_subst_apply (has_subst_toMvPowerSeries hf_constant)
            has_subst_sec_aux, subst_comp_subst_apply has_subst_sec_aux]
          apply subst_congr
          funext t
          fin_cases t
          · -- the case `t = 0`
            unfold subst_sec_aux
            simp
            rw [subst_X, PowerSeries.toMvPowerSeries, PowerSeries.subst,
              subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 0))
              has_subst_sec_aux]
            apply subst_congr
            rw [subst_X has_subst_sec_aux]
            exact has_subst_toMvPowerSeries hf_constant
          · -- the cases `t = 1`
            unfold subst_sec_aux
            simp
            rw [subst_X, PowerSeries.toMvPowerSeries, PowerSeries.subst,
              subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X 1))
              has_subst_sec_aux]
            apply subst_congr
            rw [subst_X has_subst_sec_aux]
            exact has_subst_toMvPowerSeries hf_constant
          exact has_subst_toMvPowerSeries hf_constant
    obtain eq_aux₁ := h₂ _ aux₁
    obtain eq_aux₂ := h₂ _ aux₂
    unfold G₁ at eq_aux₁
    unfold G₂ at eq_aux₂
    rw [eq_aux₁, ←eq_aux₂]
}

namespace LubinTateFormalGroup

omit [UniformSpace K] [IsNonarchimedeanLocalField K] in
lemma supp_of_linear_term :
  let ϕ₁ : MvPolynomial (Fin 2) (𝒪[K]) := MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2);
  ∀ i ∈ ϕ₁.support, Finset.univ.sum ⇑i = 1 := by
  intro ϕ₁ i
  -- MvPolynomial.support_X and MvPolynomial.support_add
  have supp_eq : MvPolynomial.support ϕ₁ =
    {(Finsupp.single 0 1), (Finsupp.single 1 1)} := by
    refine Finset.ext_iff.mpr ?_
    intro d
    constructor
    · intro hd
      simp [ϕ₁] at hd ⊢
      by_contra hc
      simp at hc
      obtain ⟨hc₁, hc₂⟩ := hc
      simp [MvPolynomial.coeff_X', Ne.symm hc₁, Ne.symm hc₂] at hd
    · simp
      intro h
      have neg_aux : ¬ Finsupp.single (1 : Fin 2) 1 = Finsupp.single 0 1 := by
        refine Finsupp.ne_iff.mpr ?_
        use 1
        simp
      obtain h1 | h2 := h
      · simp [ϕ₁, MvPolynomial.coeff_X', h1, neg_aux]
      · simp [ϕ₁, MvPolynomial.coeff_X', h2, Ne.symm neg_aux]
  simp [supp_eq]
  intro h
  obtain h1 | h2 := h
  simp [h1]
  simp [h2]

def Hom : FormalGroupHom (LubinTateFormalGroup _ f) (LubinTateFormalGroup _ f)
  := {
    toFun := f.toFun
    zero_constantCoeff := by
      obtain h₁ := f.trunc_degree_two
      have coeff_aux₁ : (PowerSeries.constantCoeff)
        (PowerSeries.trunc 2 f.toFun) = Polynomial.constantCoeff
        (Polynomial.C π * Polynomial.X) := by
        simp [h₁]
      calc
        _ = PowerSeries.constantCoeff (PowerSeries.trunc 2 f.toFun) (R := ↥𝒪[K]) := by
          simp [PowerSeries.coeff_trunc]
        _ = 0 := by
          simp [coeff_aux₁]
    hom := by
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma π 2 supp_of_linear_term f f)
      obtain ⟨h₁, h_hom⟩ := h₁
      unfold LubinTateFormalGroup
      rw [h_hom]
  }



/-- For every `f ∈ LubinTateF K π`, formal group law of Lubin Tate's construction
  `F_f` with coefficient in `𝒪[K]` admitting `f` as an endomorphism.-/
theorem FormalGroupLaw_of_endomorphism  :
  ∃ (α : FormalGroupHom (LubinTateFormalGroup _ f) (LubinTateFormalGroup _ f)),
  α.toFun = f.toFun := by
  use (Hom _ f)
  simp [Hom]


/-- For every `f ∈ LubinTateF K π`, there is a unique formal group law
  `F_f` with coefficient in `𝒪[K]` admitting `f` as an endomorphism.-/
theorem exist_unique_FormalGroup :
  ∃! (F_f : FormalGroup (𝒪[K])), ∃ (α : FormalGroupHom F_f F_f),
  α.toFun = f.toFun := by
  refine existsUnique_of_exists_of_unique ?_  ?_
  · use (LubinTateFormalGroup _ f)
    use (Hom _ f)
    rw [Hom]
  · obtain ⟨⟨h₁, h_hom⟩, h₂⟩ := choose_spec (constructive_lemma π 2 supp_of_linear_term f f)
    intro y₁ y₂ ⟨α, ha⟩ ⟨β, hb⟩
    obtain ⟨F_f', h1, h2⟩  := constructive_lemma_two π f f
    obtain eq₁ := h2 y₁.toFun ⟨FormalGroup.truncTotalDegTwo y₁, by rw [←ha,α.hom]⟩
    obtain eq₂ := h2 y₂.toFun ⟨FormalGroup.truncTotalDegTwo y₂, by rw [←hb,β.hom]⟩
    rw [FormalGroup.ext_iff, eq₁, ←eq₂]


/-- Given a `f ∈ LubinTateF π`, and `F_f` be the unique Lubin Tate Formal Group associate to
  `f`, then the constant coefficient of `F_f` is zero. -/
theorem constantCoeff_zero :
  constantCoeff (LubinTateFormalGroup π f).toFun = 0 := by
  -- rw [←coeff_zero_eq_constantCoeff]
  simp [constantCoeff_of_truncTotalDeg_ge_one _ (show 2 ≥ 1 by norm_num),
    FormalGroup.truncTotalDegTwo (LubinTateFormalGroup π f)]


/-- Given a `f ∈ LubinTateF π`, and `F_f` be the unique Lubin Tate Formal Group associate to
  `f`, `f ∘ F_f (X, Y) = F_f (f(X), f(Y))`.-/
theorem endomorphism :
  PowerSeries.subst (LubinTateFormalGroup π f).toFun f.toFun =
  subst f.toFun.toMvPowerSeries (LubinTateFormalGroup π f).toFun := by
  obtain a := choose (FormalGroupLaw_of_endomorphism π f)
  obtain ha := choose_spec (FormalGroupLaw_of_endomorphism π f)
  rw [←ha]
  exact (choose (FormalGroupLaw_of_endomorphism π f)).hom



/-- Given a `f ∈ LubinTateF π`, and `F_f` be the unique Lubin Tate Formal Group associate to
  `f`, then the truncation of total degree `2` of `F_f ∈ 𝒪[K]⟦X, Y⟧` is `X + Y`. -/
theorem truncTotalDegTwo :
  truncTotalDeg 2 (LubinTateFormalGroup π f).toFun = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  simp [←FormalGroup.truncTotalDegTwo (LubinTateFormalGroup π f), truncTotalDegHom]


open LubinTateFormalGroup

/-- For all `f, g ∈ F_π` there is a unique power series`[a]_g,f` such that
  `PowerSeries.trunc 2 [a]_g,f = a * X` and `g ∘ [a]_g,f = [a]_g,f ∘ f`, and this
  `[a]_g,f` turn out to be a formal group homomorphim from `F_f` to `F_g`. -/
def ScalarHom (a : 𝒪[K]) : FormalGroupHom (LubinTateFormalGroup π f) (LubinTateFormalGroup π g) :=
  let hom_a := choose (constructive_lemma_poly π f g a)
  have hom_a_eq : hom_a = choose (constructive_lemma_poly π f g a) := rfl
  { toFun := choose (constructive_lemma_poly π f g a)
    zero_constantCoeff := by
      obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma_poly π f g a)
      rw [←hom_a_eq] at h₁ ⊢
      obtain ⟨htrunc, hsubst⟩ := h₁
      have aux : PowerSeries.constantCoeff hom_a
        = Polynomial.constantCoeff (PowerSeries.trunc 2 hom_a) := by
        rw [Polynomial.constantCoeff_apply, ←PowerSeries.coeff_zero_eq_constantCoeff,
          PowerSeries.coeff_trunc, if_pos (by norm_num)]
      simp [aux, Polynomial.constantCoeff_apply, htrunc]
    hom := by
      rw [←hom_a_eq]
      obtain ⟨ϕ, h₁, h₂⟩ := constructive_lemma_two' π f g a
      obtain ⟨htrunc, hsubst⟩ := h₁
      simp at h₂
      obtain ⟨hom_a_spec₁, hom_a_spec₂⟩ := choose_spec (constructive_lemma_poly π f g a)
      rw [←hom_a_eq] at hom_a_spec₁ hom_a_spec₂
      obtain ⟨hom_a_trunc, hom_a_subst⟩ := hom_a_spec₁
      have eq_aux₁ : MvPowerSeries.truncTotalDeg 2 (PowerSeries.subst
        (LubinTateFormalGroup π f).toFun hom_a)
        = MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 := by
        rw [MvPowerSeries.truncTotalDeg.PowerSeries_subst_n _ _ 2 (constantCoeff_zero π f), hom_a_trunc]
        simp
        rw [←(PowerSeries.smul_eq_C_mul PowerSeries.X a), PowerSeries.subst_smul
          (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_zero π f)),
          PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero
          (constantCoeff_zero π f)), truncTotalDeg_smul, LubinTateFormalGroup.truncTotalDegTwo,
          MvPolynomial.smul_eq_C_mul _ a]
        ring
      have hom_a_constantCoeff : PowerSeries.constantCoeff hom_a = 0 := by
        rw [←PowerSeries.coeff_zero_eq_constantCoeff]
        calc
          _ = Polynomial.coeff (PowerSeries.trunc 2 hom_a) 0 := by
            rw [PowerSeries.coeff_trunc, if_pos (by norm_num)]
          _ = 0 := by
            rw [hom_a_trunc]
            simp
      have eq_aux₂ : truncTotalDeg 2 (subst
        hom_a.toMvPowerSeries (LubinTateFormalGroup π g).toFun)
        = MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 := by
        have aux : ∀ (x : Fin 2), constantCoeff (hom_a.toMvPowerSeries x) = 0 := by
          intro x
          fin_cases x
          · rw [PowerSeries.toMvPowerSeries, ←coeff_zero_eq_constantCoeff, PowerSeries.coeff_subst
              (PowerSeries.HasSubst.X _)]
            simp
            apply finsum_eq_zero_of_forall_eq_zero
            intro d
            by_cases hd₀ : d = 0
            · simp [hd₀, hom_a_constantCoeff]
            · simp [zero_pow hd₀]
          · rw [PowerSeries.toMvPowerSeries, ←coeff_zero_eq_constantCoeff, PowerSeries.coeff_subst
              (PowerSeries.HasSubst.X _)]
            simp
            apply finsum_eq_zero_of_forall_eq_zero
            intro d
            by_cases hd₀ : d = 0
            · simp [hd₀, hom_a_constantCoeff]
            · simp [zero_pow hd₀]
        rw [truncTotalDeg.MvPowerSeries_subst_two _ _ aux, LubinTateFormalGroup.truncTotalDegTwo]
        simp
        rw [subst_add (hasSubst_of_constantCoeff_zero aux),
          subst_X (hasSubst_of_constantCoeff_zero aux),
          subst_X (hasSubst_of_constantCoeff_zero aux),
          PowerSeries.toMvPowerSeries, PowerSeries.toMvPowerSeries,
          truncTotalDeg_map_add, truncTotalDeg.PowerSeries_subst_n _ _ 2 (constantCoeff_X 0),
          hom_a_trunc]
        simp
        rw [←(PowerSeries.smul_eq_C_mul PowerSeries.X a), PowerSeries.subst_smul
          (PowerSeries.HasSubst.X 0), PowerSeries.subst_X (PowerSeries.HasSubst.X 0),
          truncTotalDeg.PowerSeries_subst_n _ _ 2 (constantCoeff_X 1), hom_a_trunc]
        simp
        rw [←(PowerSeries.smul_eq_C_mul PowerSeries.X a), PowerSeries.subst_smul
          (PowerSeries.HasSubst.X 1), PowerSeries.subst_X (PowerSeries.HasSubst.X 1)]
        ext m
        rw [MvPolynomial.coeff_add]
        rw [coeff_truncTotalDeg, coeff_truncTotalDeg]
        by_cases ha : Finset.univ.sum ⇑m < 2
        · rw [if_pos ha, if_pos ha]
          simp [MvPolynomial.coeff_X']
          by_cases hb : Finsupp.single 0 1 = m
          · have neq : Finsupp.single 1 1 ≠ m := by
              rw [←hb]
              by_contra hc
              have aux' : Finsupp.single (1 : Fin 2) 1 0 = Finsupp.single (0 : Fin 2) 1 0 := by
                rw [hc]
              simp at aux'
            rw [if_neg neq, if_pos hb, coeff_X, coeff_X, if_neg (Ne.symm neq),
              if_pos (Eq.symm hb)]
            simp
          · by_cases hb' : Finsupp.single 1 1 = m
            rw [if_neg hb, if_pos hb', coeff_X, coeff_X, if_neg (Ne.symm hb),
              if_pos (Eq.symm hb')]
            simp
            rw [if_neg hb', if_neg hb, coeff_X, coeff_X, if_neg (Ne.symm hb),
              if_neg (Ne.symm hb')]
            simp
        · rw [if_neg ha, if_neg ha]
          simp [MvPolynomial.coeff_X']
          have neq₁ : Finsupp.single (0 : Fin 2) 1 ≠ m := by
            simp at ha
            by_contra hc
            have add_aux : m 0 + m 1 = 1 := by
              simp [←hc]
            linarith
          have neq₂ : Finsupp.single (1 : Fin 2) 1 ≠ m := by
            simp at ha
            by_contra hc
            have add_aux : m 0 + m 1 = 1 := by
              simp [←hc]
            linarith
          simp [if_neg neq₁, if_neg neq₂]
      /- `g ∘ hom_a (F_f (X, Y)) = hom_a (F_f (f(X), f(Y)))`. -/
      have eq_aux₃ : PowerSeries.subst (PowerSeries.subst
        (LubinTateFormalGroup π f).toFun hom_a) g.toFun = subst f.toFun.toMvPowerSeries
        (PowerSeries.subst (LubinTateFormalGroup π f).toFun hom_a) := by
        obtain has_subst₃:=  PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero
          (LubinTateFormalGroup.constantCoeff_zero π f))
        obtain has_subst₄ := has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f) (σ := Fin 2)
        obtain has_subst₁ := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_LubinTateF π f)
        obtain has_subst₂ := PowerSeries.HasSubst.of_constantCoeff_zero (LubinTateFormalGroup.constantCoeff_zero π f)
        rw [←PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero'
          hom_a_constantCoeff) (PowerSeries.HasSubst.of_constantCoeff_zero
          (LubinTateFormalGroup.constantCoeff_zero π f)), hom_a_subst,
          PowerSeries.subst_comp_subst_apply has_subst₁ has_subst₂, PowerSeries.subst,
          PowerSeries.subst, PowerSeries.subst,subst_comp_subst_apply has_subst₃ has_subst₄]
        apply subst_congr
        funext s
        rw [←LubinTateFormalGroup.endomorphism, PowerSeries.subst]
      /- `g ∘ F_g (hom_a (X), hom_a (Y)) = F_g (hom_a (f (X)), hom_a (f (Y)))`. -/
      have eq_aux₄ : PowerSeries.subst (subst hom_a.toMvPowerSeries
        (LubinTateFormalGroup π g).toFun) g.toFun = subst f.toFun.toMvPowerSeries
        (subst hom_a.toMvPowerSeries (LubinTateFormalGroup π g).toFun) := by
        obtain has_subst₁ := PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero (LubinTateFormalGroup.constantCoeff_zero π g))
        obtain has_subst₂ := has_subst_toMvPowerSeries hom_a_constantCoeff (σ := Fin 2)
        rw [PowerSeries.subst, ←subst_comp_subst_apply has_subst₁ has_subst₂, ←PowerSeries.subst,
        LubinTateFormalGroup.endomorphism, subst_comp_subst_apply
        (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π g))
        has_subst₂, subst_comp_subst_apply
        has_subst₂ (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f))]
        apply subst_congr
        funext s
        have subst_eq : subst hom_a.toMvPowerSeries (g.toFun.toMvPowerSeries s)
          = PowerSeries.toMvPowerSeries (PowerSeries.subst hom_a g.toFun) s := by
          simp [PowerSeries.toMvPowerSeries, PowerSeries.subst]
          rw [subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s))
          has_subst₂, subst_comp_subst_apply
          (hasSubst_of_constantCoeff_zero fun s ↦ hom_a_constantCoeff)
          (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s))]
          apply subst_congr
          funext t
          rw [subst_X has_subst₂]
          rfl
        have subst_eq' : subst f.toFun.toMvPowerSeries (hom_a.toMvPowerSeries s)
          = PowerSeries.toMvPowerSeries (PowerSeries.subst f.toFun hom_a) s := by
          simp [PowerSeries.toMvPowerSeries, PowerSeries.subst]
          rw [subst_comp_subst_apply (PowerSeries.HasSubst.const
          (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_LubinTateF π f)))
          (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s)), subst_comp_subst_apply
          (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X s))
          (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f))]
          apply subst_congr
          funext t
          rw [subst_X (has_subst_toMvPowerSeries (constantCoeff_LubinTateF π f))]
          rfl
        rw [subst_eq, hom_a_subst, ←subst_eq']
      obtain eq₁ := h₂ _ eq_aux₁ eq_aux₃
      obtain eq₂ := h₂ _ eq_aux₂ eq_aux₄
      rw [eq₁, ←eq₂]
      }

/-- For all `f, g ∈ F_π`, the scalar homomorpshim `[a]_g,f` such that
  `PowerSeries.trunc 2 [a]_g,f = a * X` and `g ∘ [a]_g,f = [a]_g,f ∘ f`, and this
  `[a]_g,f` turn out to be a formal group homomorphim from `F_f` to `F_g`. -/
theorem subst_of_ScalarHom (a : 𝒪[K]) : PowerSeries.trunc 2 (ScalarHom _ f g a).toFun
  = (Polynomial.C a) * (Polynomial.X) ∧
  PowerSeries.subst (ScalarHom _ f g a).toFun g.toFun
  = PowerSeries.subst f.toFun (ScalarHom _ f g a).toFun := by
  have scalarHom_eq : (ScalarHom _ f g a).toFun = choose (constructive_lemma_poly π f g a) := rfl
  obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma_poly π f g a)
  exact h₁


-- Proposition 2.14
/-- For all `f, g ∈ F_π` there is a unique power series`[a]_g,f` such that
  `PowerSeries.trunc 2 [a]_g,f = a * X` and `g ∘ [a]_g,f = [a]_g,f ∘ f`, and this
  `[a]_g,f` turn out to be a formal group homomorphim from `F_f` to `F_g`. -/
theorem exist_unique_of_scalar_mul (f g : LubinTateF π) (a : 𝒪[K]) :
  ∃! (scalarHom : FormalGroupHom (LubinTateFormalGroup π f) (LubinTateFormalGroup π g)),
  PowerSeries.trunc 2 scalarHom.toFun = (Polynomial.C a) * (Polynomial.X) ∧
  PowerSeries.subst scalarHom.toFun g.toFun  = PowerSeries.subst f.toFun scalarHom.toFun := by
  /- Existence of homomorphism of formal group induced by `a ∈ 𝒪[K]`.-/
  use (ScalarHom _ f g a)
  /- Uniqueness of this homomorphism of formal group induced by `a ∈ 𝒪[K]`. -/
  have scalarHom_eq : (ScalarHom _ f g a).toFun = choose (constructive_lemma_poly π f g a) := rfl
  obtain ⟨h₁, h₂⟩ := choose_spec (constructive_lemma_poly π f g a)
  simp
  constructor
  · exact h₁
  · intro a' ha₁' ha₂'
    apply  FormalGroupHom.ext_iff.mpr
    obtain h1 := h₂ a'.toFun ⟨ha₁',ha₂'⟩
    rw [scalarHom_eq]
    exact h1


/-- For all `f, g ∈ F_π` there is a unique power series`[a]_g,f` such that
  `PowerSeries.trunc 2 [a]_g,f = a * X`.  -/
theorem ScalarHom.PowerSeries_trunc_two (f g : LubinTateF π) (a : 𝒪[K]) :
  PowerSeries.trunc 2 (ScalarHom π f g a).toFun = Polynomial.C a * Polynomial.X := by
  obtain h₁ := choose_spec (exist_unique_of_scalar_mul π f g a)
  simp at h₁
  obtain ⟨h₁, h₂⟩ := h₁
  obtain ⟨htrunc, hsubst⟩ := h₁
  rw [←htrunc, ScalarHom]
  simp


  sorry

/-- For all `f, g ∈ F_π` there is a unique power series`[a]_g,f` such that
  `g ∘ [a]_g,f = [a]_g,f ∘ f`. -/
theorem ScalarHom.subst_eq (f g : LubinTateF π) (a : 𝒪[K]) :
  PowerSeries.subst (ScalarHom π f g a).toFun g.toFun = PowerSeries.subst
  f.toFun (ScalarHom π f g a).toFun := by
  obtain h₁ := choose_spec (exist_unique_of_scalar_mul π f g a)
  simp at h₁
  obtain ⟨h₁, h₂⟩ := h₁
  obtain ⟨htrunc, hsubst⟩ := h₁
  rw [ScalarHom]
  simp [hsubst]
  sorry

-- how to define notation here `--------------------------------`
-- variable (a : 𝒪[K]) (f g : LubinTateF π)

-- notation "[" a "]" π f g => choose (existence_of_scalar_mul π f g a)

-- #check [ a ] π f g

open scoped FormalGroup


-- Proposition 2.15.1
/-- For any `f, g` be Lubin Tate F, `a b ∈ 𝒪[K]`,
  then `[a + b]_f,g = [a]_f, g + [b]_f, g` -/
theorem additive_of_ScalarHom (f g : LubinTateF π) (a b : 𝒪[K]) :
  (ScalarHom π f g (a + b)).toFun = (ScalarHom π f g a).toFun +[(LubinTateFormalGroup π g)]
  (ScalarHom π f g b).toFun := by
  /- use constructive_lemma_poly. -/
  obtain trunc_eq₁ := ScalarHom.PowerSeries_trunc_two π f g (a + b)
  obtain trunc_eq₂ := ScalarHom.PowerSeries_trunc_two π f g a
  obtain trunc_eq₃ := ScalarHom.PowerSeries_trunc_two π f g b
  obtain ⟨φ, h₁, h₂⟩ := constructive_lemma_poly π f g (a + b)
  let F₂ := (ScalarHom π f g a).toFun +[(LubinTateFormalGroup π g)] (ScalarHom π f g b).toFun
  obtain ⟨htrunc, hsubst⟩ := h₁
  simp at h₂
  have eq_aux : PowerSeries.trunc 2 F₂ =
    Polynomial.C (a + b) * Polynomial.X := by
    unfold F₂ FormalGroup.add
    have coeff_zero : ∀ (x : Fin 2),
    PowerSeries.constantCoeff (FormalGroup.add_aux (ScalarHom π f g a).toFun
    (ScalarHom π f g b).toFun x) = 0 := by
      intro x
      fin_cases x
      · simp [FormalGroup.add_aux, (ScalarHom π f g a).zero_constantCoeff]
      · simp [FormalGroup.add_aux, (ScalarHom π f g b).zero_constantCoeff]
    obtain has_subst₄:=  hasSubst_of_constantCoeff_zero coeff_zero
    rw [PowerSeries.trunc_of_subst_trunc _ _ coeff_zero, LubinTateFormalGroup.truncTotalDegTwo]
    simp
    rw [subst_add has_subst₄, subst_X has_subst₄, subst_X has_subst₄]
    simp [FormalGroup.add_aux]
    rw [ScalarHom.PowerSeries_trunc_two, ScalarHom.PowerSeries_trunc_two]
    ring
  have subst_aux₂ : PowerSeries.subst F₂
    g.toFun = PowerSeries.subst f.toFun F₂  := by
    unfold F₂ FormalGroup.add
    have has_subst₁ : HasSubst (FormalGroup.add_aux (ScalarHom π f g a).toFun
      (ScalarHom π f g b).toFun) := by
      refine hasSubst_of_constantCoeff_zero ?_
      intro x
      fin_cases x
      simp [FormalGroup.add_aux, (ScalarHom π f g _).zero_constantCoeff]
      simp [FormalGroup.add_aux, (ScalarHom π f g _).zero_constantCoeff]
    obtain has_subst₂ := (PowerSeries.HasSubst.const
      (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_LubinTateF π f)))
    obtain has_subst₃ := PowerSeries.HasSubst.const
      (PowerSeries.HasSubst.of_constantCoeff_zero (LubinTateFormalGroup.constantCoeff_zero π g))
    rw [PowerSeries.subst, ←subst_comp_subst_apply has_subst₃ has_subst₁, ←PowerSeries.subst,
      LubinTateFormalGroup.endomorphism, subst_comp_subst_apply (has_subst_toMvPowerSeries
      (constantCoeff_LubinTateF π g)) has_subst₁, PowerSeries.subst,
      subst_comp_subst_apply has_subst₁ has_subst₂]
    apply subst_congr
    funext s
    fin_cases s
    · simp [FormalGroup.add_aux]
      rw [←PowerSeries.subst, ←ScalarHom.subst_eq, PowerSeries.toMvPowerSeries,
        PowerSeries.subst, subst_comp_subst_apply (PowerSeries.HasSubst.const
        (PowerSeries.HasSubst.X 0)) has_subst₁]
      apply subst_congr
      funext t
      rw [subst_X has_subst₁]
      simp [FormalGroup.add_aux]
    · simp [FormalGroup.add_aux]
      rw [←PowerSeries.subst, ←ScalarHom.subst_eq, PowerSeries.toMvPowerSeries,
        PowerSeries.subst, subst_comp_subst_apply (PowerSeries.HasSubst.const
        (PowerSeries.HasSubst.X 1)) has_subst₁]
      apply subst_congr
      rw [subst_X has_subst₁]
      simp [FormalGroup.add_aux]

  unfold F₂ at subst_aux₂ eq_aux
  /- use the uniqueness of the constructive lemma, we get the result. -/
  rw [h₂ _ (by simp [trunc_eq₁]) (ScalarHom.subst_eq π f g (a + b)), h₂ _ (by simp [eq_aux]) subst_aux₂]

-- Proposition 2.15.2
/-- For any `f, g, h` in LubinTate F, then `[a * b]_f, h = [a]_g, h ∘ [b]_f, g`-/
theorem multiplicative_of_ScalarHom (f g h : LubinTateF π) (a b : 𝒪[K]) :
  (ScalarHom π f h (a * b)).toFun = PowerSeries.subst (ScalarHom π f g b).toFun
  (ScalarHom π g h a).toFun := by
  obtain ⟨φ, h₁, h₂⟩ := constructive_lemma_poly π f h (a * b)
  obtain ⟨htrunc, hsubst⟩ := h₁
  obtain trunc_eq₁ := ScalarHom.PowerSeries_trunc_two π f h (a * b)
  obtain has_subst₁ := PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π f g b).zero_constantCoeff)
  obtain has_subst₂ :=  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_LubinTateF π f)
  obtain has_subst₃ :=  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_LubinTateF π g)
  obtain has_subst₄ := PowerSeries.HasSubst.of_constantCoeff_zero' (ScalarHom π g h a).zero_constantCoeff
  have trunc_eq₂ : PowerSeries.trunc 2 (PowerSeries.subst (ScalarHom π f g b).toFun
    (ScalarHom π g h a).toFun) = Polynomial.C a * Polynomial.C b * Polynomial.X := by
    rw [PowerSeries.trunc_of_subst_trunc' _ _ (ScalarHom π f g b).zero_constantCoeff,
      ScalarHom.PowerSeries_trunc_two π g h a]
    simp
    rw [←PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul has_subst₁, PowerSeries.subst_X has_subst₁,
      PowerSeries.smul_eq_C_mul, PowerSeries.trunc_C_mul, ScalarHom.PowerSeries_trunc_two π f g b]
    ring
  have subst_eq₁ : PowerSeries.subst (ScalarHom π f h (a * b)).toFun
    h.toFun = PowerSeries.subst f.toFun (ScalarHom π f h (a * b)).toFun := by
    exact ScalarHom.subst_eq π f h (a * b)
  have subst_eq₂ : PowerSeries.subst (PowerSeries.subst (ScalarHom π f g b).toFun
    (ScalarHom π g h a).toFun) h.toFun = PowerSeries.subst f.toFun (PowerSeries.subst
    (ScalarHom π f g b).toFun (ScalarHom π g h a).toFun) := by
    rw [←PowerSeries.subst_comp_subst_apply has_subst₄ has_subst₁, ScalarHom.subst_eq,
      PowerSeries.subst_comp_subst_apply has_subst₃ has_subst₁, ScalarHom.subst_eq,
      PowerSeries.subst_comp_subst_apply has_subst₁ has_subst₂]
  simp at h₂
  simp at trunc_eq₁
  obtain eq₁ := h₂ _ trunc_eq₁ subst_eq₁
  obtain eq₂ := h₂ _ trunc_eq₂ subst_eq₂
  rw [eq₁, eq₂]


/-- Given a Lubin Tate `f`, then `[1]_f,f = PowerSeries.X`-/
theorem ScalarHom_one (f : LubinTateF π): (ScalarHom π f f 1).toFun = PowerSeries.X := by
  obtain ⟨φ, h₁, h₂⟩ := constructive_lemma_poly π f f 1
  obtain ⟨htrunc, hsubst⟩ := h₁
  have eq_aux : PowerSeries.subst PowerSeries.X f.toFun
    = PowerSeries.subst f.toFun PowerSeries.X (R := 𝒪[K]) := by
    simp [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_LubinTateF π f)), ←PowerSeries.map_algebraMap_eq_subst_X]
  simp at h₂
  rw [h₂ _ (by simp [ScalarHom.PowerSeries_trunc_two]) (ScalarHom.subst_eq π f f 1),
    h₂ _ (by simp) eq_aux]


/- [π]_f, f = f -/
/-- For any two LubinTateF `f, g`, there exist a Formal Group isomorphism
  `α` from `F_f` to `F_g`. -/
theorem LubinTateFormalGroup_of_SameClass (f g : LubinTateF π) :
  ∃ (α : FormalGroupIso (LubinTateFormalGroup π f) (LubinTateFormalGroup π g)),
  PowerSeries.subst α.toHom.toFun g.toFun = PowerSeries.subst f.toFun α.toHom.toFun := by
  let α : FormalGroupIso (LubinTateFormalGroup π f) (LubinTateFormalGroup π g) := {
    toHom := ScalarHom π f g 1
    invHom := ScalarHom π g f 1
    left_inv := by
      refine (PowerSeries.subst_comp_eq_id_iff (ScalarHom π f g 1).toFun ?_ ?_).mpr ?_
      · exact PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π f g 1).zero_constantCoeff)
      · exact PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π g f 1).zero_constantCoeff)
      · rw [←multiplicative_of_ScalarHom]
        simp
        exact ScalarHom_one π f
    right_inv := by
      refine (PowerSeries.subst_comp_eq_id_iff (ScalarHom π g f 1).toFun ?_ ?_).mpr ?_
      · exact PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π g f 1).zero_constantCoeff)
      · exact PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π f g 1).zero_constantCoeff)
      · rw [←multiplicative_of_ScalarHom]
        simp
        exact ScalarHom_one π g

  }
  use α
  exact ScalarHom.subst_eq π f g 1



/-- For any two LubinTateF `f, g`, there exist a unique Formal Group strict
  isomorphism `α` from `F_f` to `F_g`. -/
theorem LubinTateFormalGroup_of_SameClass' (f g : LubinTateF π) :
  ∃! (α : FormalGroupStrictIso (LubinTateFormalGroup π f) (LubinTateFormalGroup π g)),
  PowerSeries.subst α.toHom.toFun g.toFun = PowerSeries.subst f.toFun α.toHom.toFun := by
  let α : FormalGroupStrictIso (LubinTateFormalGroup π f) (LubinTateFormalGroup π g) := {
    toHom := ScalarHom π f g 1
    invHom := ScalarHom π g f 1
    left_inv := by
      refine (PowerSeries.subst_comp_eq_id_iff (ScalarHom π f g 1).toFun ?_ ?_).mpr ?_
      · refine PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π f g 1).zero_constantCoeff)
      · refine PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π g f 1).zero_constantCoeff)
      · rw [←multiplicative_of_ScalarHom]
        simp
        exact ScalarHom_one π f
    right_inv := by
      refine (PowerSeries.subst_comp_eq_id_iff (ScalarHom π g f 1).toFun ?_ ?_).mpr ?_
      · refine PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π g f 1).zero_constantCoeff)
      · refine PowerSeries.HasSubst.of_constantCoeff_zero' ((ScalarHom π f g 1).zero_constantCoeff)
      · rw [←multiplicative_of_ScalarHom]
        simp
        exact ScalarHom_one π g
    one_coeff_one := by
      calc
        _ = Polynomial.coeff (PowerSeries.trunc 2 (ScalarHom π f g 1).toFun) 1 := by
          rw [PowerSeries.coeff_trunc, if_pos (by norm_num)]
        _ = 1 := by
          simp [ScalarHom.PowerSeries_trunc_two]
  }
  use α
  simp
  have trunc_striciso : ∀ (γ : FormalGroupStrictIso (LubinTateFormalGroup π f)
    (LubinTateFormalGroup π g)), PowerSeries.trunc 2 γ.toHom.toFun = Polynomial.X := by
    intro γ
    ext d
    norm_cast
    by_cases hd : d < 2
    · -- the case d < 2
      interval_cases d
      · rw [PowerSeries.coeff_trunc, if_pos hd]
        simp [γ.toHom.zero_constantCoeff]
      · rw [PowerSeries.coeff_trunc, if_pos hd]
        simp [γ.one_coeff_one]
    · -- the case d ≥ 2
      rw [PowerSeries.coeff_trunc, if_neg hd]
      simp [Polynomial.coeff_X]
      linarith
  constructor
  · exact ScalarHom.subst_eq π f g 1
  ·
    intro β hb
    have eq₁ : β.toHom = α.toHom := by
      apply FormalGroupHom.ext_iff.mpr
      obtain ⟨φ, h₁, h₂⟩ := constructive_lemma_poly π f g 1
      obtain ⟨htrunc, hsubst⟩ := h₁
      simp at h₂
      have subst_eq₂ : PowerSeries.subst α.toHom.toFun g.toFun = PowerSeries.subst f.toFun
        α.toHom.toFun := ScalarHom.subst_eq π f g 1
      rw [h₂ _ (trunc_striciso _) hb, h₂ _ (trunc_striciso _) subst_eq₂]
    exact (FormalGroupStrictIso.ext_iff' _ _ _ _ ).mpr eq₁


-- formalize the Corollary 2.17, give the definition of `End(F_f)`

-- #lint

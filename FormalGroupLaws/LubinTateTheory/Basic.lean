module

public import FormalGroupLaws.Basic
public import FormalGroupLaws.LubinTateTheory.ConstructiveLem
public import FormalGroupLaws.AddInverse

@[expose] public section

noncomputable section

open ValuativeRel MvPowerSeries Classical Finsupp

namespace FormalGroup.LubinTate

section

variable {K σ : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {π : (valuation K).Uniformizer}

variable (f g h : LubinTate.𝓕 π)

name_power_vars X₀, X₁, X₂ over 𝒪[K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
lemma L_one : (L (equivFunOnFinite.symm (1 : Fin 2 → 𝒪[K]))).toMvPowerSeries = X 0 + X 1 := by
  simp [L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
-- @[simp]
lemma L_one' :
    (L (equivFunOnFinite.symm (1 : Fin 2 → 𝒪[K]))) = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  simp [L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
lemma L_two : (L (equivFunOnFinite.symm (1 : Fin 3 → 𝒪[K]))) = MvPolynomial.X 0 +
    MvPolynomial.X 1 + MvPolynomial.X 2 := by
  simp [L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum, Fin.sum_univ_three]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
lemma L_single {a : 𝒪[K]} : (L (single () a)) = a • MvPolynomial.X () := by
  simp [L, MvPolynomial.sumSMulX]

lemma assoc_truncTotal_left :
    let Φ := Phi f f (equivFunOnFinite.symm 1)
    (Φ.subst ![Φ.subst ![X₀, X₁], X₂]).truncTotal 2 =
      (Phi f f (equivFunOnFinite.symm 1)).truncTotal 2 := by
  intro Φ
  have : Φ = Phi f f (equivFunOnFinite.symm 1) := rfl
  rw [this, truncTotal_subst, Phi_truncTotal_two, L_one]
  have aux : (fun i ↦ ((truncTotal 2) (![subst ![X₀, X₁]
    (Phi f f (equivFunOnFinite.symm 1)), X₂] i)).toMvPowerSeries) = ![X₀ + X₁, X₂] := by
    funext i; fin_cases i
    · simp [truncTotal_subst_eq_truncTotal_left, Phi_truncTotal_two, L_one,
        subst_add HasSubst.X_X, subst_X HasSubst.X_X]
    · simp
  · simp [aux, subst_add, hasSubst_of_constantCoeff_zero, Phi_truncTotal_two, L_two]
  · simp [constantCoeff_subst_eq_zero, hasSubst_of_constantCoeff_zero]

lemma assoc_truncTotal_right :
    let Φ := Phi f f (equivFunOnFinite.symm 1)
    (Φ.subst ![X₀, Φ.subst ![X₁, X₂]]).truncTotal 2 =
      (Phi f f (equivFunOnFinite.symm 1)).truncTotal 2 := by
  intro Φ
  have : Φ = Phi f f (equivFunOnFinite.symm 1) := rfl
  rw [this, truncTotal_subst, Phi_truncTotal_two, L_one]
  have aux : (fun i ↦ ↑((truncTotal 2) (![X₀, subst ![X₁, X₂]
    (Phi f f (equivFunOnFinite.symm 1))] i))) = ![X₀, X₁ + X₂] := by
    funext i; fin_cases i
    · simp
    · simp [truncTotal_subst_eq_truncTotal_left, Phi_truncTotal_two, L_one,
        subst_add HasSubst.X_X, subst_X HasSubst.X_X]
  · simp [aux, subst_add, Phi_truncTotal_two, L_two, subst_X, hasSubst_of_constantCoeff_zero,
      _root_.add_assoc]
  · simp [constantCoeff_subst_eq_zero, hasSubst_of_constantCoeff_zero]

lemma f_Phi_eq_Phi_f {p q : MvPowerSeries σ 𝒪[K]} (h : HasSubst ![p, q]) :
    let Φ := Phi f f (equivFunOnFinite.symm 1)
    f.toPowerSeries.subst (Φ.subst ![p, q]) =
      Φ.subst ![f.toPowerSeries.subst p, f.toPowerSeries.subst q] := by
  intro _
  rw [PowerSeries.subst, ← subst_comp_subst_apply _ h, ← PowerSeries.subst,
    constructive_lemma f f (equivFunOnFinite.symm 1), subst_comp_subst_apply _ h]
  congr! 2 with i
  fin_cases i <;> simp [PowerSeries.toMvPowerSeries_val _ h]
  · exact PowerSeries.HasSubst.toMvPowerSeries constantCoeff_F
  · exact hasSubst_of_constantCoeff_zero (congrFun rfl)

lemma subst_left :
    let Φ := Phi f f (equivFunOnFinite.symm 1)
    let Φ₁ := Φ.subst ![Φ.subst ![X₀, X₁], X₂]
    f.toPowerSeries.subst Φ₁ = Φ₁.subst (f.toPowerSeries.toMvPowerSeries · ) := by
  intro Φ Φ₁
  obtain h1 := PowerSeries.HasSubst.toMvPowerSeries (σ := Fin 3) (constantCoeff_F (f := f))
  rw [f_Phi_eq_Phi_f f (HasSubst.cons_subst_zero_left _ _ _ rfl), f_Phi_eq_Phi_f f (HasSubst.X_X), subst_comp_subst_apply
    (HasSubst.cons_subst_zero_left _ _ _ rfl) h1]
  congr! 2 with i
  fin_cases i
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
    rw [subst_comp_subst_apply HasSubst.X_X h1]
    congr! 2 with j
    fin_cases j <;>
    simp [← PowerSeries.toMvPowerSeries_apply, subst_X, h1]
  · simp [← PowerSeries.toMvPowerSeries_apply, subst_X, h1]

lemma subst_right :
    let Φ := Phi f f (equivFunOnFinite.symm 1)
    let Φ₁ := Φ.subst ![X₀, Φ.subst ![X₁, X₂]]
    f.toPowerSeries.subst Φ₁ = Φ₁.subst (f.toPowerSeries.toMvPowerSeries · ) := by
  intro Φ Φ₁
  obtain h1 := PowerSeries.HasSubst.toMvPowerSeries (σ := Fin 3) (constantCoeff_F (f := f))
  rw [f_Phi_eq_Phi_f f (HasSubst.cons_subst_zero_right _ _ _ rfl), f_Phi_eq_Phi_f f (HasSubst.X_X), subst_comp_subst_apply
    (HasSubst.cons_subst_zero_right _ _ _ rfl) h1]
  congr! 2 with i
  fin_cases i
  · simp [← PowerSeries.toMvPowerSeries_apply, subst_X, h1]
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, subst_comp_subst_apply HasSubst.X_X h1]
    congr! 2 with j
    fin_cases j <;>
    simp [← PowerSeries.toMvPowerSeries_apply, subst_X, h1]

/-- Lubin-Tate formal group law related to `f : 𝓕 π`, namely a multivariate power series $F$
with two variable such that $f(F(X,Y)) = F(f(X), f(Y))$. -/
def formalGroup : FormalGroup 𝒪[K] where
  toPowerSeries := Phi f f (equivFunOnFinite.symm 1)
  zero_constantCoeff := LubinTate.constantCoeff_Phi ..
  lin_coeff_X := calc
    _ = ((LubinTate.Phi f f (equivFunOnFinite.symm 1)).truncTotal 2).coeff
      (single (0 : Fin 2) 1) := by simp [coeff_truncTotal_eq_ite]
    _ = _ := by
      simp [Phi_truncTotal_two, L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]
  lin_coeff_Y := calc
    _ = ((LubinTate.Phi f f (equivFunOnFinite.symm 1)).truncTotal 2).coeff
      (single (1 : Fin 2) 1) := by simp [coeff_truncTotal_eq_ite]
    _ = _ := by
      simp [Phi_truncTotal_two, L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]
  assoc := by
    rw [constructive_lemma_unique _ _ _ (assoc_truncTotal_left f) (subst_left f),
      constructive_lemma_unique _ _ _ (assoc_truncTotal_right f) (subst_right f)]

local notation "F" => formalGroup

lemma formalGroup_apply : (F f).toPowerSeries = Phi f f (equivFunOnFinite.symm 1) := rfl

/-- The power series `f : 𝓕 π` is a formal group homomorphism of the Lubin-Tate formal
  group law `F f` associated to `f : 𝓕 π` -/
def LT_hom : FormalGroupHom (F f) (F f) where
  toPowerSeries := f.toPowerSeries
  zero_constantCoeff := constantCoeff_F
  hom := constructive_lemma f f _

lemma self_hom_apply :
    PowerSeries.subst (Phi f f (equivFunOnFinite.symm (1 : Fin 2 → 𝒪[K]))) f.toPowerSeries =
      subst (fun x ↦ (PowerSeries.toMvPowerSeries x) f.toPowerSeries)
        (Phi f f (equivFunOnFinite.symm 1)) := (LT_hom f).hom

instance : (F f).IsComm where
  comm := by
    rw [formalGroup_apply]
    have aux : HasSubst fun x : Fin 2 ↦ (PowerSeries.toMvPowerSeries x) f.toPowerSeries :=
      PowerSeries.HasSubst.toMvPowerSeries constantCoeff_F
    refine (constructive_lemma_unique f f (equivFunOnFinite.symm 1) ?_ ?_).symm
    · simp [Phi_truncTotal_two, L_one', truncTotal_subst_eq_truncTotal_left, Phi_truncTotal_two,
        subst_add, HasSubst.X_X, _root_.add_comm]
    · rw [PowerSeries.subst, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
        (congrFun rfl)) HasSubst.X_X, ← PowerSeries.subst, self_hom_apply,
          subst_comp_subst_apply aux HasSubst.X_X, subst_comp_subst_apply HasSubst.X_X aux]
      congr! 2 with i
      fin_cases i
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero]
        rw [subst_X aux, PowerSeries.toMvPowerSeries_val _ HasSubst.X_X, PowerSeries.toMvPowerSeries_apply]
        simp
      · simp
        rw [subst_X aux, PowerSeries.toMvPowerSeries_val _ HasSubst.X_X, PowerSeries.toMvPowerSeries_apply]
        simp

variable {a : 𝒪[K]}

lemma SMul_trunc_two : PowerSeries.trunc 2 (Phi f g (single () a)) = a • Polynomial.X := by
  ext n : 1
  by_cases hn : n < 2
  · rw [PowerSeries.coeff_trunc, if_pos hn, PowerSeries.coeff]
    calc
      _ = MvPolynomial.coeff (single () n) ((Phi f g (single () a)).truncTotal 2) := by
        simp [coeff_truncTotal_eq_ite, hn]
      _ = _ := by
        rw [Phi_truncTotal_two, L_single]
        simp [Polynomial.coeff_X]
        grind
  have : 1 ≠ n := by grind
  simp [PowerSeries.coeff_trunc, hn, Polynomial.coeff_X, this]

lemma SMul_truncTotal_left :
    (PowerSeries.subst (F g).toPowerSeries (Phi f g (single () a))).truncTotal 2 =
      a • (MvPolynomial.X 0 + MvPolynomial.X 1) := by
  simp [PowerSeries.truncTotal_subst_eq_trunc, SMul_trunc_two, PowerSeries.subst_smul,
    PowerSeries.subst_X, (F g).truncTotal_two, PowerSeries.HasSubst, (F g).zero_constantCoeff]


lemma SMul_truncTotal_left' :
    (PowerSeries.subst (F g).toPowerSeries (Phi f g (single () a))).truncTotal 2 =
      (Phi f g (equivFunOnFinite.symm ![a, a])).truncTotal 2 := by
  rw [SMul_truncTotal_left, Phi_truncTotal_two]
  by_cases ha : a = 0
  · subst ha
    have hsupp : (Function.support ![(0 : 𝒪[K]), 0]).toFinset = ∅ := by simp
    simp [hsupp, L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]
  · have hsupp : (Function.support ![a, a]).toFinset = Finset.univ := by
      ext i; fin_cases i <;> simp [Function.mem_support, ha]
    simp [hsupp, L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]

lemma SMul_truncTotal_right :
    ((F f).toPowerSeries.subst fun x ↦ PowerSeries.toMvPowerSeries x
      (Phi f g (single () a))).truncTotal 2 = a • (MvPolynomial.X 0 + MvPolynomial.X 1) := by
  have : HasSubst fun (x : Fin 2) ↦ (PowerSeries.toMvPowerSeries x) (Phi f g (single () a)) := by
    apply PowerSeries.HasSubst.toMvPowerSeries
    rw [PowerSeries.constantCoeff, constantCoeff_Phi]
  rw [truncTotal_subst_eq_truncTotal_left _, (F f).truncTotal_two]
  simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X, smul_add]
  rw [subst_add this, subst_X this, subst_X this, map_add, PowerSeries.toMvPowerSeries_apply,
    PowerSeries.toMvPowerSeries_apply, PowerSeries.truncTotal_subst_eq_trunc (constantCoeff_X _),
      PowerSeries.truncTotal_subst_eq_trunc (constantCoeff_X _) (f := Phi f g _), SMul_trunc_two]
  simp [PowerSeries.subst_smul, PowerSeries.subst_X, truncTotal_X_of_lt]
  · simp [PowerSeries.constantCoeff_toMvPowerSeries, PowerSeries.constantCoeff]

lemma SMul_truncTotal_right' :
    ((F f).toPowerSeries.subst fun x ↦ PowerSeries.toMvPowerSeries x
      (Phi f g (single () a))).truncTotal 2 =
        (Phi f g (equivFunOnFinite.symm ![a, a])).truncTotal 2 := by
  rw [SMul_truncTotal_right, Phi_truncTotal_two]
  by_cases ha : a = 0
  · subst ha
    have hsupp : (Function.support ![(0 : 𝒪[K]), 0]).toFinset = ∅ := by simp
    simp [hsupp, L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]
  · have hsupp : (Function.support ![a, a]).toFinset = Finset.univ := by
      ext i; fin_cases i <;> simp [Function.mem_support, ha]
    simp [hsupp, L, MvPolynomial.sumSMulX, linearCombination, Finsupp.sum]

/-- For any multivariate power series `p` with property `PowerSeries.HasSubst p`, we have that
`f ∘ [a]_{f,g} ∘ p = [a]_{f,g} g ∘ p`. -/
lemma SMul_subst_aux {p : MvPowerSeries σ 𝒪[K]} (hp : PowerSeries.HasSubst p) :
    f.toPowerSeries.subst (PowerSeries.subst p (Phi f g (single () a))) =
      PowerSeries.subst (g.toPowerSeries.subst p) (Phi f g (single () a)) := by
  have := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_F (f := g))
  rw [← PowerSeries.subst_comp_subst_apply _ hp, constructive_lemma,
    ← PowerSeries.subst_comp_subst_apply this hp]
  congr; funext _
  rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.subst, subst_self, id]
  · exact PowerSeries.HasSubst.of_constantCoeff_zero' rfl

lemma SMul_subst_left :
    let Φ := PowerSeries.subst (F g).toPowerSeries (Phi f g (single () a))
    f.toPowerSeries.subst Φ = Φ.subst (g.toPowerSeries.toMvPowerSeries · ) := by
  intro Φ
  /- can we avoid erw here. `self_hom_apply` need erw -/
  rw (transparency := .default) [SMul_subst_aux, self_hom_apply]
  rw [PowerSeries.subst, ← subst_comp_subst_apply]
  congr
  · exact hasSubst_of_constantCoeff_zero (congrFun rfl)
  · exact PowerSeries.HasSubst.toMvPowerSeries constantCoeff_F
  · exact PowerSeries.HasSubst.of_constantCoeff_zero rfl

lemma SMul_subst_right :
    let Φ := (F f).toPowerSeries.subst fun x ↦ PowerSeries.toMvPowerSeries x (Phi f g (single () a))
    f.toPowerSeries.subst Φ = Φ.subst (g.toPowerSeries.toMvPowerSeries ·) := by
  have aux : HasSubst fun (x : Fin 2) ↦ PowerSeries.toMvPowerSeries x (Phi f g (single () a)) :=
    PowerSeries.HasSubst.toMvPowerSeries rfl
  have {f : 𝓕 π} := PowerSeries.HasSubst.toMvPowerSeries (constantCoeff_F (f := f)) (σ := Fin 2)
  intro Φ
  rw [PowerSeries.subst, ← subst_comp_subst_apply _ aux, ← PowerSeries.subst]
  erw [self_hom_apply]
  rw [subst_comp_subst_apply this aux, subst_comp_subst_apply aux this]
  congr! 2 with i
  · rw [PowerSeries.toMvPowerSeries_val _ aux, PowerSeries.toMvPowerSeries_val _ this,
      PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply, SMul_subst_aux _ _
        (PowerSeries.HasSubst.X i)]
  · exact hasSubst_of_constantCoeff_zero (congrFun rfl)

variable (a) in
/-- For all `f, g ∈ F_π` there is a unique power series`[a]_f,g` such that
`PowerSeries.trunc 2 [a]_f,g = a * X` and `f ∘ [a]_f,g = [a]_f,g ∘ g`, and this
`[a]_f,g` turn out to be a formal group homomorphim from `F_g` to `F_f`. -/
def SMul : FormalGroupHom (F g) (F f) where
  toPowerSeries := Phi f g (single () a)
  zero_constantCoeff := constantCoeff_Phi _ _ _
  hom := by
    rw [constructive_lemma_unique _ _ _ (SMul_truncTotal_left' f g) (SMul_subst_left f g),
      constructive_lemma_unique _ _ _ (SMul_truncTotal_right' f g) (SMul_subst_right f g)]

@[simp]
lemma SMul_apply : (SMul f g a).toPowerSeries = Phi f g (single () a) := rfl

/-- Local notation for scalar multiplication of Lubin-Tate formal group law,
`[a]_ f g`. -/
local notation "[" a "]_" => fun f g => SMul f g a

-- local notation "[" a "]" => fun f => SMul f f a

lemma SMul_pi : (SMul f f π).toPowerSeries = f.toPowerSeries := by
  rw [SMul_apply, ← constructive_lemma_unique f f (single () π)]
  · rw [Phi_truncTotal_two, L_single, ← PowerSeries.trunc_eq_truncTotal, f.trunc_two]
    simp [MvPolynomial.smul_eq_C_mul]
  · rw [PowerSeries.subst]
    congr! 2
    rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.subst, subst_self, id]

lemma SMul_one : (SMul f f 1).toPowerSeries = .X := by
  rw [SMul_apply, ← constructive_lemma_unique f f (single () 1)]
  · rw [PowerSeries.X, truncTotal_X_of_lt one_lt_two, Phi_truncTotal_two, L_single, one_smul]
  have : HasSubst fun (x : Unit) ↦ (PowerSeries.toMvPowerSeries x) f.toPowerSeries :=
    PowerSeries.HasSubst.toMvPowerSeries constantCoeff_F
  rw [PowerSeries.X, subst_X this, PowerSeries.subst, subst_self, id,
    PowerSeries.toMvPowerSeries_apply, PowerSeries.subst, subst_self, id]

variable {b : 𝒪[K]}

/-- $[a]_{f,g} ∘ [b]_{g,h} = [ab]_{f,h}$. -/
lemma SMul_tower : PowerSeries.subst ([b]_ g h).toPowerSeries ([a]_ f g).toPowerSeries =
    ([a * b]_ f h).toPowerSeries := by
  simp only [SMul_apply]
  refine constructive_lemma_unique f h _ ?_ ?_
  · have : PowerSeries.HasSubst (Phi g h (single () b)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' rfl
    rw [PowerSeries.truncTotal_subst_eq_trunc rfl, SMul_trunc_two]
    ext n
    simp [PowerSeries.subst_smul, map_smul, PowerSeries.subst_X,
      ← PowerSeries.trunc_eq_truncTotal, ← PowerSeries.trunc_eq_truncTotal,
        SMul_trunc_two, mul_assoc]
  conv_rhs =>
    rw [PowerSeries.subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (congrFun rfl))
      (PowerSeries.HasSubst.toMvPowerSeries constantCoeff_F)]
  rw [SMul_subst_aux _ _ (PowerSeries.HasSubst.of_constantCoeff_zero' rfl), PowerSeries.subst,
    constructive_lemma]

lemma SMul_add : ([a + b]_ f g).toPowerSeries =
    (F f).toPowerSeries.subst ![([a]_ f g).toPowerSeries, ([b]_ f g).toPowerSeries] := by
  simp only [SMul_apply, formalGroup_apply]
  have : HasSubst ![Phi f g (single () a), Phi f g (single () b)] :=
    hasSubst_of_constantCoeff_zero <| by simpa using ⟨rfl, rfl⟩
  refine (constructive_lemma_unique f g _ ?_ ?_).symm
  · rw [truncTotal_subst_eq_truncTotal_left, Phi_truncTotal_two, L_one, subst_add this,
      subst_X this, subst_X this, Phi_truncTotal_two, L_single]
    simp [Phi_truncTotal_two, L_single, add_smul]
    · simpa using ⟨rfl, rfl⟩
  rw [PowerSeries.subst, ← subst_comp_subst_apply _ this, ← PowerSeries.subst, self_hom_apply,
    subst_comp_subst_apply _ this, subst_comp_subst_apply this _]
  congr! 2 with i
  fin_cases i <;> simp [← constructive_lemma, PowerSeries.toMvPowerSeries_val _ this]
  · exact PowerSeries.HasSubst.toMvPowerSeries constantCoeff_F
  · exact PowerSeries.HasSubst.toMvPowerSeries constantCoeff_F
  · exact hasSubst_of_constantCoeff_zero (congrFun rfl)

end

section

variable {K σ : Type*} [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]


variable {π : (valuation K).Uniformizer} (f : 𝓕 π)

local notation "F" => formalGroup

-- instance : NonUnitalCommSemiring R := inferInstance

-- instance : NonUnitalCommRing 𝓂[K] := inferInstance

/- here we need to generalize this `MvPowerSeries.HasEval` to
`NonUnitalCommRing`. And we can start with generalizing `MvPolynomial.eval` to
`NonUnitalCommSemiring`. -/

instance : IsLinearTopology 𝒪[K] 𝒪[K] := by
  let I : (ValueGroupWithZero K)ˣ → Ideal 𝒪[K] := fun γ ↦
    { carrier := {x | valuation K (((x : 𝒪[K]) : K)) < γ}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change valuation K (((x + y : 𝒪[K]) : K)) < γ
        simpa using (valuation K).map_add_lt hx hy
      smul_mem' := by
        intro c x hx
        change valuation K (((c * x : 𝒪[K]) : K)) < γ
        simpa [map_mul] using mul_lt_of_le_one_of_lt c.2 hx }
  refine IsLinearTopology.mk_of_hasBasis (R := 𝒪[K]) (M := 𝒪[K])
    (S := Ideal 𝒪[K]) (p := fun _ : (ValueGroupWithZero K)ˣ ↦ True) (s := I) ?_
  rw [nhds_subtype_eq_comap]
  exact (IsValuativeTopology.hasBasis_nhds_zero K).comap ((↑) : 𝒪[K] → K)

omit [IsUniformAddGroup K] in
lemma PowerSeries.hasEval_of_mem_maximalIdeal (x : 𝓂[K]) :
    PowerSeries.HasEval (x : 𝒪[K]) := by
  have hz : valuation K (((x : 𝒪[K]) : K)) < 1 :=
    (Valuation.mem_maximalIdeal_iff K (valuation K)).mp x.2
  rw [PowerSeries.hasEval_def, IsTopologicallyNilpotent, tendsto_subtype_rng]
  change Filter.Tendsto (fun n : ℕ ↦ (((x : 𝒪[K]) : K) ^ n))
    Filter.atTop (nhds (0 : K))
  rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hz γ
  refine Filter.eventually_atTop.mpr ⟨n, fun m hm ↦ ?_⟩
  simpa [map_pow] using (pow_le_pow_right_of_le_one' hz.le hm).trans_lt hn

omit [IsUniformAddGroup K] in
lemma MvPowerSeries.hasEval_of_forall_mem_maximalIdeal [Finite σ] {a : σ → 𝒪[K]}
    (ha : ∀ i, a i ∈ 𝓂[K]) :
    HasEval a := by
  refine { hpow := ?_, tendsto_zero := ?_ }
  · intro i
    exact PowerSeries.hasEval_of_mem_maximalIdeal ⟨a i, ha i⟩
  · rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot


lemma MvPowerSeries.aeval_mem_maximalIdeal_of_constantCoeff_eq_zero [Finite σ]
    {G : MvPowerSeries σ 𝒪[K]} (hG : G.constantCoeff = 0)
    {a : σ → 𝒪[K]} (ha : ∀ i, a i ∈ 𝓂[K]) :
    G.aeval (MvPowerSeries.hasEval_of_forall_mem_maximalIdeal ha) ∈ 𝓂[K] := by
  rw [MvPowerSeries.aeval_eq_sum]
  refine tsum_mem (IsNoetherianRing.isClosed_ideal (𝓂[K])) fun d ↦ ?_
  by_cases hd : d = 0
  · subst hd
    change (MvPowerSeries.coeff 0 G) • (1 : 𝒪[K]) ∈ 𝓂[K]
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff, hG]
    simp
  · have hprod : d.prod (fun s e ↦ (a s) ^ e) ∈ 𝓂[K] := by
      obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
        by_contra h
        apply hd
        ext i
        by_contra hi
        exact h ⟨i, hi⟩
      exact (𝓂[K]).prod_mem (Finsupp.mem_support_iff.mpr hi)
        ((𝓂[K]).pow_mem_of_mem (ha i) (d i) (Nat.pos_of_ne_zero hi))
    simpa [smul_eq_mul] using Ideal.mul_mem_left (𝓂[K]) (MvPowerSeries.coeff d G) hprod

set_option linter.unusedVariables false in
def Point (f : 𝓕 π) := 𝓂[K]

omit [IsUniformAddGroup K] in
lemma pointPair_apply_mem_maximalIdeal (x y : Point f) :
    ∀ i, ![(x : 𝒪[K]), y] i ∈ 𝓂[K] :=
  fun i => by fin_cases i <;> simp

instance : Add (Point f) where
  add x y :=
    ⟨(F f).toPowerSeries.aeval
        (MvPowerSeries.hasEval_of_forall_mem_maximalIdeal (pointPair_apply_mem_maximalIdeal f x y)),
      MvPowerSeries.aeval_mem_maximalIdeal_of_constantCoeff_eq_zero
        (F f).zero_constantCoeff (pointPair_apply_mem_maximalIdeal f x y)⟩

instance : Zero (Point f) where
  zero := ⟨0, Submodule.zero_mem _⟩

instance : Neg (Point f) where
  neg x := by
    have : PowerSeries.HasEval (x : 𝒪[K]) := by
      refine IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp ?_
      sorry
    refine ⟨(F f).addInv_X.aeval this,
      ?_⟩
    rw [PowerSeries.aeval]
    exact MvPowerSeries.aeval_mem_maximalIdeal_of_constantCoeff_eq_zero rfl
      fun _ ↦ Submodule.coe_mem x

instance : AddCommGroup (Point f) := sorry

instance : Module 𝒪[K] (Point f) where
  smul := sorry
  mul_smul := sorry
  one_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

end

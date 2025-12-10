import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
import FormalGroupLaws.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.Data.Finsupp.Weight

variable {R S: Type*} [CommRing R] [CommRing S] {σ τ: Type*} {I : Ideal R} [DecidableEq σ] {n : ℕ}
  [DecidableEq τ] [Algebra R S]

open MvPowerSeries
open scoped WithPiTopology

/- Given a ideal `I` of commutative ring `R`, then multivariate power series with coefficient in
`I`, forms a ideal of ring of multivariate power series over `R`. -/
def Ideal.MvPowerSeries : Ideal (MvPowerSeries σ R) where
  carrier := {p | ∀ n, p n ∈ I}
  add_mem' := fun ha hb n => add_mem (ha n) (hb n)
  zero_mem' := fun _ => (Submodule.Quotient.mk_eq_zero I).mp rfl
  smul_mem' := fun c {_} hx _ ↦
    I.sum_mem <| fun d _ => mul_mem_left I ((coeff d.1) c) (hx d.2)

omit [DecidableEq σ] in
lemma MvPowerSeries.mul_mem_mul {a b : MvPowerSeries σ R} {J : Ideal R}
    (ha : a ∈ I.MvPowerSeries) (hb : b ∈ J.MvPowerSeries) :
    a * b ∈ (I * J).MvPowerSeries :=
  fun _ ↦ (I * J).sum_mem  <| fun d _ => Submodule.mul_mem_mul (ha d.1) (hb d.2)

section ToSubring

variable {σ : Type*} (p : MvPowerSeries σ R) (T : Subring R)

/-- Given a multivariate formal power series `p` and a subring `T` that contains the
 coefficients of `p`,return the corresponding multivariate formal power series
 whose coefficients are in `T`. -/
def MvPowerSeries.toSubring (hp : ∀ n, p n ∈ T) : MvPowerSeries σ T := fun n => ⟨p n, hp n⟩

variable (hp : ∀ n, p n ∈ T)

@[simp]
theorem coeff_toSubring {n : σ →₀ ℕ} : ↑((toSubring p T hp).coeff n) = p.coeff n := rfl

@[simp]
theorem constantCoeff_toSubring : ↑(toSubring p T hp).constantCoeff =
  p.constantCoeff := rfl

/-- Given a multivariate formal power series whose coefficients are in some subring, return
the multivariate formal power series whose coefficients are in the ambient ring. -/
def MvPowerSeries.ofSubring (p : MvPowerSeries σ T) : MvPowerSeries σ R :=
  fun n => (p n : R)

def PowerSeries.ofSubring (p : PowerSeries T) : PowerSeries R :=
  fun n => (p n : R)

@[simp]
theorem coeff_ofSubring {n : σ →₀ ℕ} (p : MvPowerSeries σ T) : (ofSubring T p).coeff n = p.coeff n
  := rfl

variable (F : FormalGroup R)

-- lemma subst_aux (hp : ∀ n, p n ∈ T) : ∀ n, (HasSubst n) → subst n p = subst n (p.toSubring T hp) := by
--   sorry

/- If `F` is a formal group with coefficient in `T`, where `T` is a subring of `R`, then
  `F` is a formal group with coefficient in `R`.-/
def FormalGroup.ofSubring : FormalGroup T → FormalGroup R := fun F => F.map (Subring.subtype T)


def FormalGroup.toSubring (hF : ∀ n, F.toFun n ∈ T) : FormalGroup T where
  toFun := F.toFun.toSubring _ hF
  zero_constantCoeff := by
    rw [← @coeff_zero_eq_constantCoeff_apply]
    have aux : (coeff 0) (F.toFun.toSubring T hF) = (0 : R) := by
      rw [@coeff_toSubring]
      simp [F.zero_constantCoeff]
    norm_cast at aux
  lin_coeff_X := by
    have aux : (coeff (Finsupp.single 0 1)) (F.toFun.toSubring T hF) = (1 : R) := by
      rw [coeff_toSubring]
      simp [F.lin_coeff_X]
    norm_cast at aux
  lin_coeff_Y:= by
    have aux : (coeff (Finsupp.single 1 1)) (F.toFun.toSubring T hF) = (1 : R) := by
      rw [coeff_toSubring]
      simp [F.lin_coeff_Y]
    norm_cast at aux
  assoc := by
    have coeff_mem_aux (s : Fin 3): ∀ n, (X s (R := R)) n ∈ T := by
      intro n; rw [←coeff_apply (X s), coeff_X]; split_ifs <;> simp
    have eq_aux (s : Fin 3) : (X s (R := R)).toSubring _ (coeff_mem_aux s) = (X s (R := T)) := by
      ext n; rw [coeff_X]; split_ifs with h <;> simp [coeff_X, h]
    have aux' {h : T} : (algebraMap (↥T.toSubsemiring) R) h =
      (algebraMap (↥T.toSubsemiring) R).toAddMonoidHom h := rfl
    have has_subst_aux₀ : HasSubst ![subst ![Y₀ (R := T), Y₁] (F.toFun.toSubring T hF), Y₂] :=
      has_subst_aux₁ <| (Subring.coe_eq_zero_iff T).mp <| by simp [F.zero_constantCoeff]
    have has_subst_aux₀' : HasSubst ![Y₀ (R := T), subst ![Y₁, Y₂] (F.toFun.toSubring T hF)] :=
      has_subst_aux₂ <| (Subring.coe_eq_zero_iff T).mp <| by simp [F.zero_constantCoeff]
    have has_subst_aux' : HasSubst ![(X 1).toSubring T (coeff_mem_aux 1), Y₂] :=
      HasSubst.FinPairing ((Subring.coe_eq_zero_iff T).mp <| by simp) (constantCoeff_X _)
    ext n
    calc
      _ = (coeff n) (subst ![subst ![Y₀, Y₁] F.toFun, Y₂] F.toFun) := by
        rw [coeff_subst <| has_subst_aux₁ F.zero_constantCoeff, coeff_subst has_subst_aux₀]
        obtain h₁ := coeff_subst_finite has_subst_aux₀ (F.toFun.toSubring T hF) n
        rw [← @Algebra.algebraMap_ofSubsemiring_apply, aux', AddMonoidHom.map_finsum (algebraMap
          (↥T.toSubsemiring) R).toAddMonoidHom h₁]
        simp [Algebra.algebraMap_ofSubsemiring_apply]
        congr! 3 with i
        · simp [coeff_mul, coeff_mul]
          congr with j
          congr
          · simp [coeff_pow, coeff_pow]
            congr! 2 with x_1 x_2 x_3 x_4
            obtain h₂ := coeff_subst_finite (has_subst_XY (R := T)) (F.toFun.toSubring T hF)
              (x_1 x_3)
            rw [← @Algebra.algebraMap_ofSubsemiring_apply, @coeff_apply,
              aux', ←coeff_apply (subst ![Y₀, Y₁] (F.toFun.toSubring T hF)) (x_1 x_3),
              coeff_subst has_subst_XY,
              AddMonoidHom.map_finsum (algebraMap (↥T.toSubsemiring) R).toAddMonoidHom h₂]
            simp [Algebra.algebraMap_ofSubsemiring_apply]
            rw [coeff_subst (has_subst_XY (R := R))]
            apply finsum_congr
            intro x'
            rw [Y₀, ←eq_aux 0, Y₁, ← eq_aux 1,]
            simp [coeff_mul, coeff_pow]
          · simp [Y₂, ←eq_aux 2, coeff_pow, coeff_pow]
      _ = _ := by
        obtain h₁ := coeff_subst_finite has_subst_aux₀' (F.toFun.toSubring T hF) n
        rw [F.assoc, coeff_subst <| has_subst_aux₂ F.zero_constantCoeff,
          coeff_subst has_subst_aux₀', ← @Algebra.algebraMap_ofSubsemiring_apply, aux',
          AddMonoidHom.map_finsum (algebraMap (↥T.toSubsemiring) R).toAddMonoidHom h₁]
        simp [Algebra.algebraMap_ofSubsemiring_apply]
        congr! 3 with d
        simp [coeff_mul]
        congr! 1 with x_1 x_2
        rw [Y₀, Y₀,  ←eq_aux 0, Y₁, Y₁, ←eq_aux 1]
        simp [coeff_pow]
        congr! 3 with x_1 x_2 x_3 x_4
        obtain h₂ := coeff_subst_finite has_subst_aux' (F.toFun.toSubring T hF) (x_1 x_3)
        rw [coeff_subst has_subst_YZ, coeff_subst has_subst_aux',
          ← @Algebra.algebraMap_ofSubsemiring_apply, aux',
          AddMonoidHom.map_finsum (algebraMap (↥T.toSubsemiring) R).toAddMonoidHom h₂]
        simp [Algebra.algebraMap_ofSubsemiring_apply]
        congr! 3 with d
        simp [coeff_mul]
        rw [Y₂, Y₂, ←eq_aux 2]
        simp [coeff_pow]

end ToSubring

lemma PowerSeries.constantCoeff_subst_X {f : PowerSeries R} (hf : constantCoeff f = 0) {s : σ} :
    MvPowerSeries.constantCoeff (subst (MvPowerSeries.X s (R := R)) f) = 0 := by
  rw [PowerSeries.constantCoeff_subst <| HasSubst.X s]
  apply finsum_eq_zero_of_forall_eq_zero <| fun d => by
    if hd : d = 0 then simp [hd, hf]
    else
    rw [MvPowerSeries.X, MvPowerSeries.monomial_pow, ←MvPowerSeries.coeff_zero_eq_constantCoeff,
      MvPowerSeries.coeff_monomial, if_neg <| Finsupp.ne_iff.mpr <| ⟨s, by simp [Ne.symm hd]⟩]
    simp

omit [Algebra R S] in
@[simp]
theorem PowerSeries.constantCoeff_map (f : R →+* S) (φ : PowerSeries R) :
    constantCoeff (map f φ) = f (constantCoeff φ) := rfl

omit [DecidableEq σ]
lemma tsum_subst {x : ℕ → PowerSeries R} {g: MvPowerSeries σ R} [UniformSpace R] [T2Space R]
    [DiscreteUniformity R] (hx : Summable x) (hg : PowerSeries.HasSubst g) :
    (∑' i, x i).subst g = ∑' i, ((x i).subst g) := by
  rw [←PowerSeries.coe_substAlgHom hg, PowerSeries.substAlgHom_eq_aeval hg,
    Summable.map_tsum hx _ <| PowerSeries.continuous_aeval _]

open Finset in
/-- A series of multi variate power series is summable if the order of the sequence
  strictly increase. -/
lemma MvPowerSeries.HasSum.increase_order {x : ℕ → MvPowerSeries σ R}
    [TopologicalSpace R] (hx : ∀ n, n ≤ (x n).order) :
    HasSum x (fun n => ∑ i ∈ Finset.range (n.degree + 1), ((x i).coeff n)) := by
  rw [HasSum, (MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _)]
  intro d
  simp only [map_sum, SummationFilter.unconditional_filter]
  refine tendsto_atTop_nhds.mpr fun U hU₁ Uopen => by
    use (Finset.range (d.degree + 1))
    intro s hs
    rw [(sum_subset hs _).symm]; exact hU₁
    intro i _ hi
    by_cases hxi : (x i).order = ⊤
    · exact ((weightedOrder_eq_top_iff fun x ↦ 1).mp hxi) ▸ (coeff_zero _)
    · simp only [mem_range, not_lt] at hi
      rw [coeff_of_lt_order]
      specialize hx i
      rw [←(ENat.coe_toNat hxi)] at ⊢ hx
      norm_cast at ⊢ hx
      linarith

lemma PowerSeries.HasSum.increase_order {x : ℕ → PowerSeries R}
    [TopologicalSpace R] (hx : ∀ n, n ≤ (x n).order) :
    HasSum x <| PowerSeries.mk (fun n => ∑ i ∈ Finset.range (n + 1), ((x i).coeff n)) := by
  rw [HasSum, (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _)]
  intro d
  simp only [map_sum, SummationFilter.unconditional_filter]
  refine tendsto_atTop_nhds.mpr fun U hU₁ Uopen => by
    use (Finset.range (d + 1))
    intro s hs
    rw [(Finset.sum_subset hs _).symm]
    rw [coeff_mk] at hU₁
    exact hU₁
    intro i _ hi
    sorry
    -- by_cases hxi : (x i).order = ⊤
    -- · exact ((weightedOrder_eq_top_iff fun x ↦ 1).mp hxi) ▸ (coeff_zero _)
    -- · simp only [mem_range, not_lt] at hi
    --   rw [coeff_of_lt_order]
    --   specialize hx i
    --   rw [←(ENat.coe_toNat hxi)] at ⊢ hx
    --   norm_cast at ⊢ hx
    --   linarith

open Finset in
/-- A series of multi variate power series is summable if the order of the sequence
  strictly increase. -/
lemma MvPowerSeries.Summable.increase_order {x : ℕ → MvPowerSeries σ R}
    [TopologicalSpace R] (hx : ∀ n, (x n).order ≥ n) : Summable x :=
  ⟨(fun n => ∑ i ∈ Finset.range (n.degree + 1), ((x i).coeff n)), HasSum.increase_order hx⟩


section

variable (w : τ → ℕ) {a : σ → MvPowerSeries τ R}

open MvPowerSeries

omit [DecidableEq τ] in
theorem MvPowerSeries.le_weightedOrder_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    ⨅ (d : σ →₀ ℕ) (_ : coeff d f ≠ 0), d.weight (weightedOrder w ∘ a) ≤
      (f.subst a).weightedOrder w := by
  classical
  apply MvPowerSeries.le_weightedOrder
  intro d hd
  rw [coeff_subst ha, finsum_eq_zero_of_forall_eq_zero]
  intro x
  by_cases hfx : f.coeff x = 0
  · simp [hfx]
  rw [coeff_eq_zero_of_lt_weightedOrder w, smul_zero]
  refine hd.trans_le (((biInf_le _ hfx).trans ?_).trans (le_weightedOrder_prod ..))
  simp only [Finsupp.weight_apply, Finsupp.sum, Function.comp_apply]
  exact Finset.sum_le_sum fun i hi ↦ .trans (by simp) (le_weightedOrder_pow ..)

omit [DecidableEq τ] in
theorem MvPowerSeries.le_weightedOrder_subst_of_forall_ne_zero
    (ha : MvPowerSeries.HasSubst a) (ha0 : ∀ i, a i ≠ 0) (f : MvPowerSeries σ R) :
    f.weightedOrder (ENat.toNat ∘ weightedOrder w ∘ a) ≤ (f.subst a).weightedOrder w := by
  refine .trans ?_ (le_weightedOrder_subst w ha f)
  simp only [ne_eq, le_iInf_iff]
  refine fun i hi ↦ (weightedOrder_le _ hi).trans ?_
  simp [Finsupp.weight_apply, Finsupp.sum, (ne_zero_iff_weightedOrder_finite _).mp (ha0 _)]

omit [DecidableEq τ] in
theorem MvPowerSeries.le_order_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    (⨅ i, (a i).order) * f.order ≤ (f.subst a).order := by
  refine .trans ?_ (le_weightedOrder_subst _ ha _)
  simp only [ne_eq, le_iInf_iff]
  intro i hi
  trans (⨅ (i : σ), (order ∘ a) i) * ↑i.degree
  · refine mul_le_mul_right (order_le hi ) _
  · simp only [Function.comp_apply, order, Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Nat.cast_sum, Finset.mul_sum, Finsupp.weight_apply, nsmul_eq_mul]
    exact Finset.sum_le_sum fun j hj => by
      simp [mul_comm, mul_le_mul_right (iInf_le_iff.mpr fun _ a ↦ a j)]

end

open PowerSeries in
theorem order_eq_order {φ : PowerSeries R} : φ.order = MvPowerSeries.order φ := by
  refine eq_of_le_of_ge ?_ ?_
  · refine MvPowerSeries.le_order fun d hd => by
      have : coeff ↑(Finsupp.degree d) φ = 0 := coeff_of_lt_order _ hd
      have eq_aux : d.degree = d () := Finset.sum_eq_single _ (by simp) (by simp)
      exact (PowerSeries.coeff_def rfl (R := R)) ▸ (eq_aux ▸ this)
  · refine le_order φ (MvPowerSeries.order φ) fun i hi => by
      rw [←Finsupp.degree_single () i] at hi
      exact MvPowerSeries.coeff_of_lt_order hi

section

variable {a : MvPowerSeries τ R}

omit [DecidableEq τ] in
theorem PowerSeries.le_weightedOrder_subst (w : τ → ℕ) (ha : HasSubst a) (f : PowerSeries R) :
    f.order * (a.weightedOrder w) ≤ (f.subst a).weightedOrder w := by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ (PowerSeries.hasSubst_iff.mp ha) _)
  simp only [ne_eq, Function.comp_const, le_iInf_iff]
  intro i hi
  trans i () * MvPowerSeries.weightedOrder w a
  · exact mul_le_mul_left (f.order_le (i ()) (by delta PowerSeries.coeff; convert hi; aesop)) _
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype]

theorem PowerSeries.le_order_subst (a : MvPowerSeries τ S) (ha : HasSubst a) (f : PowerSeries R) :
    a.order * f.order ≤ (f.subst a).order := by
  sorry
  -- refine .trans ?_ (MvPowerSeries.le_order_subst (PowerSeries.hasSubst_iff.mp ha) _)
  -- simp [order_eq_order]

end
-- lemma PowerSeries.le_order_subst (a : MvPowerSeries τ S) (f : PowerSeries R)
--     (ha : PowerSeries.HasSubst a) :
--     a.order * f.order ≤ (f.subst a).order := by
--   by_cases hf₀ : f.order = 0
--   · simp [hf₀]
--   apply MvPowerSeries.le_order
--   intro d hd
--   rw [coeff_subst ha, finsum_eq_zero_of_forall_eq_zero]
--   intro x
--   by_cases hf : f.order = ⊤
--   · simp [order_eq_top.mp hf]
--   · by_cases ha' : a.order = ⊤
--     · simp only [order_eq_top_iff.mp ha']
--       by_cases hx : x = 0
--       · simp [hx, order_ne_zero_iff_constCoeff_eq_zero.mp hf₀]
--       · simp [zero_pow hx]
--     by_cases hx : x < f.order
--     · rw [coeff_of_lt_order x hx, zero_smul]
--     · suffices (MvPowerSeries.coeff d) (a ^ x) = 0 by rw [this, smul_zero]
--       rw [MvPowerSeries.coeff_pow, Finset.sum_eq_zero]
--       intro l hl
--       rw [←ENat.coe_toNat hf, ←ENat.coe_toNat ha'] at hd
--       rw [←ENat.coe_toNat hf] at hx
--       norm_cast at hx hd
--       simp only [Finset.mem_finsuppAntidiag] at hl
--       have h : ∃ i ∈ Finset.range x, (l i).degree < a.order := by
--         rw [← ENat.coe_toNat ha']
--         by_contra hc
--         simp only [not_exists, not_and, not_lt] at hc
--         suffices a.order.toNat * f.order.toNat ≤ d.degree by linarith
--         calc
--           _ ≤ a.order.toNat * x :=
--             Nat.mul_le_mul_left a.order.toNat <| Nat.le_of_not_lt hx
--           _ = ∑ i ∈ Finset.range x, a.order.toNat := by
--             rw [Finset.sum_const, Finset.card_range, Nat.mul_comm, Nat.nsmul_eq_mul]
--           _ ≤ _ := by
--             rw [←hl.1, map_sum]
--             exact Finset.sum_le_sum <| fun i hi => by exact_mod_cast hc i hi
--       obtain ⟨i, hi₀, hi₁⟩ := h
--       rw [Finset.prod_eq_zero hi₀ (MvPowerSeries.coeff_of_lt_order hi₁)]

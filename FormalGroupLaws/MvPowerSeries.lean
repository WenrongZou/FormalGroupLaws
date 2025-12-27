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
        erw [← Algebra.algebraMap_ofSubsemiring_apply, AddMonoidHom.map_finsum (algebraMap
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
            erw [← @Algebra.algebraMap_ofSubsemiring_apply, coeff_apply,
               ←coeff_apply (subst ![Y₀, Y₁] (F.toFun.toSubring T hF)) (x_1 x_3),
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
        erw [F.assoc, coeff_subst <| has_subst_aux₂ F.zero_constantCoeff,
          coeff_subst has_subst_aux₀', ← @Algebra.algebraMap_ofSubsemiring_apply,
          AddMonoidHom.map_finsum (algebraMap (↥T.toSubsemiring) R).toAddMonoidHom h₁]
        simp [Algebra.algebraMap_ofSubsemiring_apply]
        congr! 3 with d
        simp [coeff_mul]
        congr! 1 with x_1 x_2
        rw [Y₀, Y₀,  ←eq_aux 0, Y₁, Y₁, ←eq_aux 1]
        simp [coeff_pow]
        congr! 3 with x_1 x_2 x_3 x_4
        obtain h₂ := coeff_subst_finite has_subst_aux' (F.toFun.toSubring T hF) (x_1 x_3)
        erw [coeff_subst has_subst_YZ, coeff_subst has_subst_aux',
          ← Algebra.algebraMap_ofSubsemiring_apply,
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

omit [DecidableEq σ]
lemma Summable.summable_of_subst {x : ℕ → PowerSeries R} {g: MvPowerSeries σ R}
    [UniformSpace R] [T2Space R] [DiscreteUniformity R] (hx : Summable x)
    (hg : PowerSeries.HasSubst g) : Summable fun i => (x i).subst g := by
  rw [←PowerSeries.coe_substAlgHom hg, PowerSeries.substAlgHom_eq_aeval hg]
  exact Summable.map hx _ <| PowerSeries.continuous_aeval (PowerSeries.HasSubst.hasEval hg)

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
    by_cases hxi : (x i).order = ⊤
    · exact ((x i).order_eq_top.mp hxi) ▸ (coeff_zero _)
    · simp  at hi
      rw [coeff_of_lt_order]
      specialize hx i
      rw [← (ENat.coe_toNat hxi)] at ⊢ hx
      norm_cast at ⊢ hx
      linarith

open Finset in
/-- A series of multi variate power series is summable if the order of the sequence
  strictly increase. -/
lemma MvPowerSeries.Summable.increase_order {x : ℕ → MvPowerSeries σ R}
    [TopologicalSpace R] (hx : ∀ n, n ≤ (x n).order) : Summable x :=
  ⟨(fun n => ∑ i ∈ Finset.range (n.degree + 1), ((x i).coeff n)), HasSum.increase_order hx⟩

open Finset in
/-- A series of multi variate power series is summable if the order of the sequence
  strictly increase. -/
lemma PowerSeries.Summable.increase_order {x : ℕ → PowerSeries R}
    [TopologicalSpace R] (hx : ∀ n, n ≤ (x n).order) : Summable x :=
  ⟨(.mk fun n => ∑ i ∈ Finset.range (n + 1), (((x i).coeff n))), HasSum.increase_order hx⟩


section

variable (w : τ → ℕ) {a : σ → MvPowerSeries τ R}

open MvPowerSeries

-- lemma MvPowerSeries.subst_C (ha : HasSubst a) (r : R) : subst a (C r) = C r := by
--   conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, subst_smul ha, ← substAlgHom_apply ha,
--     map_one, smul_eq_C_mul, mul_one]

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

omit [Algebra R S]
theorem PowerSeries.le_order_map (f : R →+* S) {φ : PowerSeries R} :
    φ.order ≤ (φ.map f).order :=
  le_order _ _ fun i hi => by simp [coeff_of_lt_order i hi]

omit [Algebra R S]
theorem MvPowerSeries.le_order_map (f : R →+* S) {φ : MvPowerSeries σ R} :
    φ.order ≤ (φ.map f).order :=
  le_order  fun i hi => by simp [coeff_of_lt_order hi]

theorem PowerSeries.le_order_smul {φ : PowerSeries R} {a : R} :
    φ.order ≤ (a • φ).order :=
  le_order _ φ.order fun i hi => by simp [coeff_of_lt_order i hi]

theorem MvPowerSeries.le_order_smul {φ : MvPowerSeries σ R} {a : R} :
    φ.order ≤ (a • φ).order := le_order fun i hi => by simp [coeff_of_lt_order hi]

end

section

lemma PowerSeries.coeff_subst_X_s {s : σ} [DecidableEq σ] {f : PowerSeries R} :
    (f.subst (MvPowerSeries.X s)).coeff (Finsupp.single s 1) = f.coeff 1 := by
  rw [coeff_subst (.X _), finsum_eq_single _ 1]
  simp
  intro d hd
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg _, smul_zero]
  refine Finsupp.ne_iff.mpr ⟨s, by simp [hd.symm]⟩

lemma PowerSeries.coeff_subst_X_s' {s t: σ} [DecidableEq σ] {f : PowerSeries R} (h : s ≠ t) :
    (f.subst (MvPowerSeries.X s (R := R))).coeff (Finsupp.single t 1) = 0 := by
  rw [coeff_subst (.X _), finsum_eq_zero_of_forall_eq_zero]
  intro d
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg _, smul_zero]
  refine Finsupp.ne_iff.mpr ?_
  use t
  simp [Finsupp.single_eq_of_ne' h]


end


lemma PowerSeries.one_le_order {f : PowerSeries R} (hf : f.constantCoeff = 0) : 1 ≤ f.order := by
  sorry

lemma MvPowerSeries.one_le_order {F : MvPowerSeries σ R} (hF : F.constantCoeff = 0) :
    1 ≤ F.order := sorry

lemma MvPowerSeries.order_X_pow_ge [DecidableEq σ] {n : ℕ} (s : σ) : n ≤ ((X s (R := R))^n).order  := by
  refine le_order fun d hd => by
    rw [coeff_X_pow, if_neg]
    by_contra hc
    simp [hc] at hd

lemma PowerSeries.le_order_monomial (n : ℕ) (r : R): n ≤ (monomial n r).order  :=
  le_order _ _ fun d hd => by
    rw [coeff_monomial, if_neg (Nat.ne_of_lt (ENat.coe_lt_coe.mp hd)) ]

lemma PowerSeries.HasSubst.pow {f : MvPowerSeries σ R} (hf : HasSubst f) {n : ℕ} (hn : 1 ≤ n) :
    HasSubst (f ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simp [hf]
  | succ k hk ih =>
    rw [pow_add, pow_one]
    exact HasSubst.mul_left ih

lemma Rchar_p {p : ℕ} {I : Ideal R} (hI : ↑p ∈ I) [hp : Fact (Nat.Prime p)] :
    ExpChar (R ⧸ I) p := by
  by_cases h : Nontrivial (R ⧸ I)
  · have aux : CharP (R ⧸ I) p := by

      refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hI
    exact expChar_prime _ p
  -- charP_iff

  simp_all
  have aux : CharP (R ⧸ I) p := by
    rw [charP_iff]
    intro x
    constructor
    · intro hx
      obtain h₁ := Ideal.Quotient.eq_zero_iff_mem.mp hx
      simp_all
      sorry
    · sorry
  sorry

lemma PowerSeries.subst_express_as_tsum [UniformSpace R] [T2Space R] [DiscreteUniformity R]
    {G : MvPowerSeries σ R} (f : PowerSeries R)
    (hG : HasSubst G) :
    f.subst G = ∑' i, (f.coeff i) • G ^ i := by

  sorry

-- lemma PowerSeries.subst_express_as_tsum [UniformSpace R] [T2Space R] [DiscreteUniformity R]
--     {G : MvPowerSeries σ R} (f : PowerSeries R)
--     (hG : HasSubst G) :
--     expand p hp ∑' i, (f.coeff i) • G ^ i := by


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

-- section prime_pow_poly

-- open Polynomial

-- variable {R : Type*} {p : ℕ} [CommSemiring R] [ExpChar R p]

-- theorem Polynomial.prime_pow_eq {q : Polynomial R} :
--   q ^ p = q.expand

-- end prime_pow_poly

section

end

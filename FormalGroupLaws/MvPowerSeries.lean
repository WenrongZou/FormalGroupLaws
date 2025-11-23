import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
import FormalGroupLaws.Basic

variable {R : Type*} [CommRing R] {σ τ: Type*} {I : Ideal R} [DecidableEq σ] {n : ℕ}
  [DecidableEq τ]

open MvPowerSeries

/- Given a ideal `I` of commutative ring `R`, then multivariate power series with coefficient in
`I`, forms a ideal of ring of multivariate power series over `R`. -/
def Ideal.MvPowerSeries : Ideal (MvPowerSeries σ R) where
  carrier := {p | ∀ n, p n ∈ I}
  add_mem' := fun {a} {b} ha hb n => add_mem (ha n) (hb n)
  zero_mem' := fun n => (Submodule.Quotient.mk_eq_zero I).mp rfl
  smul_mem' := fun c {x} hx n ↦ by
    rw [smul_eq_mul, ← show coeff n (c * x) = (c * x) n by rfl, coeff_mul]
    exact Ideal.sum_mem _ <| fun d hd => mul_mem_left I ((coeff d.1) c) (hx d.2)

lemma MvPowerSeries.mul_mem_mul {a b : MvPowerSeries σ R} {J : Ideal R}
    (ha : a ∈ I.MvPowerSeries) (hb : b ∈ J.MvPowerSeries) :
    a * b ∈ (I * J).MvPowerSeries := by
  unfold Ideal.MvPowerSeries
  simp
  intro n
  rw [show (a * b) n = coeff n (a * b) by rfl, coeff_mul]
  refine Ideal.sum_mem (I * J) <| fun d hd => Submodule.mul_mem_mul (ha d.1) (hb d.2)

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

@[simp]
theorem coeff_ofSubring {n : σ →₀ ℕ} (p : MvPowerSeries σ T) : (ofSubring T p).coeff n = p.coeff n
  := by
  exact rfl

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

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
import FormalGroupLaws.Basic

variable {R : Type*} [CommRing R] {σ : Type*} {I : Ideal R} [DecidableEq σ] {n : ℕ}

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

/-- Given a multivariate formal power series whose coefficients are in some subring, return
the multivariate formal power series whose coefficients are in the ambient ring. -/
def MvPowerSeries.ofSubring (p : MvPowerSeries σ T) : MvPowerSeries σ R :=
  fun n => (p n : R)

@[simp]
theorem coeff_ofSubring {n : σ →₀ ℕ} (p : MvPowerSeries σ T) : (ofSubring T p).coeff n = p.coeff n
  := by
  exact rfl

variable (F : FormalGroup R)

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

    sorry


end ToSubring

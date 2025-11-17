import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
-- import Mathlib.LinearAlgebra.SModEq.Basic
-- import Mathlib

variable {R : Type*} [CommRing R] {σ : Type*} {I : Ideal R} [DecidableEq σ]

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


section ToSubring

variable {σ : Type*} (p : MvPowerSeries σ R) (T : Subring R)

/-- Given a multivariate formal power series `p` and a subring `T` that contains the
 coefficients of `p`,return the corresponding multivariate formal power series
 whose coefficients are in `T`. -/
def MvPowerSeries.toSubring (hp : ∀ n, p n ∈ T) : MvPowerSeries σ T := fun n => ⟨p n, hp n⟩

variable (hp : ∀ n, p n ∈ T)

@[simp]
theorem coeff_toSubring {n : σ →₀ ℕ} : ↑((toSubring p T hp).coeff n) = p.coeff n:= rfl

/-- Given a multivariate formal power series whose coefficients are in some subring, return
the multivariate formal power series whose coefficients are in the ambient ring. -/
def MvPowerSeries.ofSubring (p : MvPowerSeries σ T) : MvPowerSeries σ R :=
  fun n => (p n : R)

@[simp]
theorem coeff_ofSubring {n : σ →₀ ℕ} (p : MvPowerSeries σ T) : (ofSubring T p).coeff n = p.coeff n
  := by
  exact rfl


end ToSubring

-- lemma aux : f ≡ g [IMOD I.MvPowerSeries] ↔ f ≡ g [SMOD I.MvPowerSeries] := by
--   constructor
--   intro h
--   apply SModEq.sub_mem.mpr
--   exact h
--   intro h
--   apply SModEq.sub_mem.mp
--   exact h

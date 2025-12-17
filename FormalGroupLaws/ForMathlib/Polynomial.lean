import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Substitution

section prime_pow_poly

open MvPolynomial

#check Polynomial.induction_on'
#check MvPolynomial.induction_on
#check MvPolynomial.instCharP

variable {R : Type*} {p : ℕ} [CommSemiring R] [ExpChar R p] {σ : Type*}

-- instance : CharP (MvPolynomial σ R) p := inferInstance

instance [h : ExpChar R p] : ExpChar (MvPolynomial σ R) p := by
  cases h; exacts [ExpChar.zero, ExpChar.prime ‹_›]

theorem Polynomial.prime_pow_eq {q : Polynomial R} :
    q ^ p = (q.expand R p).map (frobenius R p) := (expand_char p q).symm

theorem MvPolynomial.expand_char {q : MvPolynomial σ R} :
    (q.expand p).map (frobenius R p) = q ^ p :=
  q.induction_on' fun _ _ => by simp [monomial_pow, frobenius]
    fun _ _ ha hb => by rw [map_add, map_add, ha, hb, add_pow_expChar]

end prime_pow_poly

section PowerSeries

open scoped PowerSeries

section expand

variable {R : Type*} {p : ℕ} [CommRing R] (hp : p ≠ 0)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
noncomputable
def PowerSeries.expand : R⟦X⟧ →ₐ[R] R⟦X⟧ := substAlgHom (HasSubst.X_pow hp)

end expand

variable {R : Type*} {p : ℕ} [CommRing R] [ExpChar R p] {σ : Type*}

include R in
lemma aux : p ≠ 0 := expChar_ne_zero R p

end PowerSeries

section MvPowerSeries



end MvPowerSeries

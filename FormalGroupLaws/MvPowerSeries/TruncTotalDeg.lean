import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc


noncomputable section

variable {σ : Type*} [DecidableEq σ] [Fintype σ] {R : Type*} [CommRing R]

open  MvPowerSeries Classical

/-- The part of a multivariate power series with total degree n.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `truncTotalDeg R n p` is the multivariable power series obtained from `p`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `∑ a_i = n`.

TODO: FIX NAME
TODO: Remove [Fintype σ] typeclass requirement
-/
def MvPowerSeries.truncTotalDegEq (n : ℕ) (p : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.univ.finsuppAntidiag n, MvPolynomial.monomial m (coeff R m p)

lemma MvPowerSeries.truncTotalDegEq_eq (n : ℕ) (p : MvPowerSeries σ R) :
    p.truncTotalDegEq n
      = ∑ m ∈ Finset.univ.finsuppAntidiag n, MvPolynomial.monomial m (coeff R m p) :=
  rfl

/-- The part of a multivariate power series with total degree at most n.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `truncTotalDeg R n p` is the multivariable power series obtained from `p`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `∑ a_i ≤ n`.
-/
def MvPowerSeries.truncTotalDeg (n : ℕ) (p : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ i ∈ Finset.range n, p.truncTotalDegEq i

lemma MvPowerSeries.truncTotalDeg_eq (n : ℕ) (p : MvPowerSeries σ R) :
    p.truncTotalDeg n = ∑ i ∈ Finset.range n, p.truncTotalDegEq i :=
  rfl

theorem coeff_truncTotalDegEq (n : ℕ) (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncTotalDegEq n φ).coeff m = if Finset.univ.sum m = n then coeff R m φ else 0 := by
  simp [truncTotalDegEq, MvPolynomial.coeff_sum]

theorem coeff_truncTotalDeg (n : ℕ) (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncTotalDeg n φ).coeff m = if Finset.univ.sum m < n then coeff R m φ else 0 := by
  simp_rw [truncTotalDeg, MvPolynomial.coeff_sum, coeff_truncTotalDegEq,
    Finset.sum_ite_eq, Finset.mem_range]

theorem coeff_truncTotalDegEq_of_totalDeg_eq (n : ℕ) (m : σ →₀ ℕ) (hm : Finset.univ.sum m = n) (φ : MvPowerSeries σ R) :
    (truncTotalDegEq n φ).coeff m = coeff R m φ := by
  simp only [coeff_truncTotalDegEq, hm, if_true]

theorem coeff_truncTotalDeg_of_totalDeg_lt (n : ℕ) (m : σ →₀ ℕ) (hm : Finset.univ.sum m < n) (φ : MvPowerSeries σ R) :
    (truncTotalDeg n φ).coeff m = coeff R m φ := by
  simp only [coeff_truncTotalDeg, hm, if_true]

theorem truncTotalDegEq_powerSeries (n : ℕ) (ϕ : PowerSeries R) :
  truncTotalDegEq n ϕ
    = (MvPolynomial.pUnitAlgEquiv _).symm (Polynomial.monomial n (PowerSeries.coeff _ n ϕ)) := by
  ext w
  simp [coeff_truncTotalDegEq, MvPolynomial.coeff_X_pow]
  split_ifs with h₁ h₂ h₃
  · subst h₂
    rfl
  · subst h₁
    simpa using Finsupp.ext_iff.not.mp h₂
  · subst h₃
    simp at h₁
  · rfl

theorem truncTotalDeg_powerSeries (n : ℕ) (ϕ : PowerSeries R) :
    truncTotalDeg n ϕ = (MvPolynomial.pUnitAlgEquiv _).symm (ϕ.trunc n) := by
  rw [(MvPolynomial.pUnitAlgEquiv _).eq_symm_apply, truncTotalDeg]
  ext d
  simp_rw [truncTotalDegEq_powerSeries, map_sum,
    (MvPolynomial.pUnitAlgEquiv _).apply_symm_apply, PowerSeries.trunc,
    Finset.range_eq_Ico]

lemma MvPowerSeries.truncTotalDeg_map_add (f g : MvPowerSeries σ R) (n : ℕ) :
  truncTotalDeg n (f + g) = truncTotalDeg n f + truncTotalDeg n g := by
  ext m
  rw [MvPolynomial.coeff_add]
  rw [coeff_truncTotalDeg, coeff_truncTotalDeg, coeff_truncTotalDeg]
  split_ifs <;> simp

/--
`MvPowerSeries.truncTotalDeg` as a monoid homomorphism.
-/
def MvPowerSeries.truncTotalDegHom (n : ℕ) : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncTotalDeg n
  map_zero' := by
    simp [truncTotalDeg, truncTotalDegEq]
  map_add' := by
    intro x y
    apply truncTotalDeg_map_add

theorem MvPowerSeries.truncTotalDegHom_apply (n : ℕ) (p : MvPowerSeries σ R) :
    p.truncTotalDegHom n = p.truncTotalDeg n :=
  rfl

end

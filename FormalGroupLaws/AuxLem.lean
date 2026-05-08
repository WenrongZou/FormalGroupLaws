module

public import Mathlib.Data.Nat.Choose.Lucas

@[expose] public section

/-!
# Binomial coefficients and prime powers
We prove two results:
1. If `p` is prime, `0 < m`, and `p ∣ m.choose i` for all `i ∈ Finset.Icc 1 (m-1)`,
   then `m` is a power of `p`.
2. The gcd of all middle binomial coefficients `C(m, i)` for `1 ≤ i ≤ m-1` equals `1`
   if and only if `m` is not a prime power (assuming `1 < m`).
-/

variable {n p : ℕ} [hp : Fact (Nat.Prime p)]

open Finset hiding choose

open Nat Polynomial

namespace Choose

/-- For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero_nat` for the version with `MOD`. -/
theorem eq_pow_multiplicity_of_choose_modEq_zero (hn : 0 < n)
    (h : ∀ i ∈ Icc 1 (n - 1), n.choose i ≡ 0 [ZMOD p]) : n = p ^ multiplicity p n := by
  by_contra! hn₀
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd p n
  specialize h _ (mem_Icc.mpr ⟨NeZero.one_le, le_sub_one_of_lt <| lt_of_le_of_ne (le_of_dvd hn
    (pow_multiplicity_dvd p n)) hn₀.symm⟩)
  nth_grw 1 [← mul_one (p ^ _), hm, choose_pow_mul_pow_mul_modEq_choose, choose_one_right] at h
  have : ¬ p ∣ m := by
    by_contra! hc
    have : p ^ (multiplicity p n + 1) ∣ n := by
      nth_rw 2 [hm]
      simpa using Nat.mul_dvd_mul_left _ hc
    nlinarith [(FiniteMultiplicity.pow_dvd_iff_le_multiplicity (finiteMultiplicity_iff.mpr
      ⟨hp.out.ne_one, hn⟩)).mp this]
  norm_cast at h
  exact absurd (dvd_iff_mod_eq_zero.mpr h) this

/-- For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero` for the version with `ZMOD`. -/
theorem eq_pow_multiplicity_of_choose_modEq_zero_nat (hn : 0 < n)
    (h : ∀ i ∈ Icc 1 (n - 1), n.choose i ≡ 0 [MOD p]) : n = p ^ multiplicity p n :=
  eq_pow_multiplicity_of_choose_modEq_zero hn (by exact_mod_cast h)

/-- For a prime power `n`, the minimal prime factor divides the greatest common divisor of
`choose n 1, ⋯, choose n (n - 1)`. -/
theorem minFac_dvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    n.minFac ∣ (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) := by
  obtain ⟨k, _, _, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  exact dvd_gcd_iff.mpr fun i hi => by
    nth_rw 2 [hn₁]
    exact Prime.dvd_choose_pow (minFac_prime_iff.mpr h.ne_one) (by grind) (by grind)

/-- For a prime power `n`, the greatest common divisor of `choose n 1, ⋯, choose n (n - 1)`
is actually the minimal prime factor of `n`. -/
theorem gcd_choose_eq_minFac_of_isPrimePow (h : IsPrimePow n) :
    (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) = n.minFac := by
  have ne_zero : (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) ≠ 0 :=
    Finset.gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  obtain ⟨k, _, k_pos, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  have : ¬ n.minFac ^ 2 ∣ (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) := by
    refine mt Finset.dvd_gcd_iff.mp ?_
    simp only [mem_Icc, not_forall]
    have : n.minFac ^ (k - 1) ≤ n.minFac ^ k := Nat.pow_le_pow_right (minFac_pos n) (sub_le k 1)
    refine ⟨n.minFac ^ (k-1), ⟨one_le_pow _ _ (minFac_pos n), ?_⟩, ?_⟩
    · refine le_sub_one_of_lt ?_
      nth_rw 2 [hn₁]
      exact Nat.pow_lt_pow_of_lt (Prime.one_lt isPrime) (sub_one_lt_of_lt k_pos)
    · refine emultiplicity_lt_iff_not_dvd.mp ?_
      nth_rw 2 [hn₁]
      rw [Nat.Prime.emultiplicity_choose_prime_pow isPrime this (pow_ne_zero _
        (Nat.Prime.ne_zero isPrime)), multiplicity_pow_self_of_prime (prime_iff.mp isPrime)]
      norm_cast
      grind
  have h₁ : ((Icc 1 (n - 1)).gcd fun i ↦ n.choose i).primeFactors = {n.minFac} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨isPrime.mem_primeFactors
      (minFac_dvd_gcd_choose_of_isPrimePow h) ne_zero, ?_⟩
    intro p hp
    simp only [mem_primeFactors, ne_eq] at hp
    obtain ⟨hp₁, hp₂, hp₃⟩ := hp
    simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at hp₂
    have := eq_pow_multiplicity_of_choose_modEq_zero_nat (hp := ⟨hp₁⟩) h.pos hp₂
    have dvd_pow : n.minFac ∣  p ^ multiplicity p n := this ▸ minFac_dvd _
    exact (Nat.prime_dvd_prime_iff_eq isPrime hp₁).mp (isPrime.dvd_of_dvd_pow dvd_pow)|>.symm
  have : multiplicity n.minFac ((Icc 1 (n - 1)).gcd fun i ↦ n.choose i) = 1 := by
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ this
    simpa using minFac_dvd_gcd_choose_of_isPrimePow h
  rw [Nat.prod_pow_primeFactors_factorization ne_zero, h₁]
  simp [← Nat.multiplicity_eq_factorization isPrime ne_zero, this]

/-- For a natural number `n` greater than `1`, assume that `n` is not a prime power, then
the greatest common divisor of  `choose n 1, ⋯, choose n (n - 1)` is `1`. -/
theorem gcd_choose_eq_one_of_not_isPrimePow (hn : 1 < n) (hpn : ¬ IsPrimePow n) :
    (Icc 1 (n - 1)).gcd (fun i ↦ n.choose i) = 1 := by
  contrapose! hpn
  obtain ⟨q, hq, h⟩ := Nat.exists_prime_and_dvd hpn
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at h
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat (zero_lt_of_lt hn) h (hp := ⟨hq⟩)
  refine (isPrimePow_nat_iff n).mpr ⟨q, _, hq, Dvd.multiplicity_pos ?_, this.symm⟩
  specialize h 1 (by grind)
  rw [choose_one_right, modEq_zero_iff_dvd] at h
  exact h

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic
/-!
# Binomial coefficients and prime powers
We prove two results:
1. If `p` is prime, `0 < m`, and `p ∣ m.choose i` for all `i ∈ Finset.Icc 1 (m-1)`,
   then `m` is a power of `p`.
2. The gcd of all middle binomial coefficients `C(m, i)` for `1 ≤ i ≤ m-1` equals `1`
   if and only if `m` is not a prime power (assuming `1 < m`).
-/
section Theorem1
/-! ### Theorem 1: All middle binomial coefficients divisible by p implies prime power -/
/-
Using Lucas' theorem, if all middle binomial coefficients of `m` are divisible by the
prime `p`, and `p ∣ m`, then all middle binomial coefficients of `m / p` are also
divisible by `p`.
-/
private lemma dvd_choose_div_of_dvd_choose {p m : ℕ} (hp : Nat.Prime p) (hdvd : p ∣ m)
    (h : ∀ i ∈ Finset.Icc 1 (m - 1), p ∣ m.choose i) :
    ∀ j ∈ Finset.Icc 1 (m / p - 1), p ∣ (m / p).choose j := by
  intro j hj;
  -- Since $j \in [1, m/p - 1]$, we have $p * j \in [p, m - p]$. Therefore, $p * j \in [1, m - 1]$.
  have h_pj_range : p * j ∈ Finset.Icc 1 (m - 1) := by
    simp only [Finset.mem_Icc] at ⊢ hj
    obtain ⟨hj₁, hj₂⟩ := hj
    constructor
    · exact Right.one_le_mul (Nat.Prime.one_le hp) hj₁
    · sorry
    -- rcases p with ( _ | _ | p ) <;> rcases m with ( _ | _ | m ) <;> simp_all +decide;
    -- exact ⟨ Nat.mul_pos ( Nat.succ_pos _ ) hj.1,
    --   by nlinarith [ Nat.div_mul_le_self ( m + 1 + 1 ) ( p + 1 + 1 ), Nat.sub_add_cancel ( show 1 ≤ ( m + 1 + 1 ) / ( p + 1 + 1 ) from Nat.div_pos ( Nat.le_of_dvd ( Nat.succ_pos _ ) hdvd ) ( Nat.succ_pos _ ) ) ] ⟩;
  -- By Lucas' theorem, $C(m, p * j) \equiv C(m / p, j) * C(0, 0) \pmod{p}$.
  have h_lucas : Nat.choose m (p * j) ≡ Nat.choose (m / p) j * Nat.choose (m % p) 0 [MOD p] := by
    convert Choose.choose_modEq_choose_mod_mul_choose_div_nat using 1;
    · cases p <;> simp_all
    · exact ⟨hp⟩
  simp only [Nat.choose_zero_right, mul_one] at h_lucas
  specialize h (p * j) h_pj_range
  grw [Dvd.dvd.modEq_zero_nat h] at h_lucas
  exact Nat.dvd_of_mod_eq_zero h_lucas.symm

/-
If `p` is prime, `0 < m`, and `p` divides all middle binomial coefficients of `m`,
then `m` is a power of `p`. The proof proceeds by strong induction: if `m ≥ 2` then
`p ∣ C(m,1) = m`, and by `dvd_choose_div_of_dvd_choose` the same property holds for
`m / p`, so the inductive hypothesis gives `m / p = p ^ k` whence `m = p ^ (k+1)`.
-/
theorem exists_pow_eq_of_prime_dvd_choose {p m : ℕ} (hp : Nat.Prime p) (hm : 0 < m)
    (h : ∀ i ∈ Finset.Icc 1 (m - 1), p ∣ m.choose i) : ∃ n, m = p ^ n := by
  -- We proceed by strong induction on $m$.
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hpm : p ∣ m
    · -- By `dvd_choose_div_of_dvd_choose`, all middle binomial coefficients of `m / p` are also divisible by `p`.
      have h_div_choose_m_div_p : ∀ j ∈ Finset.Icc 1 ((m / p) - 1), p ∣ (m / p).choose j := by
        exact fun j a => dvd_choose_div_of_dvd_choose hp hpm h j a
      rcases ih ( m / p ) ( Nat.div_lt_self hm hp.one_lt ) ( Nat.div_pos ( Nat.le_of_dvd hm hpm )
        hp.pos ) h_div_choose_m_div_p with ⟨ n, hn ⟩
      exact ⟨ n + 1, by rw [ pow_succ', ← hn, Nat.mul_div_cancel' hpm ] ⟩
    · rcases m with ( _ | _ | m )
      · simp at hm
      · exact ⟨0, rfl⟩;
      · simp only [add_tsub_cancel_right, Finset.mem_Icc, and_imp] at h
        exact absurd (h 1 (by norm_num) (by norm_num)) (by simpa using hpm)
end Theorem1
section Theorem2
/-! ### Theorem 2: gcd of middle binomial coefficients equals 1 iff not a prime power -/
/-
The forward direction: if `IsPrimePow m`, then `p ∣ gcd` for some prime `p`,
so the gcd is not 1.
-/
private lemma gcd_choose_ne_one_of_isPrimePow {m : ℕ} (hm : 1 < m)
    (hpm : IsPrimePow m) :
    Finset.gcd (Finset.Icc 1 (m - 1)) (fun n ↦ m.choose n) ≠ 1 := by
  -- Suppose m = q^k with q prime and k ≥ 1. By Nat.Prime.dvd_choose_pow, q ∣ C(q^k, i) for all i with i ≠ 0 and i ≠ q^k. So for all i ∈ Icc 1 (m-1), q ∣ C(m, i). By Finset.dvd_gcd, q ∣ gcd. Since q ≥ 2, gcd ≥ 2, so gcd ≠ 1.
  obtain ⟨q, k, hq, hk, rfl⟩ : ∃ q k, Nat.Prime q ∧ 0 < k ∧ m = q^k := by
    rw [ isPrimePow_nat_iff ] at hpm ; aesop;
  refine' fun h => absurd ( h ▸ Finset.dvd_gcd fun x hx => Nat.Prime.dvd_choose_pow hq ( by linarith [ Finset.mem_Icc.mp hx ] ) ( by linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel hm.le ] ) ) ( by aesop )
/-
The backward direction: if `m` is not a prime power and `1 < m`, then the gcd
of the middle binomial coefficients is 1.
-/
private lemma gcd_choose_eq_one_of_not_isPrimePow {m : ℕ} (hm : 1 < m)
    (hpm : ¬IsPrimePow m) :
    Finset.gcd (Finset.Icc 1 (m - 1)) (fun n ↦ m.choose n) = 1 := by
  contrapose! hpm
  obtain ⟨p, hp, h⟩ := Nat.exists_prime_and_dvd hpm
  rw [Finset.dvd_gcd_iff] at h
  have := exists_pow_eq_of_prime_dvd_choose hp (Nat.zero_lt_of_lt hm) h
  exact this.elim fun n hn => hn.symm ▸ hp.isPrimePow.pow (by aesop)

end Theorem2
variable {p : ℕ} (hp : Nat.Prime p)
/-- The original statement below is false for `m = 0`: the set `Finset.Icc 1 (0 - 1)` is empty,
making the hypothesis vacuously true, but `0 ≠ p ^ n` for any `n : ℕ` since `p ^ n ≥ 1`.
We add the hypothesis `0 < m`. -/
example {m : ℕ} (hm : 0 < m) :
    (∀ i, i ∈ Finset.Icc 1 (m - 1) → p ∣ m.choose i) → (∃ n, m = p ^ n) :=
  exists_pow_eq_of_prime_dvd_choose hp hm
/- Original (false for m = 0):
example {m : ℕ} : (∀ i, i ∈ Finset.Icc 1 (m - 1) → p ∣ m.choose i) → (∃ n, m = p ^ n) :=
  sorry -/
/-- The original statement below is false for `m ∈ {0, 1}`: when `Finset.Icc 1 (m - 1) = ∅`,
the gcd is `0 ≠ 1`, while `¬IsPrimePow m` is true. We add the hypothesis `1 < m`. -/
example {m : ℕ} (hm : 1 < m) :
    Finset.gcd (Finset.Icc 1 (m - 1)) (fun n ↦ m.choose n) = 1 ↔ ¬IsPrimePow m :=
  ⟨fun h hpm => absurd h (gcd_choose_ne_one_of_isPrimePow hm hpm),
   gcd_choose_eq_one_of_not_isPrimePow hm⟩

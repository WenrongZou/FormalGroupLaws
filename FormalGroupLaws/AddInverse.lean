/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import FormalGroupLaws.Basic

/-! # Formal group laws over commutative ring

We define the additive inverse under the formal group $F$ sense, namely the power series $i(X)$
such that $F(X, i(X)) = F(i(X),X) = 0$.

## Main definitions/lemmas

* The power series `addInv_X`, which is the additive inverse of `X` under formal group $F$ sense,
namely, $F(X, i (X)) = 0$.

## References
* [Hazewinkel, Michiel. «Formal Groups and Applications»]

-/

@[expose] public section

noncomputable section

namespace FormalGroup

variable {R σ : Type*} [CommRing R] (f g : PowerSeries R) (F : FormalGroup R) (n : ℕ)

open PowerSeries Finset Fin Finsupp

/-- Inductive definition of the power series $i(X)$ such that $F(X,i(X)) = 0$. -/
abbrev addInv_aux (F : FormalGroup R) : ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1) (F.toPowerSeries.subst
    ![X, (∑ i : Fin (n + 1), C (addInv_aux F i.1) * X ^ i.1)]))

@[simp]
lemma addInv_aux_zero : addInv_aux F 0 = 0 := rfl

@[simp]
lemma addInv_aux_one : addInv_aux F 1 = -1 := rfl

/-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `i(X)`,
such that `F(X, i(X)) = 0`. -/
def addInv_X : PowerSeries R := .mk (addInv_aux F ·)

@[simp]
lemma constantCoeff_addInv_X : constantCoeff (addInv_X F) = 0 := rfl

@[simp]
lemma coeff_one_addInv_X : coeff 1 (addInv_X F) = -1 := by
  simp only [addInv_X, coeff_mk]; rfl

lemma _root_.MvPowerSeries.HasSubst.addInv_aux : MvPowerSeries.HasSubst ![X, (addInv_X F)] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by fin_cases x <;> simp

lemma addInv_trunc_aux :
    trunc (n + 1) (addInv_X F) =
      ∑ i : Fin (n + 1), Polynomial.C (addInv_aux F i.1) * Polynomial.X ^ i.1 := by
  induction n with
  | zero => simp [addInv_X]
  | succ k ih =>
    simp only [trunc_apply, Nat.Ico_zero_eq_range, Fin.sum_univ_eq_sum_range
      (fun i => (Polynomial.C (R := R)) (addInv_aux F i) * Polynomial.X ^ i)] at ⊢ ih
    rw [Finset.sum_range_add, ih]
    conv_rhs => rw [Finset.sum_range_add]
    simp [Polynomial.C_mul_X_pow_eq_monomial, addInv_X]

lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
    coeff n (F.toPowerSeries.subst ![X, (addInv_X F)]) =
      coeff n (F.toPowerSeries.subst ![X, (trunc (n + 1) (addInv_X F))]) := by
  have : trunc (n + 1) X = Polynomial.X (R := R):= trunc_X_of <| by omega
  rw [trunc_subst_trunc_add_one (MvPowerSeries.HasSubst.addInv_aux F)]
  congr! 3 with i
  fin_cases i <;>  simp [this]

lemma _root_.MvPowerSeries.HasSubst.addInv_fin :
    MvPowerSeries.HasSubst ![X, (∑ (i ∈ range (n + 1)), Polynomial.C (F.addInv_aux i) *
      Polynomial.X (R := R) ^ i).toPowerSeries] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)

lemma coeff_subst_sum_C_addInv_mul_X_pow_sub_X (n : ℕ) :
  (coeff n) (F.toPowerSeries.subst ![X, (∑ (i : Fin (n + 1)), Polynomial.C (F.addInv_aux i.1) *
    Polynomial.X (R := R) ^ i.1).toPowerSeries]) = 0 := by
  rw [sum_univ_eq_sum_range fun i => (Polynomial.C (F.addInv_aux i) * Polynomial.X (R := R) ^ i)]
  induction n with
  | zero =>
    simp only [_root_.zero_add, range_one, sum_singleton, addInv_aux_zero, map_zero,
      pow_zero, mul_one, Polynomial.coe_zero, coeff_zero_eq_constantCoeff, constantCoeff]
    rw [MvPowerSeries.constantCoeff_subst_eq_zero _ _ F.zero_constantCoeff]
    exact MvPowerSeries.HasSubst.X_zero
    simp
  | succ k ih =>
    by_cases hk : k = 0
    · rw [hk, show range 2 = {0, 1} by rfl, coeff, MvPowerSeries.coeff_subst
        (MvPowerSeries.hasSubst_of_constantCoeff_zero <| by simp)]
      · rw [finsum_eq_finsetSum_of_support_subset (s := {single 0 1, single 1 1}),
          sum_pair (ne_iff.mpr ⟨0, by simp⟩)]
        · simp [F.lin_coeff_X, F.lin_coeff_Y]
        have (x : Fin 2 →₀ ℕ) (h : ¬(MvPowerSeries.coeff x) F.toPowerSeries
          * (coeff 1) (X ^ x 0 * (-X) ^ x 1) = 0) : x = single 0 1 ∨ x = single 1 1 := by
          rw [neg_pow, coeff_X_pow_mul', coeff_mul_X_pow'] at h
          simp only [isValue, mul_ite, mul_zero, ite_eq_right_iff, Classical.not_imp] at h
          have : x 0 + x 1 ≤ 1 := by omega
          have x_one_le : x 1 ≤ 1 := Nat.le_of_add_left_le this
          by_cases hx₀ : x 0 = 0
          · by_cases hx₁ : x 1 = 0
            · have x_eq_zero : x = 0 := by ext n; fin_cases n <;> simpa
              simp [x_eq_zero] at h
            right; ext n; fin_cases n <;> grind
          · -- the cases x 0 ≠ 0
            have hx₀' : x 0 = 1 := by omega
            by_cases hx₁ : x 1 = 0
            · left; ext n; fin_cases n <;> simpa
            omega
        simpa
    simp_rw [coeff, MvPowerSeries.coeff_subst (MvPowerSeries.HasSubst.addInv_fin F (k + 1)),
      coeff_coeToMvPowerSeries]
    generalize hB : (∑ i ∈ range (k + 1), Polynomial.C (F.addInv_aux i) * Polynomial.X ^ i) = B
    have coeff_B : B.coeff 0 = 0 := by simp [← hB]
    calc
      _ = ∑ᶠ (d : Fin 2 →₀ ℕ), (MvPowerSeries.coeff d) F * (coeff (k + 1))
          (X ^ d 0 * (↑B + C (F.addInv_aux (k + 1)) * X ^ (k + 1)) ^ d 1) := by
        simp [sum_range_add, hB]
      _ = _ := by
        have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) (X ^ d 0 *
          (B.toPowerSeries + C (addInv_aux F (k + 1)) * X ^ (k + 1)) ^ d 1) =
            (coeff (k + 1)) (X ^ d 0 * B.toPowerSeries ^ d 1)
              + if d = single 1 1 then (addInv_aux F (k + 1)) else 0 := by
          rw [coeff_X_pow_mul', coeff_X_pow_mul']
          by_cases hd : d = single 1 1
          · simp [hd]
          rw [if_neg hd, _root_.add_zero]
          by_cases hd_le : d 0 ≤ k + 1
          · simp_rw [if_pos hd_le, add_pow, map_sum]
            rw [Finset.sum_eq_single (d 1) _ (by simp)]
            · simp
            · intro i hi_mem hi
              rw [mul_pow, mul_assoc, mul_assoc, mul_comm ((X ^ (k + 1)) ^ (d 1 - i)),
                ← mul_assoc, ← mul_assoc, ← pow_mul, coeff_mul_X_pow']
              by_cases! hd₀ : d 0 = 0 ∧ d 1 - i = 1
              · have i_ne_zero : i ≠ 0 := by grind
                simp [hd₀, coeff_B, zero_pow i_ne_zero]
              have : k + 1 ≤ (k + 1) * (d 1 - i) := by
                simp only [isValue, mem_range, Order.lt_add_one_iff, _root_.zero_le,
                  le_mul_iff_one_le_right] at ⊢ hi_mem
                omega
              rw [if_neg _]
              by_cases hd₀' : d 0 = 0
              · have aux : (k + 1) * 2 ≤ (k + 1) * (d 1 - i) :=
                  Nat.mul_le_mul_left _ (by grind only [= mem_range])
                omega
              omega
          simp_rw [if_neg hd_le]
        have Beq : B.toPowerSeries = ∑ i ∈ range (k + 1), C (F.addInv_aux i) * X ^ i := by
          ext n; simp [← hB]
        simp_rw [eq_aux, mul_add]
        rw [finsum_add_distrib]
        · nth_rw 2 [finsum_eq_single _ (single 1 1) fun d hd => by rw [if_neg hd, mul_zero]]
          · rw [if_pos rfl, F.lin_coeff_Y, one_mul, addInv_aux]
            · simp [sum_univ_eq_sum_range (fun i => (C (addInv_aux F i) * X ^ i)), ← Beq,
                coeff, MvPowerSeries.coeff_subst (hB ▸ MvPowerSeries.HasSubst.addInv_fin F k)]
            · exact hk
        · obtain h := MvPowerSeries.coeff_subst_finite
            (MvPowerSeries.HasSubst.addInv_fin F k) F.toPowerSeries
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hB, Finsupp.prod_pow, prod_univ_two,
            isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            smul_eq_mul] at h
          exact h _
        refine Set.Finite.subset (Set.finite_singleton (single 1 1))
          (Function.support_subset_iff'.mpr fun d hd => ?_)
        simp only [isValue, Set.mem_singleton_iff] at hd
        simp [hd]

/- Given a formal group law `F` over coefficient ring `R`, there exist a power series
`addInv_X F`, such that `F(X, (addInv_X F)) = 0`. -/
theorem subst_addInv_eq_zero : F.toPowerSeries.subst ![X, (addInv_X F)] = 0 := by
  ext n
  by_cases hn : n = 0
  · simp [hn, constantCoeff, MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.HasSubst.addInv_aux F) (by simp) F.zero_constantCoeff]
  rw [coeff_subst_addInv_trunc _ _ hn, addInv_trunc_aux, coeff_subst_sum_C_addInv_mul_X_pow_sub_X,
    map_zero]

variable (φ : MvPowerSeries σ R)

/-- For any multivariate power series `φ` with zero constant coefficient, `addInv F φ` is the
additive inverse of `φ` under formal group `F` sense. -/
def addInv : MvPowerSeries σ R := subst φ (addInv_X F)

@[simp]
theorem addInv_apply : addInv F φ = subst φ (addInv_X F) := rfl

instance : Neg (F.Point σ) where
  neg f := ⟨F.addInv f.val, MvPowerSeries.IsNilpotent_subst'
    f.prop.const (HasSubst.of_constantCoeff_zero' rfl)⟩

@[simp]
lemma neg_apply {f : F.Point σ} : (-f).val = F.addInv f.val := rfl

/-- For any multivariate power series `φ` with zero constant coefficient, then
`φ` plus (under `F` sense) additive inverse of `φ` (under `F` sense) equals zero. -/
theorem add_neg_cancel (f : F.Point σ) : f + (-f) = 0 := by
  apply Subtype.ext
  calc
    _ = subst f.val (MvPowerSeries.subst ![PowerSeries.X, addInv_X F] F.toPowerSeries) := by
      rw [subst, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.addInv_aux F)
        f.prop.const, add_apply]
      congr! 1
      funext s;
      fin_cases s
      · simp [X, MvPowerSeries.subst_X f.prop.const]
      · simp [neg_apply, subst]
    _ = _ := by
      rw [subst_addInv_eq_zero]; ext n
      simp [← coe_substAlgHom f.prop]

instance : AddGroup (F.Point σ) where
  zsmul := zsmulRec
  neg_add_cancel x := by
    rw [← _root_.add_zero (- x + x), ← F.add_neg_cancel (- x), ← _root_.add_assoc,
      _root_.add_assoc (-x), F.add_neg_cancel, _root_.add_zero]

instance [F.IsComm] : AddCommGroup (F.Point σ) where
  add_comm x y := Subtype.ext <| F.comm' x.prop y.prop

example [F.IsComm] (x y z : F.Point σ) :
    x + y + z = z + (x + y) := by
  abel

example [F.IsComm] {n : ℕ} (x y : F.Point σ) :
    n • (x + y) = n • x + n • y :=
  nsmul_add x y n

example [F.IsComm] {n : ℤ} (x y : F.Point σ) :
    n • (x + y) = n • x + n • y :=
  zsmul_add x y n

/-- Substituting a power series `Q` into `F(p, q)` equals `F(p(Q), q(Q))`. -/
lemma subst_subst_pair {p q : PowerSeries R} (hp : p.constantCoeff = 0) (hq : q.constantCoeff = 0)
    {τ : Type*} {Q : MvPowerSeries τ R} (hQ : PowerSeries.HasSubst Q) :
    PowerSeries.subst Q (F.toPowerSeries.subst ![p, q])
      = F.toPowerSeries.subst ![PowerSeries.subst Q p, PowerSeries.subst Q q] := by
  rw [PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp [hp, hq])) hQ.const]
  refine MvPowerSeries.subst_congr ?_
  funext s
  fin_cases s <;> rfl

/-- The substitution `F(p(X₀), p(X₁))` written with an explicit pair. -/
lemma subst_toMv (p : PowerSeries R) :
    F.toPowerSeries.subst (fun i : Fin 2 => p.toMvPowerSeries i)
      = F.toPowerSeries.subst ![p.toMvPowerSeries 0, p.toMvPowerSeries 1] :=
  MvPowerSeries.subst_congr (by funext s; fin_cases s <;> rfl)

/-- The medial (interchange) law for a commutative formal group law:
`F(F(a, b), F(c, d)) = F(F(a, c), F(b, d))`. -/
lemma medial [F.IsComm] {a b c d : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b)
    (hc : PowerSeries.HasSubst c) (hd : PowerSeries.HasSubst d) :
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![a, b], F.toPowerSeries.subst ![c, d]]
      = F.toPowerSeries.subst ![F.toPowerSeries.subst ![a, c], F.toPowerSeries.subst ![b, d]] := by
  have hsubst : ∀ {x y : MvPowerSeries σ R}, PowerSeries.HasSubst x → PowerSeries.HasSubst y →
      PowerSeries.HasSubst (F.toPowerSeries.subst ![x, y]) := by
    intro x y hx hy
    refine MvPowerSeries.IsNilpotent_subst' ?_ (F.zero_constantCoeff ▸ IsNilpotent.zero)
    refine MvPowerSeries.hasSubst_of_constantCoeff_nilpotent ?_
    intro s
    fin_cases s
    · exact hx
    · exact hy
  calc
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![a, b], F.toPowerSeries.subst ![c, d]]
        = F.toPowerSeries.subst ![a, F.toPowerSeries.subst ![b, F.toPowerSeries.subst ![c, d]]] :=
          F.assoc' ha hb (hsubst hc hd)
    _ = F.toPowerSeries.subst ![a, F.toPowerSeries.subst ![F.toPowerSeries.subst ![b, c], d]] := by
          rw [← F.assoc' hb hc hd]
    _ = F.toPowerSeries.subst ![a, F.toPowerSeries.subst ![F.toPowerSeries.subst ![c, b], d]] := by
          rw [F.comm' hb hc]
    _ = F.toPowerSeries.subst ![a, F.toPowerSeries.subst ![c, F.toPowerSeries.subst ![b, d]]] := by
          rw [F.assoc' hc hb hd]
    _ = F.toPowerSeries.subst ![F.toPowerSeries.subst ![a, c], F.toPowerSeries.subst ![b, d]] :=
          (F.assoc' ha hc (hsubst hb hd)).symm

def add_hom [F.IsComm] (f g : FormalGroupHom F F) : FormalGroupHom F F where
  toPowerSeries := F.toPowerSeries.subst ![f.toPowerSeries, g.toPowerSeries]
  zero_constantCoeff := by
    refine MvPowerSeries.constantCoeff_subst_eq_zero ?_ ?_ F.zero_constantCoeff
    · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      simp [f.zero_constantCoeff, g.zero_constantCoeff]
    · simp [f.zero_constantCoeff, g.zero_constantCoeff]
  hom := by
    have fhom : PowerSeries.subst F.toPowerSeries f.toPowerSeries
        = F.toPowerSeries.subst (fun i : Fin 2 => f.toPowerSeries.toMvPowerSeries i) := f.hom
    have ghom : PowerSeries.subst F.toPowerSeries g.toPowerSeries
        = F.toPowerSeries.subst (fun i : Fin 2 => g.toPowerSeries.toMvPowerSeries i) := g.hom
    have hh : ∀ i : Fin 2,
        (PowerSeries.toMvPowerSeries i) (F.toPowerSeries.subst ![f.toPowerSeries, g.toPowerSeries])
          = F.toPowerSeries.subst
              ![f.toPowerSeries.toMvPowerSeries i, g.toPowerSeries.toMvPowerSeries i] := by
      intro i
      rw [PowerSeries.toMvPowerSeries_apply,
        F.subst_subst_pair f.zero_constantCoeff g.zero_constantCoeff (PowerSeries.HasSubst.X i)]
      simp only [← PowerSeries.toMvPowerSeries_apply]
    show PowerSeries.subst F.toPowerSeries
          (F.toPowerSeries.subst ![f.toPowerSeries, g.toPowerSeries])
        = F.toPowerSeries.subst
            (fun i : Fin 2 =>
              (PowerSeries.toMvPowerSeries i)
                (F.toPowerSeries.subst ![f.toPowerSeries, g.toPowerSeries]))
    rw [F.subst_subst_pair f.zero_constantCoeff g.zero_constantCoeff
          (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
      fhom, ghom, F.subst_toMv f.toPowerSeries, F.subst_toMv g.toPowerSeries,
      F.subst_toMv (F.toPowerSeries.subst ![f.toPowerSeries, g.toPowerSeries]), hh 0, hh 1]
    exact F.medial ((PowerSeries.HasSubst.toMvPowerSeries f.zero_constantCoeff).const_coeff 0)
      ((PowerSeries.HasSubst.toMvPowerSeries f.zero_constantCoeff).const_coeff 1)
      ((PowerSeries.HasSubst.toMvPowerSeries g.zero_constantCoeff).const_coeff 0)
      ((PowerSeries.HasSubst.toMvPowerSeries g.zero_constantCoeff).const_coeff 1)

end FormalGroup


-- module
-- public import FormalGroupLaws.Basic
-- public import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators

-- @[expose] public section

-- noncomputable section

-- variable {R : Type*} [CommRing R] [Nontrivial R] (f g : PowerSeries R) (F : FormalGroup R) {σ : Type*}
--   (φ : MvPowerSeries (Fin 2) R) (n : ℕ)


-- open PowerSeries FormalGroup Finset


-- abbrev FormalGroup.addInv_aux (F : FormalGroup R): ℕ → R
--   | 0 => 0
--   | 1 => -1
--   | n + 1 => - (coeff (n + 1) (MvPowerSeries.subst
--     ![X, (∑ i : Fin (n + 1), C (addInv_aux F i.1) * X ^ i.1)] F.toPowerSeries))

-- abbrev FormalGroup.addInv_aux' (F : FormalGroup R): ℕ → R
--   | 0 => 0
--   | 1 => -1
--   | n + 1 => - (coeff (n + 1 : ℕ) (MvPowerSeries.subst
--     ![(∑ i : Fin (n + 1), C (addInv_aux' F i.1) * X ^ i.1), X] F.toPowerSeries))

-- /-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `ι`,
--   such that `F(X, ι(X)) = 0`. -/
-- def FormalGroup.addInv_X := PowerSeries.mk (fun n => (FormalGroup.addInv_aux F n))

-- /-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `ι`,
--   such that `F(ι(X), X) = 0`. -/
-- def FormalGroup.addInv_X_left := PowerSeries.mk (fun n => (FormalGroup.addInv_aux' F n))

-- lemma Finset.sum_fin_eq_sum_range' {β : Type*} [AddCommMonoid β] {n : ℕ}  (f : ℕ → β) :
--   ∑ i : Fin n, f i.1 = ∑ i ∈ range n, f i := by
--   rw [Fin.sum_univ_eq_sum_range]

-- omit [Nontrivial R] in
-- lemma HasSubst.addInv_aux : MvPowerSeries.HasSubst ![X, (addInv_X F)] := by
--   refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--   intro x; fin_cases x
--   · simp
--   · simp [addInv_X]; rw [FormalGroup.addInv_aux]

-- omit [Nontrivial R] in
-- lemma HasSubst.addInv_aux' : MvPowerSeries.HasSubst ![(addInv_X_left F), X] := by
--   refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--   intro x; fin_cases x
--   · simp [addInv_X_left]; rw [FormalGroup.addInv_aux']
--   · simp

-- omit [Nontrivial R] in
-- lemma addInv_trunc_aux :
--   trunc (n + 1) (addInv_X F) = ∑ i : Fin (n + 1), Polynomial.C (addInv_aux F i.1)
--   * Polynomial.X ^ i.1 := by
--   induction n with
--   | zero => simp [addInv_X]
--   | succ k ih =>
--     rw [trunc_apply] at ⊢ ih
--     simp [sum_fin_eq_sum_range'
--       (fun i => (Polynomial.C (R := R)) (addInv_aux F i) * Polynomial.X ^ i)] at ⊢ ih

--     rw [Finset.sum_range_add, ih]
--     conv_rhs => rw [Finset.sum_range_add]
--     simp [Polynomial.C_mul_X_pow_eq_monomial, FormalGroup.addInv_X]

-- omit [Nontrivial R] in
-- lemma coeff_subst_map₂_eq_subst_subst_map₂_trunc (hf : constantCoeff f = 0)
--   (hg : constantCoeff g = 0) :
--   coeff n (MvPowerSeries.subst ![f, g] φ) =
--   coeff n (MvPowerSeries.subst ![(trunc (n + 1) f), (trunc (n + 1) g)] φ) := by
--   rw [coeff, MvPowerSeries.coeff_subst (HasSubst.FinPairing  hf hg),
--     MvPowerSeries.coeff_subst (HasSubst.FinPairing  (by simp [coeff_trunc, hf])
--     (by simp [coeff_trunc, hg]))]
--   simp; apply finsum_congr
--   intro d
--   congr! 1
--   rw [coeff_mul, coeff_mul, sum_congr rfl]
--   intro x hx
--   simp at hx
--   congr! 1
--   · rw [coeff_pow, coeff_pow, sum_congr rfl]
--     simp
--     intro l hl₁ hl₂
--     rw [prod_congr rfl]
--     intro s hs
--     have aux : l s < n + 1 := by
--       calc
--         _ ≤ (range (d 0)).sum ⇑l := by
--           exact Finset.single_le_sum_of_canonicallyOrdered hs
--         _ < n + 1 := by
--           linarith
--     rw [coeff_trunc, if_pos aux]
--   · rw [coeff_pow, coeff_pow, sum_congr rfl]
--     simp
--     intro l hl₁ hl₂
--     rw [prod_congr rfl]
--     intro s hs
--     have aux : l s < n + 1 := by
--       calc
--         _ ≤ (range (d 1)).sum ⇑l := by
--           exact Finset.single_le_sum_of_canonicallyOrdered hs
--         _ < n + 1 := by
--           linarith
--     rw [coeff_trunc, if_pos aux]




-- omit [Nontrivial R] in
-- lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
--   coeff n (MvPowerSeries.subst ![X, (addInv_X F)] F.toPowerSeries) =
--   coeff n (MvPowerSeries.subst ![X, (trunc (n + 1) (addInv_X F))] F.toPowerSeries) := by
--   have trunc_X_aux : trunc (n + 1) X = Polynomial.X (R := R):= by
--     refine trunc_X_of ?_
--     omega
--   have constant_aux : constantCoeff (addInv_X F) = 0 := by
--     simp [addInv_X]
--     rw [FormalGroup.addInv_aux]
--   rw [coeff_subst_map₂_eq_subst_subst_map₂_trunc _ _ _ _ constantCoeff_X constant_aux]
--   simp [trunc_X_aux]

-- omit [Nontrivial R] in
-- lemma coeff_subst_addInv_left_trunc (hn : n ≠ 0) :
--   coeff n (MvPowerSeries.subst ![(addInv_X_left F), X] F.toPowerSeries) =
--   coeff n (MvPowerSeries.subst ![(trunc (n + 1) (addInv_X_left F)), X] F.toPowerSeries) := by
--   have trunc_X_aux : trunc (n + 1) X = Polynomial.X (R := R):= by
--     refine trunc_X_of ?_
--     omega
--   have constant_aux : constantCoeff (addInv_X_left F) = 0 := by
--     simp [addInv_X_left]
--     rw [FormalGroup.addInv_aux']
--   rw [coeff_subst_map₂_eq_subst_subst_map₂_trunc _ _ _ _ constant_aux constantCoeff_X]
--   simp [ trunc_X_aux]


-- -- lemma FormalGroup.coeff_X₀_pow {k : ℕ} (hk : k ≥ 2) :
-- --   MvPowerSeries.coeff (Finsupp.single 0 k) F.toPowerSeries = 0 := by
-- --   sorry



-- -- lemma FormalGroup.coeff_X₁_pow {k : ℕ} (hk : k ≥ 2) :
-- --   MvPowerSeries.coeff (Finsupp.single 1 k) F.toPowerSeries = 0 := by
-- --   sorry


-- lemma coeff_n_aux (n : ℕ):
--   coeff n (MvPowerSeries.subst ![X, (∑ i : Fin (n + 1),
--   C (addInv_aux F i.1) * X ^ i.1)] F.toPowerSeries) = 0 := by
--   rw [sum_fin_eq_sum_range' (fun i => (C (addInv_aux F i) * X ^ i))]
--   induction n with
--   | zero =>
--     simp
--     rw [constantCoeff, MvPowerSeries.constantCoeff_subst, show (addInv_aux F 0) = 0 by
--       rw [FormalGroup.addInv_aux]]
--     simp
--     apply finsum_eq_zero_of_forall_eq_zero
--     intro d
--     by_cases hd₀ : d 0 ≠ 0
--     · simp [hd₀]
--     by_cases hd₁ : d 1 ≠ 0
--     · simp [hd₁]
--     have d_eq_zero : d = 0 := by ext x; fin_cases x <;> simp_all
--     simp [d_eq_zero, F.zero_constantCoeff]
--     · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--       intro x
--       fin_cases x
--       all_goals simp [show (addInv_aux F 0) = 0 by rw [FormalGroup.addInv_aux]]
--   | succ k ih =>
--     by_cases hk₀ : k = 0
--     · simp [hk₀, show range 2 = {0, 1} by rfl]
--       rw [coeff, MvPowerSeries.coeff_subst]
--       unfold addInv_aux
--       simp
--       have supp_eq : (Function.support (fun d => (MvPowerSeries.coeff d) F.toPowerSeries
--         * (coeff 1) (X ^ d 0 * (-X) ^ d 1))) = {Finsupp.single (0 : Fin 2) 1,
--         Finsupp.single (1 : Fin 2) 1}
--         := by
--         refine Function.support_eq_iff.mpr ?_
--         constructor
--         · intro x hx
--           simp at hx
--           obtain hx | hx := hx
--           · simp [hx, F.lin_coeff_X]
--           · simp [hx, F.lin_coeff_Y]
--         intro  x hx
--         simp at hx
--         obtain ⟨neq₁, neq₂⟩ := hx
--         by_cases hx₀ : x 0 = 0
--         · by_cases hx₁ : x 1 = 0
--           · have x_zero : x = 0 := by
--               ext i; fin_cases i <;> simp [hx₀, hx₁]
--             simp [x_zero, F.zero_constantCoeff]
--           have xge₁ : x 1 ≥ 2 := by
--             by_contra hc
--             have xeq : x 1 = 1 := by omega
--             have xeq' : x = Finsupp.single 1 1 := by
--               ext i; fin_cases i <;> simp [hx₀, xeq]
--             contradiction
--           simp [hx₀, neg_pow X _]
--           rw [coeff_mul_X_pow', if_neg (by linarith)]
--           simp
--         rw [coeff_X_pow_mul']
--         by_cases hx₁ : x 0 = 1
--         · rw [if_pos (by linarith)]
--           by_cases hx₂ : x 1 = 0
--           · have xeq : x = Finsupp.single 0 1 := by
--               ext i; fin_cases i <;> simp [hx₂, hx₁]
--             contradiction
--           simp [hx₁, zero_pow hx₂]
--         have xgt : ¬ x 0 ≤ 1 := by omega
--         simp [if_neg xgt]
--       have supp_fin : (Function.support (fun d => (MvPowerSeries.coeff d) F.toPowerSeries
--         * (coeff 1) (X ^ d 0 * (-X) ^ d 1))).Finite := by
--         simp [supp_eq]
--       rw [finsum_eq_sum _ supp_fin]
--       simp_all
--       rw [sum_pair (Finsupp.ne_iff.mpr (by use 0; simp))]
--       simp [F.lin_coeff_X, F.lin_coeff_Y]
--       · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--         intro s; fin_cases s
--         · rw [addInv_aux]; simp
--         · unfold addInv_aux
--           simp
--     -- second case: k ≠ 0
--     have has_subst₁ (m : ℕ) : MvPowerSeries.HasSubst ![X, (∑ i ∈ range (m + 1),
--       C (addInv_aux F i) * X ^ i)] := by
--       refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--       intro x; fin_cases x
--       · simp
--       · simp
--         refine sum_eq_zero ?_
--         intro i hi
--         by_cases hi₀ : i ≠ 0
--         · simp [zero_pow hi₀]
--         · simp_all
--           rw [FormalGroup.addInv_aux]
--     rw [coeff, MvPowerSeries.coeff_subst (has_subst₁ (k + 1))]
--     simp_rw [PowerSeries.coeff_coe]
--     simp
--     generalize hB : ∑ i ∈ range (k + 1), C (addInv_aux F i) * X ^ i = B
--     simp [sum_range_add, hB]
--     have constantCoeff_of_B : constantCoeff B = 0 := by
--       rw [←hB, map_sum]
--       apply sum_eq_zero
--       intro x hx
--       rw [←smul_eq_C_mul, constantCoeff_smul, map_pow, constantCoeff_X, smul_eq_mul]
--       by_cases hx' : x = 0
--       · simp [hx', show addInv_aux F 0 = 0 by rw [FormalGroup.addInv_aux]]
--       · simp [zero_pow hx']
--     obtain has_subst' := has_subst₁ k
--     rw [hB] at has_subst'
--     have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) (X ^ d 0 *
--       (B + C (addInv_aux F (k + 1)) * X ^ (k + 1)) ^ d 1) = (coeff (k + 1)) (X ^ d 0 * B ^ d 1)
--       + if d = Finsupp.single 1 1 then (addInv_aux F (k + 1)) else 0 := by
--       split_ifs with hd
--       · simp [hd, ←hB, coeff_X_pow]
--       rw [coeff_X_pow_mul', coeff_X_pow_mul']
--       split_ifs with hd₁
--       ·
--         by_cases hd₂ : d 0 = 0
--         ·
--           simp [hd₂]
--           rw [add_pow, map_sum, sum_eq_single (d 1)]
--           simp
--           · intro i hi₀ hi₁
--             simp at hi₀
--             rw [mul_pow, ←pow_mul, ←map_pow]
--             calc
--               _ = (coeff (k + 1)) (B ^ i * (C ((addInv_aux F (k + 1)) ^ (d 1 - i)) * X ^ ((k + 1)
--                 * (d 1 - i))) * (C ((d 1).choose i : R))) := by
--                 rfl
--               _ = (coeff (k + 1)) (C ((addInv_aux F (k + 1)) ^ (d 1 - i))
--                 * (C ((d 1).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 1 - i))) := by
--                 ring_nf
--               _ = _ := by
--                 rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow']
--                 by_cases hi' : i = d 1 - 1
--                 · have d_minus : d 1 - i = 1 := by omega
--                   have ine_zero : i ≠ 0 := by
--                     by_contra hc
--                     have deq : d = Finsupp.single 1 1 := by
--                       ext s; fin_cases s <;> simp [hd₂]; omega
--                     contradiction
--                   simp [d_minus, constantCoeff_of_B, zero_pow ine_zero]
--                 have d_minus_ge : d 1 - i ≥ 2 := by
--                   omega
--                 have gt_aux : ¬ (k + 1) * (d 1 - i) ≤ k + 1 := by
--                   simp
--                   omega
--                 rw [if_neg gt_aux, mul_zero]
--           simp
--         -- have lt_aux : (k + 1 - d 0) < k + 1 := by omega
--         rw [add_pow, map_sum, sum_eq_single (d 1)]
--         · simp
--         · intro i hi₀ hi₁
--           simp at hi₀
--           rw [mul_pow, ←pow_mul, ←map_pow]
--           calc
--             _ = (coeff (k + 1 - d 0)) (B ^ i * (C ((addInv_aux F (k + 1)) ^ (d 1 - i)) * X ^ ((k + 1)
--               * (d 1 - i))) * (C ((d 1).choose i : R))) := by
--               rfl
--             _ = (coeff (k + 1 - d 0)) (C ((addInv_aux F (k + 1)) ^ (d 1 - i))
--               * (C ((d 1).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 1 - i))) := by
--               ring_nf
--             _ = _ := by
--               rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow', if_neg]
--               · simp
--               · simp
--                 calc
--                   _ < k + 1 := by omega
--                   _ ≤ _ := by
--                     have le_aux : d 1 - i ≥ 1 := by omega
--                     exact Nat.le_mul_of_pos_right (k + 1) le_aux
--         · simp
--       simp
--     simp_rw [eq_aux, mul_add]
--     rw [finsum_add_distrib]
--     nth_rw 2 [finsum_eq_single _ (Finsupp.single 1 1)]
--     rw [if_pos (by simp), F.lin_coeff_Y, addInv_aux,
--       sum_fin_eq_sum_range' (fun i => (C (addInv_aux F i) * X ^ i)), hB, coeff, MvPowerSeries.coeff_subst has_subst']
--     simp
--     · simp [hk₀]
--     · intro d hd
--       simp [if_neg hd]
--     · obtain h := MvPowerSeries.coeff_subst_finite (has_subst₁ k) F.toPowerSeries
--       simp [hB] at h
--       exact h (Finsupp.single () (k + 1))
--     · have aux : (Function.support fun d ↦
--         (MvPowerSeries.coeff d) F.toPowerSeries * if d = Finsupp.single 1 1 then addInv_aux F (k + 1) else 0)
--         ⊆ {Finsupp.single 1 1} := by
--         refine Function.support_subset_iff'.mpr ?_
--         intro d hd
--         simp at hd
--         simp [if_neg hd]
--       exact Set.Finite.subset (Set.finite_singleton (Finsupp.single 1 1)) aux

-- /-- this is use to construct the left inverse of `X` under the sense of formal group. -/
-- lemma coeff_n_aux' (n : ℕ):
--   coeff n (MvPowerSeries.subst ![(∑ i : Fin (n + 1),
--   C (addInv_aux' F i.1) * X ^ i.1), X] F.toPowerSeries) = 0 := by
--   rw [sum_fin_eq_sum_range' (fun i => (C (addInv_aux' F i) * X ^ i))]
--   induction n with
--   | zero =>
--     simp
--     rw [constantCoeff, MvPowerSeries.constantCoeff_subst, show (addInv_aux' F 0) = 0 by
--       rw [FormalGroup.addInv_aux']]
--     simp
--     apply finsum_eq_zero_of_forall_eq_zero
--     intro d
--     by_cases hd₀ : d 0 ≠ 0
--     · simp [hd₀]
--     by_cases hd₁ : d 1 ≠ 0
--     · simp [hd₁]
--     have d_eq_zero : d = 0 := by ext x; fin_cases x <;> simp_all
--     simp [d_eq_zero, F.zero_constantCoeff]
--     · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--       intro x
--       fin_cases x
--       all_goals simp [show (addInv_aux' F 0) = 0 by rw [FormalGroup.addInv_aux']]
--   | succ k ih =>
--     by_cases hk₀ : k = 0
--     · simp [hk₀, show range 2 = {0, 1} by rfl]
--       rw [coeff, MvPowerSeries.coeff_subst]
--       unfold addInv_aux'
--       simp
--       have supp_eq : (Function.support (fun d => (MvPowerSeries.coeff d) F.toPowerSeries
--         * (coeff 1) ((-X) ^ d 0 * X ^ d 1))) = {Finsupp.single (0 : Fin 2) 1,
--         Finsupp.single (1 : Fin 2) 1} := by
--         refine Function.support_eq_iff.mpr ?_
--         constructor
--         · intro x hx
--           simp at hx
--           obtain hx | hx := hx
--           · simp [hx, F.lin_coeff_X]
--           · simp [hx, F.lin_coeff_Y]
--         intro  x hx
--         simp at hx
--         obtain ⟨neq₁, neq₂⟩ := hx
--         by_cases hx₀ : x 1 = 0
--         · by_cases hx₁ : x 0 = 0
--           · have x_zero : x = 0 := by
--               ext i; fin_cases i <;> simp [hx₀, hx₁]
--             simp [x_zero, F.zero_constantCoeff]
--           have xge₁ : x 0 ≥ 2 := by
--             by_contra hc
--             have xeq : x 0 = 1 := by omega
--             have xeq' : x = Finsupp.single 0 1 := by
--               ext i; fin_cases i <;> simp [hx₀, xeq]
--             contradiction
--           simp [hx₀, neg_pow X _]
--           rw [coeff_mul_X_pow', if_neg (by linarith)]
--           simp
--         rw [coeff_mul_X_pow']
--         by_cases hx₁ : x 1 = 1
--         · rw [if_pos (by linarith)]
--           by_cases hx₂ : x 0 = 0
--           · have xeq : x = Finsupp.single 1 1 := by
--               ext i; fin_cases i <;> simp [hx₂, hx₁]
--             contradiction
--           simp [hx₁, zero_pow hx₂]
--         have xgt : ¬ x 1 ≤ 1 := by omega
--         simp [if_neg xgt]
--       have supp_fin : (Function.support (fun d => (MvPowerSeries.coeff d) F.toPowerSeries
--         * (coeff 1) ((-X) ^ d 0 * (X) ^ d 1))).Finite := by
--         simp [supp_eq]
--       rw [finsum_eq_sum _ supp_fin]
--       simp_all
--       rw [sum_pair (Finsupp.ne_iff.mpr (by use 0; simp))]
--       simp [F.lin_coeff_X, F.lin_coeff_Y]
--       · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--         intro s; fin_cases s
--         · simp; rw [FormalGroup.addInv_aux']
--         · simp
--     have has_subst₁ (m : ℕ) : MvPowerSeries.HasSubst ![(∑ i ∈ range (m + 1),
--       C (addInv_aux' F i) * X ^ i), X] := by
--       refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--       intro x; fin_cases x
--       · simp
--         refine sum_eq_zero ?_
--         intro i hi
--         by_cases hi₀ : i ≠ 0
--         · simp [zero_pow hi₀]
--         · simp at hi₀
--           simp [hi₀]
--           rw [FormalGroup.addInv_aux']
--       · simp
--     rw [coeff, MvPowerSeries.coeff_subst (has_subst₁ (k + 1))]
--     simp_rw [PowerSeries.coeff_coe]
--     simp
--     generalize hB : ∑ i ∈ range (k + 1), C (addInv_aux' F i) * X ^ i = B
--     simp [sum_range_add, hB]
--     have constantCoeff_of_B : constantCoeff B = 0 := by
--       rw [←hB, map_sum]
--       apply sum_eq_zero
--       intro x hx
--       rw [←smul_eq_C_mul, constantCoeff_smul, map_pow, constantCoeff_X, smul_eq_mul]
--       by_cases hx' : x = 0
--       · simp [hx', show addInv_aux' F 0 = 0 by rw [FormalGroup.addInv_aux']]
--       · simp [zero_pow hx']
--     obtain has_subst' := has_subst₁ k
--     rw [hB] at has_subst'
--     have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) ( (B + C (addInv_aux' F (k + 1))
--       * X ^ (k + 1)) ^ d 0 * X ^ d 1) = (coeff (k + 1)) (B ^ d 0 * X ^ d 1)
--       + if d = Finsupp.single 0 1 then (addInv_aux' F (k + 1)) else 0 := by
--       split_ifs with hd
--       · simp [hd, ←hB, coeff_X_pow]
--       rw [coeff_mul_X_pow', coeff_mul_X_pow']
--       split_ifs with hd₁
--       · by_cases hd₂ : d 1 = 0
--         · simp [hd₂]
--           rw [add_pow, map_sum, sum_eq_single (d 0)]
--           simp
--           · intro i hi₀ hi₁
--             simp at hi₀
--             rw [mul_pow, ←pow_mul, ←map_pow]
--             calc
--               _ = (coeff (k + 1)) (B ^ i * (C ((addInv_aux' F (k + 1)) ^ (d 0 - i)) * X ^ ((k + 1)
--                 * (d 0 - i))) * (C ((d 0).choose i : R))) := by
--                 rfl
--               _ = (coeff (k + 1)) (C ((addInv_aux' F (k + 1)) ^ (d 0 - i))
--                 * (C ((d 0).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 0 - i))) := by
--                 ring_nf
--               _ = _ := by
--                 rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow']
--                 by_cases hi' : i = d 0 - 1
--                 · have d_minus : d 0 - i = 1 := by omega
--                   have ine_zero : i ≠ 0 := by
--                     by_contra hc
--                     have deq : d = Finsupp.single 0 1 := by
--                       ext s; fin_cases s <;> simp [hd₂]; omega
--                     contradiction
--                   simp [d_minus, constantCoeff_of_B, zero_pow ine_zero]
--                 have d_minus_ge : d 0 - i ≥ 2 := by
--                   omega
--                 have gt_aux : ¬ (k + 1) * (d 0 - i) ≤ k + 1 := by
--                   simp
--                   omega
--                 rw [if_neg gt_aux]
--                 simp
--           simp
--         -- have lt_aux : (k + 1 - d 0) < k + 1 := by omega
--         rw [add_pow, map_sum, sum_eq_single (d 0)]
--         · simp
--         · intro i hi₀ hi₁
--           simp at hi₀
--           rw [mul_pow, ←pow_mul, ←map_pow]
--           calc
--             _ = (coeff (k + 1 - d 1)) (B ^ i * (C ((addInv_aux' F (k + 1)) ^ (d 0 - i)) * X ^ ((k + 1)
--               * (d 0 - i))) * (C ((d 0).choose i : R))) := by
--               rfl
--             _ = (coeff (k + 1 - d 1)) (C ((addInv_aux' F (k + 1)) ^ (d 0 - i))
--               * (C ((d 0).choose i : R)) * B ^ i * X ^ ((k + 1) * (d 0 - i))) := by
--               ring_nf
--             _ = _ := by
--               rw [←map_mul, mul_assoc, coeff_C_mul, coeff_mul_X_pow', if_neg]
--               · simp
--               · simp
--                 calc
--                   _ < k + 1 := by omega
--                   _ ≤ _ := by
--                     have le_aux : d 0 - i ≥ 1 := by omega
--                     exact Nat.le_mul_of_pos_right (k + 1) le_aux
--         · simp
--       simp
--     simp_rw [eq_aux, mul_add]
--     rw [finsum_add_distrib]
--     nth_rw 2 [finsum_eq_single _ (Finsupp.single 0 1)]
--     rw [if_pos (by simp), F.lin_coeff_X, addInv_aux',
--       sum_fin_eq_sum_range' (fun i => (C (addInv_aux' F i) * X ^ i)), hB, coeff, MvPowerSeries.coeff_subst has_subst']
--     simp
--     · simp [hk₀]
--     · intro d hd
--       simp [if_neg hd]
--     · obtain h := MvPowerSeries.coeff_subst_finite (has_subst₁ k) F.toPowerSeries
--       simp [hB] at h
--       exact h (Finsupp.single () (k + 1))
--     · have aux : (Function.support fun d ↦
--         (MvPowerSeries.coeff d) F.toPowerSeries * if d = Finsupp.single 0 1 then addInv_aux' F (k + 1) else 0)
--         ⊆ {Finsupp.single 0 1} := by
--         refine Function.support_subset_iff'.mpr ?_
--         intro d hd
--         simp at hd
--         simp [if_neg hd]
--       exact Set.Finite.subset (Set.finite_singleton (Finsupp.single 0 1)) aux


-- /- Given a formal group law `F` over coefficient ring `R`, there exist a power series
--   `addInv F`, such that `F(X, (addInv_X F)) = 0`. -/
-- theorem subst_addInv_eq_zero : MvPowerSeries.subst ![X, (addInv_X F)] F.toPowerSeries = 0 := by
--   ext n
--   by_cases hn : n = 0
--   · simp [hn, constantCoeff, MvPowerSeries.constantCoeff_subst (HasSubst.addInv_aux _)]
--     apply finsum_eq_zero_of_forall_eq_zero
--     intro d
--     by_cases hd₀ : d 0 ≠ 0
--     · simp [zero_pow hd₀]
--     by_cases hd₁ : d 1 ≠ 0
--     · have eq_aux : constantCoeff F.addInv_X = 0 := by
--         simp [addInv_X]; rw [FormalGroup.addInv_aux]
--       simp [eq_aux, zero_pow hd₁]
--     simp_all
--     have d_eq_zero : d = 0 := by
--       ext x
--       fin_cases x <;> simp [hd₀, hd₁]
--     simp [d_eq_zero, F.zero_constantCoeff]
--   simp [← (coeff_n_aux F n), coeff_subst_addInv_trunc _ _ hn]
--   congr! 3
--   simp_rw [trunc_apply, ←Polynomial.coe_C, ←Polynomial.coe_X]
--   rw [sum_fin_eq_sum_range' (fun i => (Polynomial.C (addInv_aux F i) : PowerSeries R)
--     * (Polynomial.X).toPowerSeries ^ i), Nat.Ico_zero_eq_range,
--     ←Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_finsetSum, ←Polynomial.eval₂_C_X_eq_coe,
--     sum_congr rfl]
--   intro i hi
--   rw [Polynomial.eval₂_C_X_eq_coe]
--   simp [X_pow_eq, addInv_X]
--   rw [←monomial_zero_eq_C_apply, monomial_mul_monomial]
--   simp


-- /- Given a formal group law `F` over coefficient ring `R`, there exist a power series
--   `addInv F`, such that `F(X, (addInv_X F)) = 0`. -/
-- theorem subst_addInv_eq_zero_left : MvPowerSeries.subst ![(addInv_X_left F), X] F.toPowerSeries = 0 := by
--   ext n
--   by_cases hn : n = 0
--   · simp [hn, constantCoeff, MvPowerSeries.constantCoeff_subst (HasSubst.addInv_aux' _)]
--     apply finsum_eq_zero_of_forall_eq_zero
--     intro d
--     by_cases hd₀ : d 1 ≠ 0
--     · simp [zero_pow hd₀]
--     by_cases hd₁ : d 0 ≠ 0
--     · have eq_aux : constantCoeff F.addInv_X_left = 0 := by
--         simp [addInv_X_left]; rw [FormalGroup.addInv_aux']
--       simp [eq_aux, zero_pow hd₁]
--     simp_all
--     have d_eq_zero : d = 0 := by
--       ext x
--       fin_cases x <;> simp [hd₀, hd₁]
--     simp [d_eq_zero, F.zero_constantCoeff]
--   simp
--   rw [←(coeff_n_aux' F n), coeff_subst_addInv_left_trunc _ _ hn]
--   congr! 3
--   simp_rw [trunc_apply, ←Polynomial.coe_C, ←Polynomial.coe_X]
--   rw [sum_fin_eq_sum_range' (fun i => (Polynomial.C (addInv_aux' F i) : PowerSeries R)
--     * (Polynomial.X).toPowerSeries ^ i), Nat.Ico_zero_eq_range,
--     ←Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_finsetSum, ←Polynomial.eval₂_C_X_eq_coe,
--     sum_congr rfl]
--   intro i hi
--   rw [Polynomial.eval₂_C_X_eq_coe]
--   simp [X_pow_eq, addInv_X_left]
--   rw [←monomial_zero_eq_C_apply, monomial_mul_monomial]
--   simp

-- -- /-- `-[F] f` means `FormalGroup.addInv F f`. -/
-- -- scoped[FormalGroup] notation:65 " -[" F:0 "] " f:66 =>
-- --   subst f addInv F

-- def addInv (F : FormalGroup R) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
--   subst f (addInv_X F)


-- /-- Given any formal group law `F`, `X + [F] addInv (X) = 0`. -/
-- theorem FormalGroup.X_add_addInv_X_eq_zero : X +[F] addInv_X (F) = 0 := by
--   simp [add, subst_addInv_eq_zero]


-- omit [Nontrivial R] in
-- variable {F} in
-- lemma constantCoeff_addInvF_X : MvPowerSeries.constantCoeff (addInv F X) = 0 := by
--   simp [addInv]
--   rfl

-- omit [Nontrivial R] in
-- variable {F} in
-- lemma constantCoeff_addInvF_X₀ : MvPowerSeries.constantCoeff (addInv F X₀) = 0 := by
--   simp [addInv]
--   rw [PowerSeries.subst, constantCoeff_subst_zero (by simp) _]
--   rw [addInv_X, PowerSeries.constantCoeff_coe, constantCoeff_mk, FormalGroup.addInv_aux]



-- omit [Nontrivial R] in
-- variable {F} in
-- lemma constantCoeff_addInvF_X₁ : MvPowerSeries.constantCoeff (addInv F X₁) = 0 := by
--   simp [addInv]
--   rw [PowerSeries.subst, constantCoeff_subst_zero (by simp) _]
--   rw [addInv_X, PowerSeries.constantCoeff_coe, constantCoeff_mk, FormalGroup.addInv_aux]



-- /- Let `addInv_X` be the right inverse of `X` w.r.t. formal group `F`,
--   `addInv_X_left` be the left inverse of `X` w.r.t. formal group `F`, then
--   this two power series is the same.-/
-- lemma left_addInv_eq_right_addInv : addInv_X_left F = addInv_X F := by
--   calc
--     _ = addInv_X_left F +[F] 0 := (add_zero _ rfl).symm
--     _ = (addInv_X_left F +[F] X) +[F] addInv_X F := by
--       rw [← X_add_addInv_X_eq_zero (F := F), FormalGroup.add_assoc rfl (constantCoeff_X) rfl]
--     _ = _ := by
--       simp_rw [subst_addInv_eq_zero_left]
--       rw [zero_add _ rfl]

-- /-- For any MvPowerSeries `f` with zero constant coefficient, then
--   `f +[F] addInv F f = 0`. -/
-- lemma add_addInv_eq_zero {f : MvPowerSeries σ R} (h : f.constantCoeff = 0) :
--   f +[F] addInv F f = 0 := calc
--   _ = subst f (MvPowerSeries.subst ![ PowerSeries.X, addInv_X F] F.toPowerSeries) := by
--     rw [subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.addInv_aux F)
--       (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s ↦ h)]
--     congr! 1
--     funext s; fin_cases s
--     · simp; rw [← subst, subst_X
--       <| HasSubst.of_constantCoeff_zero h]
--     · simp; rfl
--   _ = _ := by
--     rw [subst_addInv_eq_zero]; ext n
--     simp [coeff_subst <| HasSubst.of_constantCoeff_zero h]

-- /-- For any MvPowerSeries `f` with zero constant coefficient, then
--   `addInv F f +[F] f = 0`. -/
-- lemma addInv_add_eq_zero {f : MvPowerSeries σ R} (h : f.constantCoeff = 0):
--   addInv F f +[F] f = 0 := calc
--   _ = PowerSeries.subst f (MvPowerSeries.subst ![(addInv_X_left F), PowerSeries.X] F.toPowerSeries) := by
--     rw [subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.addInv_aux' F)
--       (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s ↦ h)]
--     congr! 1
--     funext s; fin_cases s
--     · simp [left_addInv_eq_right_addInv]; rfl
--     · simp; rw [← subst, subst_X
--       <| HasSubst.of_constantCoeff_zero h]
--   _ = _ := by
--     rw [subst_addInv_eq_zero_left]; ext n
--     simp [coeff_subst <| HasSubst.of_constantCoeff_zero h]

-- open MvPowerSeries in
-- /-- For any MvPowerSeries `f` with zero constant coefficient, then there exist unique
--   MvPowerSeries `g`, such that `f +[F] g = 0 ∧ constantCoeff g = 0`-/
-- lemma uniqueness_of_addInv {f : MvPowerSeries σ R} (h : constantCoeff f = 0) :
--   ∃! (g : MvPowerSeries σ R), f +[F] g = 0 ∧ constantCoeff g = 0 := by
--   refine existsUnique_of_exists_of_unique ?_ ?_
--   · use addInv F f
--     constructor
--     · exact add_addInv_eq_zero F h
--     · rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [h]) rfl]
--   · intro y z ⟨hy₁, hy₂⟩ ⟨hz₁, hz₂⟩
--     have coeff_aux : MvPowerSeries.constantCoeff (addInv F f) = 0 := by
--       rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [h]) rfl]
--     calc
--       _ = addInv F f := by
--         rw [←zero_add hy₂ (F := F), ←addInv_add_eq_zero F h, FormalGroup.add_assoc
--           coeff_aux h hy₂, hy₁, add_zero _ coeff_aux]
--       _ = _ := by
--         rw [←zero_add hz₂ (F := F), ←addInv_add_eq_zero F h, FormalGroup.add_assoc
--           coeff_aux h hz₂, hz₁, add_zero _ coeff_aux]


-- open MvPowerSeries in
-- /-- For any two MvPowerSeries `f, g` with constant coefficient are zero, then
--   `addInv F (f +[F] g) = addInv F g +[F] addInv F f`. -/
-- lemma addInv_of_add_eq {f g : MvPowerSeries σ R} (hf : constantCoeff f = 0)
--   (hg : constantCoeff g = 0) : addInv F (f +[F] g) = addInv F g +[F] addInv F f := by
--   have coeff_aux₀ : constantCoeff (f +[F] g) = 0 :=
--     constantCoeff_subst_zero (by simp [hf, hg]) F.zero_constantCoeff
--   have coeff_aux₁ : constantCoeff (addInv F (f +[F] g)) = 0 := by
--     rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [coeff_aux₀]) rfl]
--   have coeff_aux_f : constantCoeff (addInv F f) = 0 := by
--     rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [hf]) rfl]
--   have coeff_aux_g : constantCoeff (addInv F g) = 0 := by
--     rw [addInv, PowerSeries.subst, constantCoeff_subst_zero (by simp [hg]) rfl]
--   have coeff_aux₃ : constantCoeff (addInv F (f +[F] g) +[F] f) = 0 := by
--     rw [constantCoeff_subst_zero (by simp [coeff_aux₁, hf]) F.zero_constantCoeff]
--   obtain eq_aux := addInv_add_eq_zero F coeff_aux₀
--   have eq_aux₁ : addInv F (f +[F] g) +[F] f = addInv F g := by
--     rw [← add_zero _ coeff_aux₃, ← add_addInv_eq_zero F hg,
--       ← FormalGroup.add_assoc coeff_aux₃ hg coeff_aux_g, FormalGroup.add_assoc coeff_aux₁ hf hg,
--       eq_aux, zero_add _ coeff_aux_g]
--   rw [←add_zero (F := F) coeff_aux₁, ←add_addInv_eq_zero F hf,
--     ←FormalGroup.add_assoc coeff_aux₁ hf coeff_aux_f,
--     eq_aux₁]

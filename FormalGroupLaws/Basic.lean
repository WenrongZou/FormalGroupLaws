/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import FormalGroupLaws.SubstInv
public import Mathlib.Tactic.Ring.NamePowerVars

@[expose] public section

/-!

## Adivisor : María Inés de Frutos-Fernández

## Reference:
· Silverman, The Arithmetic of Elliptic Curves (2nd edition) - Chapter 4.
· Lubin-Tate, Formal Complex Multiplication in Local Fields.
· Hazewinkel, Formal Groups and Applications. Start with Chapters 1 and 2. Later you can look at some parts of Chapters 4 and 6.

## Contents in this file.
This file defines one dimensional formal group law over a ring `R`, homomorphism and isomorphism
between two formal group, coefficient base change of formal group.

In this file, I define one formal group law to be
a two variable power series `F`, with properties:
· the zero coefficient of `F` is zero.
· the coefficient of `X` is one.
· the coefficient of `Y` is one.
· associativity condition : `F(F(X,Y), Z) = F(X, F(Y,Z))`.
In this file, I also prove in this definition of Formal Group Law `F`, it follows that
`F(X,0) = X` and `F(0,Y) = Y`.
-/

-- Definition of Formal Group
-- Assume the coeffiecient ring `R` to be commutative ring.
variable {R : Type*} [CommRing R] {σ τ : Type*} (F : MvPowerSeries (Fin 2) R) (α : PowerSeries R)
  {S : Type*} [CommRing S] [Algebra R S]

noncomputable section

name_power_vars X₀, X₁ over R

name_power_vars Y₀, Y₁, Y₂ over R


open MvPowerSeries Finsupp

/-- Given a MvPowerSeries `f'` and two map `g h : σ → MvPowerSeries τ R`, if `g = h`,
  then `subst g f' = subst h f'`-/
lemma MvPowerSeries.subst_congr {τ : Type*} {f' : MvPowerSeries σ R} {g h : σ → MvPowerSeries τ R} (H : g = h) :
    subst g f' = subst h f' := H ▸ rfl

lemma MvPowerSeries.HasSubst.X_zero {i : σ} : HasSubst ![X i (R := R), 0] :=
  hasSubst_of_constantCoeff_zero (by simp)

lemma MvPowerSeries.HasSubst.zero_X {i : σ} : HasSubst ![0, X i (R := R)] :=
  hasSubst_of_constantCoeff_zero (by simp)

lemma MvPowerSeries.IsNilpotent_subst' {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    {f : MvPowerSeries σ R} (hf : IsNilpotent f.constantCoeff) :
    IsNilpotent (constantCoeff (f.subst a)) := by
  classical
  rw [constantCoeff_subst ha]
  refine isNilpotent_finsum fun d => ?_
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    apply IsNilpotent.smul
    simpa using IsNilpotent.map hf (algebraMap R S)
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr hd
  rw [Finsupp.prod, map_prod, ← Finset.prod_erase_mul _ _ hi, ← algebraMap_smul S,
    smul_eq_mul, ← mul_assoc, map_pow]
  exact Commute.isNilpotent_mul_left (Commute.all _ _)
    <| (IsNilpotent.pow_iff_pos (d.mem_support_iff.mp hi)).mpr (ha.const_coeff i)

@[simp]
lemma PowerSeries.coeff_coeToMvPowerSeries {f : PowerSeries R} (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single () n) f = f.coeff n := rfl

lemma PowerSeries.X_apply : PowerSeries.X (R := R) = MvPowerSeries.X () := by rfl

attribute [simp, grind =] PowerSeries.coeff_X_pow

lemma MvPowerSeries.subst_zero_of_constantCoeff_zero {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    f.subst (0 : σ → MvPowerSeries τ S) = 0 := by
  ext n
  rw [coeff_subst (by simp [hasSubst_def]), coeff_zero, finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd, hf]
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr hd
  simp [Finsupp.prod, Finset.prod_eq_zero hi, coeff_zero, zero_pow <| d.mem_support_iff.mp hi]

theorem PowerSeries.subst_zero_of_constantCoeff_zero {f : PowerSeries R} (hf : f.constantCoeff = 0) :
    subst (0 : MvPowerSeries τ S) f = 0 :=
  MvPowerSeries.subst_zero_of_constantCoeff_zero hf

/-- Given a PowerSeries `f'` and two MvPowerSeries `f₁, f₂`, if `f₁ = f₂`,
  then `PowerSeries.subst f₁ f' = PowerSeries.subst f₂ f'`. -/
lemma PowerSeries.subst_congr {f' : PowerSeries R} {f₁ f₂ : MvPowerSeries σ R}
    (H : f₁ = f₂): PowerSeries.subst f₁ f' = PowerSeries.subst f₂ f' :=  H ▸ rfl

@[simp]
lemma PowerSeries.coeff_coe {f : PowerSeries R} (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single () n) f = f.coeff n := rfl

@[simp]
lemma PowerSeries.constantCoeff_coe {f : PowerSeries R} : MvPowerSeries.constantCoeff f =
  PowerSeries.constantCoeff f := rfl

lemma RingHom.eq_toAddMonoidHom {S T : Type*} [Semiring S] [Semiring T] (f : S →+* T) {x : S} :
  f x = f.toAddMonoidHom x := rfl

lemma HasSubst.FinPairing {f g : MvPowerSeries σ R} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : HasSubst ![f, g] :=
  hasSubst_of_constantCoeff_zero (by simp [hf, hg])

lemma MvPowerSeries.HasSubst.X_two {i j : σ} : HasSubst ![X i, X j (R := R)] :=
  hasSubst_of_constantCoeff_zero (by simp)

lemma has_subst_XY : HasSubst (![Y₀, Y₁]) (S := R) := HasSubst.X_two

lemma has_subst_YZ : HasSubst (![Y₁, Y₂]) (S := R) := HasSubst.X_two

lemma constantCoeff_subst_zero {f : σ → MvPowerSeries τ S} {g : MvPowerSeries σ R}
  [Fintype σ] (hf : ∀ x : σ, constantCoeff (f x) = 0) (hg : constantCoeff g = 0):
  constantCoeff (subst f g) = 0 := by
  rw [constantCoeff_subst <| hasSubst_of_constantCoeff_zero hf]
  apply finsum_eq_zero_of_forall_eq_zero <| fun x => by
    by_cases hx : x = 0
    · simp [hx, hg]
    · simp only [prod_pow, map_prod, map_pow]
      have zero_aux : ∏ x_1, constantCoeff (f x_1) ^ x x_1 = 0 := by
        have exist_aux : ∃ i : σ, x i ≠ 0 := by
          by_contra hc
          simp at hc
          exact hx <| Finsupp.ext hc
        obtain ⟨i, hi⟩ := exist_aux
        apply Finset.prod_eq_zero (i := i) (by simp)
        simp [hf, zero_pow hi]
      simp [zero_aux]

variable {F} in
lemma has_subst_aux₁ (hF : constantCoeff F = 0) : HasSubst (![subst ![Y₀, Y₁] F, Y₂])
  (S := R):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s; fin_cases s
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact constantCoeff_subst_zero (by simp) hF
  · simp

variable {F} in
lemma has_subst_aux₂ (hF : constantCoeff F = 0) : HasSubst ![Y₀, subst ![Y₁, Y₂] F]
  (S := R):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s
  · simp
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
    exact constantCoeff_subst_zero (by simp) hF

lemma has_subst_swap : HasSubst ![X₁, X₀]  :=
  hasSubst_of_constantCoeff_zero (by simp [constantCoeff_X])

/--
Given a power series p(X) ∈ R⟦X⟧ and an index i, we may view it as a
multivariate power series p(X_i) ∈ R⟦X_1, ..., X_n⟧.
-/
def PowerSeries.toMvPowerSeries (i : σ) : PowerSeries R →ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.X i)

theorem PowerSeries.toMvPowerSeries_apply (i : σ) (f : PowerSeries R) :
    f.toMvPowerSeries i = f.subst (MvPowerSeries.X i) := by
  rw [toMvPowerSeries, coe_substAlgHom]

theorem PowerSeries.HasSubst.toMvPowerSeries [Finite σ]
    {f : PowerSeries R} (hf : f.constantCoeff = 0) :
    MvPowerSeries.HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by
    rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.constantCoeff_X _) _ hf]

lemma PowerSeries.toMvPowerSeries_val {f : PowerSeries R} {a : σ → MvPowerSeries τ R} (i : σ)
    (ha : MvPowerSeries.HasSubst a) : (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  simp_rw [toMvPowerSeries_apply, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X i)) ha, MvPowerSeries.subst_X ha]

/-- This is a map from `Fin 2` to `ℕ` mapping `0` to `i` and `1` to `j`, which can be used
  to compute degree of `X^i*X^j`.  -/
abbrev coeff_two (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

/-- This is a map from `Fin 3` to `ℕ` mapping `0` to `i` and `1` to `j`, `2` to `k` which can be used
  to compute degree of `X^i*Y^j*Z^k`.  -/
abbrev coeff_three (i j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k

variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`. -/
@[ext]
structure FormalGroup where
  /-- The underlying power series $F(X, Y)$ in two variables. -/
  toPowerSeries : MvPowerSeries (Fin 2) R
  /-- The constant coefficient of the formal group law is zero. -/
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  /-- The coefficient of $X$ in $F(X, Y)$ is 1. -/
  lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
  /-- The coefficient of $Y$ in $F(X, Y)$ is 1. -/
  lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
  /-- Associativity condition: $F(F(X, Y), Z) = F(X, F(Y, Z))$. -/
  assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂]
    = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)

/-- The natural inclusion from formal group law into formal power series. -/
instance FormalGroup.coeToPowerSeries : Coe (FormalGroup R) (MvPowerSeries (Fin 2) R) :=
  ⟨toPowerSeries⟩

/-- Given a formal group `F`, `F.IsComm` is a proposition that $F(X,Y) = F(Y,X)$. -/
class FormalGroup.IsComm (F : FormalGroup R) : Prop where
  comm : F = (F : MvPowerSeries (Fin 2) R).subst ![X₁, X₀]

lemma FormalGroup.assoc' (F : FormalGroup R) {f₀ f₁ f₂ : MvPowerSeries σ R}
    (h₀ : PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) (h₂ : PowerSeries.HasSubst f₂) :
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![f₀, f₁], f₂] =
      F.toPowerSeries.subst ![f₀, F.toPowerSeries.subst ![f₁, f₂]] := by
  obtain aux₁ := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  obtain aux₂ := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  have : HasSubst ![f₀, f₁, f₂] :=
    hasSubst_of_constantCoeff_nilpotent fun s => by fin_cases s <;> simpa
  calc
    _ = (F.toPowerSeries.subst ![F.toPowerSeries.subst ![Y₀, Y₁], Y₂]).subst ![f₀, f₁, f₂] := by
      rw [subst_comp_subst_apply aux₁ this]
      congr! 2 with s
      fin_cases s
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero, subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst_X this]
      · simp [subst_X this]
    _ = _ := by
      rw [F.assoc, subst_comp_subst_apply aux₂ this]
      congr! 2 with s
      fin_cases s
      · simp [subst_X this]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst]

lemma FormalGroup.comm' (F : FormalGroup R) [F.IsComm] {f g : MvPowerSeries σ R}
    (hf : PowerSeries.HasSubst f) (hg : PowerSeries.HasSubst g) :
    F.toPowerSeries.subst ![f, g] = F.toPowerSeries.subst ![g, f] := by
  nth_rw 1 [IsComm.comm]
  rw [subst_comp_subst_apply HasSubst.X_X <| hasSubst_of_constantCoeff_nilpotent (by simp [hf, hg])]
  congr! 2 with s
  fin_cases s <;> simp [subst]

namespace FormalGroup

variable {σ : Type*} (F : FormalGroup R)

set_option linter.unusedVariables false in
/-- `Point F σ` represents the mathematical space of points of a formal group $F$
taking values in the formal power series ring `MvPowerSeries σ R` with the property
that constant coefficient is nilpotent.

TODO: Mathematically, a 1-dimensional formal group law $F$ over a ring $R$ defines a group
structure on the elements of a complete local $R$-algebra (specifically, its maximal ideal)
via the substitution operation $x +_F y = F(x, y)$. -/
@[nolint unusedArguments]
def Point (F : FormalGroup R) (σ : Type*) := {f : MvPowerSeries σ R // PowerSeries.HasSubst f}

instance : Add (F.Point σ) where
  add x y := ⟨(F : MvPowerSeries (Fin 2) R).subst ![x.val, y.val],
    IsNilpotent_subst' (by simp [hasSubst_of_constantCoeff_nilpotent, x.prop, y.prop])
      (F.zero_constantCoeff ▸ IsNilpotent.zero)⟩

@[simp]
lemma add_apply {x y : F.Point σ} : (x + y).val = F.toPowerSeries.subst ![x.val, y.val] := by
  rfl

instance : Zero (F.Point σ) where
  zero := ⟨0, PowerSeries.HasSubst.zero⟩

@[simp]
lemma zero_apply : (0 : F.Point σ).val = (0 : MvPowerSeries σ R) := rfl

/- TODO : Zero, SMul, Inv instance. -/

/-- Additive formal group law `𝔾ₐ(X,Y) = X + Y`. -/
@[simps]
def 𝔾ₐ : FormalGroup R where
  toPowerSeries := X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_X aux₁, subst_add aux₂, subst_X aux₂]
    simp [subst_add .X_X, subst_X .X_X, add_assoc]

instance : (𝔾ₐ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_X .X_X, add_comm]

/-- Multiplicative formal group law `𝔾ₘ(X,Y) = X + Y + XY`. -/
@[simps]
def 𝔾ₘ : FormalGroup R where
  toPowerSeries := X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_mul aux₁, subst_X aux₁, subst_add aux₂, subst_mul aux₂,
      subst_X aux₂]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, subst_add .X_X, Fin.isValue, subst_X .X_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, subst_mul .X_X]
    ring

instance : (𝔾ₘ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_mul .X_X, subst_X .X_X, add_comm, mul_comm]

/-- Given an algebra map `f : R →+* S` and a formal group law `F` over `R`, then `f_* F` is a
formal group law formal group law over `S`. This is constructed by applying `f` to all coefficients
of the underlying power series. -/
@[simps]
def map (f : R →+* S) : FormalGroup S where
  toPowerSeries := (F : MvPowerSeries (Fin 2) R).map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => (![g₁, g₂] i).map f := by ext1 i; fin_cases i <;> simp
    simp_rw [(map_X f _).symm, this, ← map_subst .X_X, this, ← map_subst
      (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff), F.assoc,
      ← map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff)]

end FormalGroup

section

namespace FormalGroup

variable (F : FormalGroup R)

/-- An abbreviation of $F(X,0)$ for a formal group $F$. -/
abbrev Xzero : PowerSeries R := subst ![PowerSeries.X, 0] F.toPowerSeries

lemma constantCoeff_Xzero : F.Xzero.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, Xzero, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.X_zero _ F.zero_constantCoeff]

@[simp]
lemma coeff_one_Xzero : F.Xzero.coeff 1 = 1 := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 0 1)]
  · simp [F.lin_coeff_X]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · by_cases hd₀ : d 0 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.X_zero

@[simp]
lemma Xzero_subst_Xzero : F.Xzero.subst F.Xzero = F.Xzero := by
  calc
    _ = F.toPowerSeries.subst ![F.toPowerSeries.subst ![PowerSeries.X, 0], 0] := by
      have : PowerSeries.HasSubst (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff, PowerSeries.X, constantCoeff_subst_eq_zero HasSubst.X_zero
          _ F.zero_constantCoeff]
        simp [← PowerSeries.X_apply]
      rw [PowerSeries.subst, subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
      · exact HasSubst.X_zero
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 → PowerSeries R) := by
        ext x : 1; fin_cases x <;> rfl
      simp [F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst]

lemma Xzero_eq_X : F.Xzero = PowerSeries.X := by
  haveI : Invertible (F.Xzero.coeff 1) := (coeff_one_Xzero F) ▸ invertibleOne
  calc
    _ = F.Xzero.substInv.subst (F.Xzero.subst F.Xzero) := by
      have aux₀ : PowerSeries.HasSubst F.Xzero :=
        PowerSeries.HasSubst.of_constantCoeff_zero' <| constantCoeff_Xzero F
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀, PowerSeries.subst_substInv_left _
        F.constantCoeff_Xzero , PowerSeries.subst_X aux₀, Xzero]
    _ = _ := by
      rw [Xzero_subst_Xzero, F.Xzero.subst_substInv_left F.constantCoeff_Xzero]

/-- An abbreviation of $F(0,X)$ for a formal group $F$. -/
abbrev zeroX : PowerSeries R := subst ![0, PowerSeries.X] F.toPowerSeries

lemma constantCoeff_zeroX : F.zeroX.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, zeroX, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.zero_X _ F.zero_constantCoeff]

@[simp]
lemma coeff_one_zeroX : F.zeroX.coeff 1 = 1 := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 1 1)]
  · simp [F.lin_coeff_Y]
  · intro d hd
    by_cases hd₁ : d 0 = 0
    · by_cases hd₀ : d 1 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.zero_X

@[simp]
lemma zeroX_subst_zeroX : F.zeroX.subst F.zeroX = F.zeroX := by
  calc
    _ = F.toPowerSeries.subst ![0, F.toPowerSeries.subst ![0, PowerSeries.X]] := by
      have : PowerSeries.HasSubst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff, PowerSeries.X, constantCoeff_subst_eq_zero HasSubst.zero_X
          (by simp [← PowerSeries.X_apply]) F.zero_constantCoeff]
      rw [PowerSeries.subst, subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
      · exact HasSubst.zero_X
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 → PowerSeries R) := by ext x : 1; fin_cases x <;> rfl
      simp [← F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst]

lemma zeroX_eq_X : F.zeroX = PowerSeries.X := by
  haveI : Invertible (F.zeroX.coeff 1) := (coeff_one_zeroX F) ▸ invertibleOne
  calc
    _ = F.zeroX.substInv.subst (F.zeroX.subst F.zeroX) := by
      have aux₀ : PowerSeries.HasSubst F.zeroX :=
        PowerSeries.HasSubst.of_constantCoeff_zero' <| F.constantCoeff_zeroX
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀, PowerSeries.subst_substInv_left _
        F.constantCoeff_zeroX, PowerSeries.subst_X aux₀, zeroX]
    _ = _ := by
      rw [zeroX_subst_zeroX, F.zeroX.subst_substInv_left F.constantCoeff_zeroX]

theorem add_zero {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![f, 0] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![PowerSeries.X (R := R), 0]) := by
      rw [PowerSeries.subst, subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [PowerSeries.X, subst]
        · simp [subst, eval₂]
      exact HasSubst.X_zero
    _ = _ := by
      simp [Xzero_eq_X, PowerSeries.subst_X hf]

theorem zero_add {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![0, f] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![0, PowerSeries.X (R := R)]) := by
      rw [PowerSeries.subst, subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [subst, eval₂]
        · simp [PowerSeries.X, subst]
      · exact HasSubst.zero_X
    _ = _ := by
      simp [zeroX_eq_X, PowerSeries.subst_X hf]

instance : AddMonoid (F.Point σ) where
  zero_add x := Subtype.ext (zero_add F x.prop)
  add_zero x := Subtype.ext (add_zero F x.prop)
  nsmul := nsmulRec
  add_assoc x y z := Subtype.ext <| F.assoc' x.prop y.prop z.prop

instance [F.IsComm] : AddCommMonoid (F.Point σ) where
  add_comm x y := Subtype.ext <| F.comm' x.prop y.prop


lemma coeff_pow_X₀ {n : ℕ}(hn : n ≠ 1) : coeff (Finsupp.single 0 n) F.toPowerSeries = 0 := by
  calc
    _ = PowerSeries.coeff n (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
      rw [PowerSeries.coeff, coeff_subst _, finsum_eq_single _ (single 0 n)]
      simp
      intro d hd
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, prod_pow, Fin.prod_univ_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, PowerSeries.coeff_coe,
        smul_eq_mul]
      by_cases hd₀ : d = 0
      · simp [hd₀, F.zero_constantCoeff]
      · by_cases hd₀ : d 1 = 0
        · simp only [Fin.isValue, hd₀, pow_zero, mul_one]
          rw [PowerSeries.coeff_X_pow, if_neg, mul_zero]
          by_contra! hc
          have deq : d = single 0 n := by
            ext i ; fin_cases i <;> simp [hd₀, hc]
          contradiction
        simp [zero_pow hd₀]
      · exact HasSubst.X_zero
    _ = 0 := by
      rw [add_zero _ PowerSeries.HasSubst.X', PowerSeries.coeff_X, if_neg hn]

lemma coeff_pow_X₁ {n : ℕ} (hn : n ≠ 1) : coeff (Finsupp.single 1 n) F.toPowerSeries = 0 := by
  calc
    _ = PowerSeries.coeff n (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
      rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 1 n)]
      simp
      intro d hd
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, prod_pow, Fin.prod_univ_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, PowerSeries.coeff_coe,
        smul_eq_mul]
      by_cases hd₀ : d = 0
      · simp [hd₀, F.zero_constantCoeff]
      · by_cases hd₀ : d 0 = 0
        · simp only [Fin.isValue, hd₀, pow_zero, one_mul]
          rw [PowerSeries.coeff_X_pow, if_neg, mul_zero]
          by_contra! hc
          have deq : d = single 1 n := by
            ext i ; fin_cases i <;> simp [hd₀, hc]
          contradiction
        simp [zero_pow hd₀]
      exact HasSubst.zero_X
    _ = 0 := by
      rw [zero_add _ PowerSeries.HasSubst.X', PowerSeries.coeff_X, if_neg hn]

/- given a formal group law `F (X, Y)`, then there is a multivariate power series`G (X, Y)` with
two variables, such that F = X + Y * G (X, Y). -/
theorem decomp_X_add : ∃ G, F.toPowerSeries = X₀ + X₁ * G := by
  have dvd_aux : X₁ ∣ F.toPowerSeries - X₀ := by
    refine X_dvd_iff.mpr ?_
    intro m hm
    have meq : m = single 0 (m 0) := by
      ext i; fin_cases i <;> simp [hm]
    rw [meq, map_sub]
    by_cases hm₁ : m 0 = 1
    · rw [hm₁, F.lin_coeff_X, coeff_X, if_pos rfl, sub_self]
    · rw [coeff_pow_X₀, coeff_X, if_neg, sub_zero]
      refine ne_iff.mpr ?_
      use 0
      · simpa
      · simpa
  obtain ⟨G, hG⟩ := dvd_aux
  use G
  rw [← hG]
  ring

/- given a formal group law `F (X, Y)`, then there is a multivariate power series`G (X, Y)` with
two variables, such that F = Y + X * G (X, Y). -/
theorem decomp_Y_add : ∃ G, F.toPowerSeries = X₁ + X₀ * G := by
  have dvd_aux : X₀ ∣ F.toPowerSeries - X₁ := by
    refine X_dvd_iff.mpr ?_
    intro m hm
    have meq : m = single 1 (m 1) := by
      ext i; fin_cases i <;> simp [hm]
    rw [meq, map_sub]
    by_cases hm₁ : m 1 = 1
    · rw [hm₁, F.lin_coeff_Y, coeff_X, if_pos rfl, sub_self]
    · rw [coeff_pow_X₁, coeff_X, if_neg, sub_zero]
      refine ne_iff.mpr ?_
      use 1
      · simpa
      · simpa
  obtain ⟨G, hG⟩ := dvd_aux
  use G
  rw [← hG]
  ring_nf

section FormalGroupHom

variable {F G : FormalGroup R}

variable (F G) in
/-- Let $F G$ be two formal group laws over commutative ring $R$. A homomorphism (over $R$)
$F (X, Y) → G (X, Y)$ is a power series $α(X) = b_1 X + b_2 X ^ 2 + ⋯$ with coefficients
in $R$ without constant term such that $α(F (X, Y)) = G (α (X), α (Y))$. -/
@[ext]
structure FormalGroupHom where
  /-- The underlying power series of a formal group homomorphism. -/
  toPowerSeries : PowerSeries R
  /-- Constant coefficient of underlying power series is zero. -/
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  /-- The homomorphism condition: $f(F(X,Y))=G(f(X),f(Y))$. -/
  hom : toPowerSeries.subst F = G.toPowerSeries.subst (toPowerSeries.toMvPowerSeries ·)

section FormalGroupIso

variable (F G) in
/-- The homomorphism $α(X) : F (X, Y) → G (X, Y)$ is an isomorphism if there exists a
homomorphism $β(X) : G (X, Y) → F (X, Y)$ such that $α ∘ β = id$ and $β ∘ α = id$. -/
@[ext]
structure FormalGroupIso where
  /-- The underlying formal group homomorphism of a formal group isomorphism. -/
  toHom : FormalGroupHom F G
  /-- The inverse homomorphism of underlying formal group homomorphism. -/
  invHom : FormalGroupHom G F
  /-- `toHom ∘ invHom = id`. -/
  left_inv : toHom.toPowerSeries.subst ∘ (PowerSeries.subst invHom.toPowerSeries) = id
  /-- `invHom ∘ toHom = id`. -/
  right_inv : invHom.toPowerSeries.subst ∘ (PowerSeries.subst toHom.toPowerSeries) = id

@[simp]
lemma FormalGroupIso.toHom_subst_invHom {α : FormalGroupIso F G} :
    α.toHom.toPowerSeries.subst α.invHom.toPowerSeries = PowerSeries.X := by
  symm
  calc
    _ = id PowerSeries.X := by rw [id]
    _ = _ := by
      rw [← α.left_inv, Function.comp_apply, PowerSeries.subst_X
        <| PowerSeries.HasSubst.of_constantCoeff_zero' α.invHom.zero_constantCoeff]

@[simp]
lemma FormalGroupIso.invHom_subst_toHom {α : FormalGroupIso F G} :
    α.invHom.toPowerSeries.subst α.toHom.toPowerSeries = PowerSeries.X := by
  symm
  calc
    _ = id PowerSeries.X := by rw [id]
    _ = _ := by
      rw [← α.right_inv, Function.comp_apply, PowerSeries.subst_X
        <| PowerSeries.HasSubst.of_constantCoeff_zero' α.toHom.zero_constantCoeff]

/-- An isomorphism $α(X) : F (X, Y) → G (X, Y)$, $α(X) = a_1 X + a_2 X ^ 2 + ⋯$
is called strict isomorphism if $a_1 = 1$. -/
class FormalGroupIso.IsStrict (α : FormalGroupIso F G) : Prop where
  coeff_one : α.toHom.toPowerSeries.coeff 1 = 1

open PowerSeries HasSubst in
theorem FormalGroupIso.ext_iff' {α β : FormalGroupIso F G} :
    α = β ↔ α.toHom = β.toHom := by
  rw [FormalGroupIso.ext_iff, and_iff_left_iff_imp]
  intro h
  rw [FormalGroupHom.ext_iff, ← (X_subst α.invHom.toPowerSeries), ← β.toHom_subst_invHom,
    ← subst_comp_subst_apply (.of_constantCoeff_zero' (β.toHom.zero_constantCoeff))
      (.of_constantCoeff_zero' (β.invHom.zero_constantCoeff)), ← h, α.invHom_subst_toHom,
      subst_X (.of_constantCoeff_zero' (β.invHom.zero_constantCoeff))]

end FormalGroupIso

open MvPowerSeries

/-- Given a formal group homomorphism $f : F → G$ and `x : F.Point σ`, then we have a
`f x : G.Point σ`. -/
def FormalGroupHom.applyPoint (f : FormalGroupHom F G) (x : F.Point σ) : G.Point σ :=
  ⟨f.toPowerSeries.subst x.val, IsNilpotent_subst'
    x.prop.const (f.zero_constantCoeff ▸ IsNilpotent.zero)⟩

@[simp]
lemma FormalGroupHom.applyPoint_val (f : FormalGroupHom F G) (x : F.Point σ) :
    (f.applyPoint x).val =  f.toPowerSeries.subst x.val := rfl

/-- Corecion of a formal group homomorphism $f : F → G$ to a function from `F.Point σ` to
`G.Point σ`. This instance enable us to use the notation `f x` for a `x : F.Point σ`. -/
instance : CoeFun (FormalGroupHom F G) (fun _ ↦ {σ : Type*} → F.Point σ → G.Point σ) where
  coe f := f.applyPoint

lemma FormalGroupHom.map_add (f : FormalGroupHom F G) {x y : F.Point σ} :
    f (x + y) = f x + f y := by
  apply Subtype.ext
  have : HasSubst ![x.val, y.val] := by simp [hasSubst_of_constantCoeff_nilpotent, x.prop, y.prop]
  calc
    _ = (f.toPowerSeries.subst F.toPowerSeries).subst ![x.val, y.val] := by
      simp [PowerSeries.subst, PowerSeries.subst, subst_comp_subst_apply, PowerSeries.HasSubst,
        F.zero_constantCoeff, x.prop, y.prop, hasSubst_of_constantCoeff_nilpotent]
    _ = _ := by
      rw [f.hom, subst_comp_subst_apply
        (PowerSeries.HasSubst.toMvPowerSeries f.zero_constantCoeff) this]
      congr
      ext s : 1
      fin_cases s <;> simp [PowerSeries.toMvPowerSeries_val _ this]

/-- A formal group homomorphism $f : F → G$ is a add monoid homomorphism from `F.Point σ` to
`G.Point σ`. -/
def FormalGroupHom.toAddMonoidHom (f : FormalGroupHom F G) : F.Point σ →+ G.Point σ where
  toFun := f.applyPoint
  map_zero' := Subtype.ext <| PowerSeries.subst_zero_of_constantCoeff_zero f.zero_constantCoeff
  map_add' _ _ := f.map_add

lemma FormalGroupHom.toAddMonoidHom_apply (f : FormalGroupHom F G) {x : F.Point σ} :
    f.toAddMonoidHom x = f.applyPoint x := rfl

end FormalGroupHom

-- theorem FormalGroupStrictIso.ext_iff' (G₁ G₂ : FormalGroup R) (α β : FormalGroupStrictIso G₁ G₂) :
--     α = β ↔ α.toHom = β.toHom := by
--   rw [FormalGroupStrictIso.ext_iff]
--   refine ⟨fun h => h.1, fun h => ⟨h, FormalGroupHom.ext ?_⟩⟩
--   obtain ⟨g, h₁, h₂⟩ := PowerSeries.exist_unique_subst_inv_left _ (by simp [β.one_coeff_one])
--     β.toHom.zero_constantCoeff
--   simp only [and_imp] at h₂
--   rw [h₂ _ (h ▸ α.left_inv) α.invHom.zero_constantCoeff,
--     h₂ _ β.left_inv β.invHom.zero_constantCoeff]

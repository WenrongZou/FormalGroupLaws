/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import FormalGroupLaws.SubstInv

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

open MvPowerSeries Finsupp

abbrev X₀ : MvPowerSeries (Fin 2) R := X (0 : Fin 2)

abbrev X₁ : MvPowerSeries (Fin 2) R := X (1 : Fin 2)

abbrev Y₀ : MvPowerSeries (Fin 3) R := X (0 : Fin 3)

abbrev Y₁ : MvPowerSeries (Fin 3) R := X (1 : Fin 3)

abbrev Y₂ : MvPowerSeries (Fin 3) R := X (2 : Fin 3)

/-- Given a MvPowerSeries `f'` and two map `g h : σ → MvPowerSeries τ R`, if `g = h`,
  then `subst g f' = subst h f'`-/
lemma MvPowerSeries.subst_congr {τ : Type*} {f' : MvPowerSeries σ R} {g h : σ → MvPowerSeries τ R} (H : g = h) :
    subst g f' = subst h f' := H ▸ rfl

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

lemma has_subst_swap : HasSubst ![X₁, X₀ (R := R)]  :=
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

theorem HasSubst.toMvPowerSeries [Finite σ] {f : PowerSeries R} (hf : f.constantCoeff = 0) :
    HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by
    rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero
      (constantCoeff_X _) _ hf]

lemma PowerSeries.toMvPowerSeries_val {f : PowerSeries R} {a : σ → MvPowerSeries τ R} (i : σ)
    (ha : MvPowerSeries.HasSubst a) : (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  simp_rw [toMvPowerSeries_apply, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X i)) ha, MvPowerSeries.subst_X ha]

-- def PowerSeries.toMvPowerSeries (f : PowerSeries R) (i : σ) : MvPowerSeries σ R :=
--   f.subst (MvPowerSeries.X i)

-- lemma HasSubst.toMvPowerSeries [Finite σ] {f : PowerSeries R} (hf : f.constantCoeff = 0) :
--     HasSubst (fun (i : σ) => f.toMvPowerSeries i) (S := R) := by
--   refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
--   intro x
--   rw [PowerSeries.toMvPowerSeries, PowerSeries.constantCoeff_subst_eq_zero
--     (constantCoeff_X _) _ hf]

-- lemma PowerSeries.toMvPowerSeries_val {f : PowerSeries R} {a : σ → MvPowerSeries τ R} (i : σ)
--     (ha : MvPowerSeries.HasSubst a) : (f.toMvPowerSeries i).subst a = f.subst (a i) := by
--   simp_rw [PowerSeries.toMvPowerSeries, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply
--     (HasSubst.const (HasSubst.X i)) ha, MvPowerSeries.subst_X ha]

/-- This is a map from `Fin 2` to `ℕ` mapping `0` to `i` and `1` to `j`, which can be used
  to compute degree of `X^i*X^j`.  -/
abbrev coeff_two (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

/-- This is a map from `Fin 3` to `ℕ` mapping `0` to `i` and `1` to `j`, `2` to `k` which can be used
  to compute degree of `X^i*Y^j*Z^k`.  -/
abbrev coeff_three (i j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k

variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`-/
@[ext]
structure FormalGroup where
  toPowerSeries : MvPowerSeries (Fin 2) R
  zero_constantCoeff : constantCoeff toPowerSeries = 0
  lin_coeff_X : coeff (Finsupp.single 0 1) toPowerSeries = 1
  lin_coeff_Y : coeff (Finsupp.single 1 1) toPowerSeries = 1
  /- Associativity of the Formal Group : `F (F (X, Y), Z) = F (X, F (Y, Z))`. -/
  assoc : subst ![subst ![Y₀, Y₁] toPowerSeries, Y₂] toPowerSeries = subst ![Y₀, subst ![Y₁, Y₂] toPowerSeries] toPowerSeries (S := R)

variable (R) in
@[ext]
structure CommFormalGroup extends FormalGroup R where
  /- Commutativity F (X, Y) = F (Y, X)-/
  comm : toPowerSeries = MvPowerSeries.subst ![X₁, X₀] toPowerSeries

namespace FormalGroup

/-- Given a formal group `F`, `F.comm` is a proposition that `F(X,Y) = F(Y,X)`-/
def comm (F : FormalGroup R) : Prop :=
  F.toPowerSeries = MvPowerSeries.subst ![X₁, X₀] F.toPowerSeries

class IsComm (F : FormalGroup R) : Prop where
  comm : F.toPowerSeries = F.toPowerSeries.subst ![X₁, X₀]

/-- A commutative formal group law is a formal group law. -/
instance : Coe (CommFormalGroup R) (FormalGroup R) where
  coe := CommFormalGroup.toFormalGroup

/-- addition of two multi variate power series under the formal group `F` sense, namely
`f₀ + [F] f₁ := F (f₀, f₁)` -/
abbrev add (F : FormalGroup R) (f₀ f₁ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  subst ![f₀, f₁] F.toPowerSeries

-- instance : Add (MvPowerSeries σ R) := sorry

/-- `f₀ +[F] f₁` means `F (f₀, f₁)`. -/
scoped[FormalGroup] notation:65 f₀:65 " +[" F:0 "] " f₁:66 => add F f₀ f₁

lemma PowerSeries.constantCoeff_subst_zero {f : MvPowerSeries τ S} {g : PowerSeries R}
    (hf : f.constantCoeff = 0) (hg : g.constantCoeff = 0) :
    constantCoeff (g.subst f) = 0 := by
  rw [PowerSeries.constantCoeff_subst <| PowerSeries.HasSubst.of_constantCoeff_zero hf,
    finsum_eq_zero_of_forall_eq_zero]
  intro d
  if hd : d = 0 then simp [hd, hg]
  else simp [hf, zero_pow hd]

/-- The addition under the sense of formal group `F` is associative. -/
theorem add_assoc {F : FormalGroup R} {Z₀ Z₁ Z₂ : MvPowerSeries σ R}
  (hZ₀ : constantCoeff Z₀ = 0) (hZ₁ : constantCoeff Z₁ = 0) (hZ₂ : constantCoeff Z₂ = 0):
  Z₀ +[F] Z₁ +[F] Z₂ = Z₀ +[F] (Z₁ +[F] Z₂) := by
  have has_subst_aux : HasSubst ![Z₀, Z₁, Z₂] := hasSubst_of_constantCoeff_zero <|
    fun s => by fin_cases s <;> simp [hZ₀, hZ₁, hZ₂]
  have has_subst_aux₂ : HasSubst ![Y₀, subst ![Y₁, Y₂] F.toPowerSeries] :=
    hasSubst_of_constantCoeff_zero <| fun s => by
    fin_cases s
    · simp; rw [constantCoeff_X (R := R)]
    · simp
      rw [constantCoeff_subst_zero (by simp) F.zero_constantCoeff]
  have has_subst_aux₃ : HasSubst ![subst ![Y₀, Y₁] F.toPowerSeries, Y₂] :=
    hasSubst_of_constantCoeff_zero (S := R) <| fun s => by
    fin_cases s
    · simp
      rw [constantCoeff_subst_zero (by simp) F.zero_constantCoeff]
    · simp
  calc
    _ = subst ![Z₀, Z₁, Z₂] (R := R) (subst ![subst ![Y₀, Y₁] F.toPowerSeries, Y₂] F.toPowerSeries) := by
      simp [add]
      rw [subst_comp_subst_apply has_subst_aux₃ has_subst_aux]
      apply subst_congr
      funext s; fin_cases s
      · simp
        rw [subst_comp_subst_apply has_subst_XY has_subst_aux]
        apply subst_congr
        funext s; fin_cases s <;> simp [subst_X has_subst_aux]
      · simp [subst_X has_subst_aux]
    _ = _ := by
      simp [add]
      rw [F.assoc, subst_comp_subst_apply has_subst_aux₂ has_subst_aux]
      apply subst_congr
      funext s; fin_cases s
      · simp [subst_X has_subst_aux]
      · simp [subst_comp_subst_apply has_subst_YZ has_subst_aux]
        apply subst_congr
        funext t; fin_cases t <;> simp [subst_X has_subst_aux]

theorem add_comm {F : FormalGroup R} (hF : F.comm) {Z₀ Z₁ : MvPowerSeries σ R}
  (hZ₀ : constantCoeff Z₀ = 0) (hZ₁ : constantCoeff Z₁ = 0):
  Z₀ +[F] Z₁ = Z₁ +[F] Z₀ := by
  have has_subst_aux : HasSubst ![Z₀, Z₁] := hasSubst_of_constantCoeff_zero <|
    fun s => by fin_cases s <;> simp [hZ₀, hZ₁]
  calc
    _ = subst ![Z₀, Z₁] F.toPowerSeries := rfl
    _ = _ := by
      rw [hF, subst_comp_subst_apply has_subst_swap has_subst_aux]
      apply subst_congr
      funext s; fin_cases s <;> simp [subst_X has_subst_aux]

/-- The addition under the sense of formal group `F` is associative. -/
theorem add_assoc' (F : FormalGroup R) :
  Y₀ +[F] Y₁ +[F] Y₂ = Y₀ +[F] (Y₁ +[F] Y₂) := by
  rw [add, F.assoc]

/-- Additive formal group law `Gₐ(X,Y) = X + Y`-/
def Gₐ : CommFormalGroup R where
  toPowerSeries := X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    rw [subst_add (has_subst_aux₁ (by simp [constantCoeff_X])),
      subst_X (has_subst_aux₁ (by simp [constantCoeff_X])),
      subst_X (has_subst_aux₁ (by simp [constantCoeff_X])), subst_add has_subst_XY,
      subst_add (has_subst_aux₂ (by simp [constantCoeff_X])),
      subst_X (has_subst_aux₂ (by simp [constantCoeff_X])),
      subst_X (has_subst_aux₂ (by simp [constantCoeff_X]))]
    simp_rw [subst_add has_subst_YZ, subst_X has_subst_YZ, subst_X has_subst_XY]
    simp
    ring
  comm := by
    simp [subst_add has_subst_swap, subst_X has_subst_swap]
    ring

/-- Multiplicative formal group law `Gₘ(X,Y) = X + Y + XY`-/
def Gₘ : CommFormalGroup R where
  toPowerSeries := X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  assoc := by
    obtain has_subst₁ := has_subst_aux₁ (F := X₀ + X₁ + X₀ * X₁ (R := R)) (by simp)
    obtain has_subst₂ := has_subst_aux₂ (F := X₀ + X₁ + X₀ * X₁ (R := R)) (by simp)
    simp_rw [subst_add has_subst₁,  subst_mul has_subst₁, subst_X has_subst₁,
      subst_add has_subst₂, subst_mul has_subst₂, subst_X has_subst₂,
      subst_add HasSubst.X_two, subst_mul HasSubst.X_two, subst_X HasSubst.X_two]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  comm := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, subst_add has_subst_swap, subst_X has_subst_swap,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      subst_mul has_subst_swap]
    ring

/-- Given a algebra map `f : R →+* R'` and a formal group law `F` over `R`, then `f_* F` is a
formal group law formal group law over `R'`. This is constructed by applying `f` to all coefficients
of the underlying power series. -/
def map {R' : Type*} [CommRing R'] (f : R →+* R') (F : FormalGroup R) : FormalGroup R' where
  toPowerSeries := F.toPowerSeries.map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => (![g₁, g₂] i).map f := by ext1 i; fin_cases i <;> simp
    simp_rw [(map_X f _).symm, this, ← map_subst has_subst_XY, this, ← map_subst
      (has_subst_aux₁ F.zero_constantCoeff), F.assoc, ← map_subst has_subst_YZ, this,
        ← map_subst (has_subst_aux₂ F.zero_constantCoeff)]

variable (F : FormalGroup R)

lemma has_subst_X₀ : HasSubst ![PowerSeries.X (R := R), 0] :=
  hasSubst_of_constantCoeff_zero (by simp)

lemma has_subst_X₁ : HasSubst ![0, PowerSeries.X (R := R)] :=
  hasSubst_of_constantCoeff_zero (by simp)

/-- The first coefficient of `F(X, 0)` is `1`. -/
lemma coeff_of_X₀_of_subst_X₀ :
  PowerSeries.coeff 1 (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) (R := R) = 1 := by
  simp [PowerSeries.coeff, coeff_subst has_subst_X₀]
  have eq_aux : ∀ (d : Fin 2 →₀ ℕ), d ≠ (Finsupp.single 0 1) → (coeff d) F.toPowerSeries *
    (PowerSeries.coeff 1) (PowerSeries.X ^ d 0 * 0 ^ d 1) = 0 := by
    intro d hd_neq
    by_cases hd : d 1 = 0
    · -- the case `d 1 = 0`
      by_cases hd' : d 0 = 0
      · -- the case `d 0 = 0`
        have d_is_zero : d = 0 := Finsupp.ext <| fun x => by fin_cases x <;> simp [hd, hd']
        simp [d_is_zero, zero_constantCoeff]
      · -- the case `d 0 ≠ 0`
        simp [hd, PowerSeries.coeff_X_pow]
        by_cases hd₀ : d 0 = 1
        · -- the cases `d 0 = 1`
          -- contradiction to the assumption
          have d_eq : d = (Finsupp.single 0 1) := Finsupp.ext <| fun x => by
            fin_cases x <;> simp [hd₀, hd]
          contradiction
        intro hc
        by_contra
        exact hd₀ (Eq.symm hc)
    · -- the case `d 1 ≠ 0`
      simp [zero_pow hd]
  simp [finsum_eq_single _ _ eq_aux, lin_coeff_X,  PowerSeries.coeff_X]

/-- The first coefficient of `F(0, X)` is `1`. -/
lemma coeff_of_X₁_of_subst_X₁ :
  PowerSeries.coeff 1 (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) (R := R) = 1 := by
  simp [PowerSeries.coeff, coeff_subst has_subst_X₁]
  have eq_aux : ∀ (d : Fin 2 →₀ ℕ), d ≠ (Finsupp.single 1 1) → (coeff d) F.toPowerSeries *
    (PowerSeries.coeff 1) ( 0 ^ d 0 * PowerSeries.X ^ d 1) = 0 := by
    intro d hd_neq
    by_cases hd : d 0 = 0
    · -- the case `d 0 = 0`
      by_cases hd' : d 1 = 0
      · -- the case d 1 = 0
        have d_is_zero : d = 0 := Finsupp.ext fun n => by fin_cases n <;> simp [hd, hd']
        simp [d_is_zero, F.zero_constantCoeff]
      · -- the case d 1 ≠ 0
        simp [hd, PowerSeries.coeff_X_pow]
        by_cases hd₁ : d 1 = 1
        · -- the case d 1 = 1
          have d_eq : d = (Finsupp.single 1 1) :=
            Finsupp.ext <| fun x => by fin_cases x <;> simp [hd, hd₁]
          contradiction
        intro h
        by_contra _
        exact hd₁ (Eq.symm h)
    · -- the case `d 0 ≠ 0`
      simp [zero_pow hd]
  simp [finsum_eq_single _ _ eq_aux, lin_coeff_Y, PowerSeries.coeff_X]

/-- The constant coefficient of `F(X, 0)` is `0`. -/
lemma constantCoeff_of_subst_X₀ :
    PowerSeries.constantCoeff (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) (R := R) = 0 := by
  rw [PowerSeries.constantCoeff, constantCoeff_subst_zero (by simp) F.zero_constantCoeff]

/-- The constant coefficient of `F(0, X)` is `0`. -/
lemma constantCoeff_of_subst_X₁ :
  PowerSeries.constantCoeff (subst ![0, PowerSeries.X] F.toPowerSeries) (R := R) = 0 := by
  rw [PowerSeries.constantCoeff, constantCoeff_subst_zero (by simp) F.zero_constantCoeff]

/-- By the associativity of Formal Group Law,
  `F (F(X, 0), 0) = F (X, 0)`. -/
lemma self_comp_aux :
  (PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries)) ∘
  (PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries : PowerSeries R)) =
  (PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries : PowerSeries R) (R := R)) := by
  obtain assoc_eq := F.assoc
  have has_subst_aux : PowerSeries.HasSubst (subst ![PowerSeries.X, 0] F.toPowerSeries (S := R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero <| by
      rw [constantCoeff_subst_zero (by simp) F.zero_constantCoeff]
  have has_subst_map_aux : HasSubst ![PowerSeries.X (R := R), 0, 0] :=
    hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp
  /- prove that F(F(X,0),0) = F(X, F(0, 0)). -/
  have eq_aux₁ : subst ![PowerSeries.X (R := R), 0, 0] (subst ![subst ![Y₀, Y₁] F.toPowerSeries, Y₂] F.toPowerSeries (S := R)) =
    subst ![PowerSeries.X (R := R), 0, 0] (subst ![Y₀, subst ![Y₁, Y₂] F.toPowerSeries (S := R)] F.toPowerSeries) := by
    rw [assoc_eq]
  have left_eq : subst ![PowerSeries.X (R := R), 0, 0] (subst ![subst ![Y₀, Y₁] F.toPowerSeries, Y₂] F.toPowerSeries (S := R)) =
    ((PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries : PowerSeries R) (R := R)) ∘
    (PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries : PowerSeries R) (R := R))) PowerSeries.X := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply]
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_aux₁ F.zero_constantCoeff) has_subst_map_aux,
      PowerSeries.subst, subst_comp_subst_apply (has_subst_X₀) (PowerSeries.HasSubst.const
      has_subst_aux), subst_congr]
    funext s
    fin_cases s
    · -- the cases s = 0
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero]
      obtain aux := PowerSeries.HasSubst.const has_subst_aux
      -- unfold PowerSeries.X at aux
      rw [← PowerSeries.subst, PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
        has_subst_XY has_subst_map_aux, subst_congr]
      funext t; fin_cases t <;> simp [subst_X has_subst_map_aux]
    · -- the cases s = 1
      simp [subst_X has_subst_map_aux, ←coe_substAlgHom (PowerSeries.HasSubst.const has_subst_aux), map_zero]
  have right_eq : subst ![PowerSeries.X (R := R), 0, 0] (subst ![Y₀, subst ![Y₁, Y₂] F.toPowerSeries] F.toPowerSeries (S := R)) =
    (PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries : PowerSeries R) (R := R)) PowerSeries.X := by
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_aux₂ (F.zero_constantCoeff)) has_subst_map_aux, subst_congr]
    funext s
    fin_cases s
    · -- the cases s = 0
      simp [subst_X has_subst_map_aux]
    · -- the cases s = 1
      simp [subst_comp_subst_apply has_subst_YZ has_subst_map_aux]
      have eq_aux₃ :  subst (0 : Fin 2 → PowerSeries R) F.toPowerSeries = 0 := by
        have aux : HasSubst (0 : Fin 2 → PowerSeries R) := by
          exact hasSubst_of_constantCoeff_zero (congrFun rfl)
        ext n
        rw [PowerSeries.coeff, coeff_subst aux]
        simp
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        by_cases hd₀ : d = 0
        · simp [hd₀, F.zero_constantCoeff]
        · -- the case d ≠ 0
          have dneq : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
            by_contra hc
            simp at hc
            have deq : d = 0 := Finsupp.ext fun n => by fin_cases n <;> simp [hc]
            contradiction
          obtain hd₁ | hd₁ := dneq
          <;> simp [zero_pow hd₁]
      rw [←eq_aux₃]
      exact subst_congr <| by
        funext t; fin_cases t <;> simp [eq_aux₃, subst_X has_subst_map_aux]
  rw [left_eq, right_eq] at eq_aux₁
  funext g
  have eq_aux₂ : g = PowerSeries.subst PowerSeries.X g := by
    simp only [PowerSeries.X_subst]
  nth_rw 2 [eq_aux₂]
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X') has_subst_aux, ←right_eq,
    ←assoc_eq, left_eq]
  simp [PowerSeries.subst_X has_subst_aux, PowerSeries.subst_comp_subst_apply has_subst_aux has_subst_aux]

/-- By the associativity of Formal Group Law,
  `F (0, F(0, X)) = F (0, X)`. -/
lemma self_comp_aux' :
  (PowerSeries.subst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries)) ∘
  (PowerSeries.subst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries)) =
  (PowerSeries.subst (subst ![0, PowerSeries.X] F.toPowerSeries) (R := R)) := by
  obtain assoc_eq := F.assoc
  have has_subst_aux : PowerSeries.HasSubst (subst ![0, PowerSeries.X] F.toPowerSeries (S := R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero <| by
      rw [constantCoeff_subst_zero (by simp) F.zero_constantCoeff]
  have has_subst_map_aux : HasSubst ![0, 0, PowerSeries.X (R := R)] :=
    hasSubst_of_constantCoeff_zero <| fun s => by fin_cases s <;> simp
  /- prove that F(F(X,0),0) = F(X, F(0, 0)). -/
  have left_eq : subst ![0, 0, PowerSeries.X (R := R)] (subst ![Y₀, subst ![Y₁, Y₂] F.toPowerSeries] F.toPowerSeries (S := R)) =
    ((PowerSeries.subst (subst ![0, PowerSeries.X] F.toPowerSeries : PowerSeries R) (R := R)) ∘
    (PowerSeries.subst (subst ![0, PowerSeries.X] F.toPowerSeries : PowerSeries R) (R := R))) PowerSeries.X := by
    simp
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_aux₂ F.zero_constantCoeff) has_subst_map_aux,
      PowerSeries.subst, subst_comp_subst_apply (has_subst_X₁)
      (PowerSeries.HasSubst.const has_subst_aux)]
    apply subst_congr
    funext s; fin_cases s
    · -- the cases s = 0
      simp [subst_X has_subst_map_aux, ←coe_substAlgHom (PowerSeries.HasSubst.const has_subst_aux), map_zero]
    · -- the cases s = 1
      simp
      obtain aux := (PowerSeries.HasSubst.const has_subst_aux)
      rw [← PowerSeries.subst, PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
        has_subst_YZ has_subst_map_aux]
      apply subst_congr
      funext t
      fin_cases t <;> simp [subst_X has_subst_map_aux]
  have right_eq : subst ![0, 0, PowerSeries.X (R := R)] (subst ![subst ![Y₀, Y₁] F.toPowerSeries, Y₂] F.toPowerSeries (S := R)) =
    (PowerSeries.subst (subst ![0, PowerSeries.X] F.toPowerSeries : PowerSeries R) (R := R)) PowerSeries.X := by
    rw [PowerSeries.subst_X has_subst_aux, subst_comp_subst_apply
      (has_subst_aux₁ (F.zero_constantCoeff)) has_subst_map_aux]
    apply subst_congr
    funext s; fin_cases s
    · -- the cases s = 0
      simp [subst_comp_subst_apply has_subst_XY has_subst_map_aux]
      have eq_aux₃ :  subst (0 : Fin 2 → PowerSeries R) F.toPowerSeries = 0 := by
        ext n
        rw [PowerSeries.coeff, coeff_subst <| hasSubst_of_constantCoeff_zero (congrFun rfl)]
        simp
        apply finsum_eq_zero_of_forall_eq_zero <| fun d => by

          by_cases hd₀ : d = 0
          · simp [hd₀, F.zero_constantCoeff]
          · -- the case d ≠ 0
            have dneq : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
              by_contra hc
              simp at hc
              have deq : d = 0 := Finsupp.ext fun n => by fin_cases n <;> simp [hc]
              contradiction
            obtain hd₁ | hd₁ := dneq
            · simp [zero_pow hd₁]
            · simp [zero_pow hd₁]
      rw [←eq_aux₃]
      apply subst_congr
      funext t; fin_cases t <;> simp [eq_aux₃, subst_X has_subst_map_aux]
    · -- the cases s = 1
      simp [subst_X has_subst_map_aux]
  funext g
  have eq_aux₂ : g = PowerSeries.subst PowerSeries.X g := by
    simp
  nth_rw 2 [eq_aux₂]
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X') has_subst_aux, ←right_eq,
    assoc_eq, left_eq]
  simp [PowerSeries.subst_X has_subst_aux, PowerSeries.subst_comp_subst_apply has_subst_aux has_subst_aux]

/-- Given a power series `f`, if substition `f` into any power series is identity, then `f = X`. -/
lemma PowerSeries.subst_eq_id_iff_eq_X (f : PowerSeries R) (hf : PowerSeries.HasSubst f) :
  PowerSeries.subst f = id ↔ f = PowerSeries.X := by
  constructor
  · intro h
    rw [←PowerSeries.subst_X hf (R := R), h, id_eq]
  · intro h
    rw [h]
    funext g
    simp

/-- Given a formal group law `F`, `F(X,0) = X`. -/
theorem zero_right : subst ![PowerSeries.X, 0] F.toPowerSeries = PowerSeries.X (R := R) := by
  have h₀ : IsUnit (PowerSeries.coeff 1 (subst ![PowerSeries.X, 0] F.toPowerSeries) (R := R)) := by
    simp [coeff_of_X₀_of_subst_X₀]
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := PowerSeries.exist_subst_inv _  h₀ (constantCoeff_of_subst_X₀ F)
  have eq_aux :
    (PowerSeries.subst g) ∘ (PowerSeries.subst (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) (R := R)) ∘
    (PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries) (R := R)) =
    (PowerSeries.subst g) ∘
    (PowerSeries.subst (subst ![PowerSeries.X, 0] F.toPowerSeries : PowerSeries R) (R := R)) := by
    rw [self_comp_aux]
  simp [←Function.comp_assoc, hg₂] at eq_aux
  exact (PowerSeries.subst_eq_id_iff_eq_X _
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_of_subst_X₀ F))).mp eq_aux

/-- Given a formal group law `F`, `F(0, X) = X`. -/
theorem zero_left : subst ![0, PowerSeries.X] F.toPowerSeries = PowerSeries.X (R := R) := by
  have h₀ : IsUnit (PowerSeries.coeff 1 (subst ![0, PowerSeries.X] F.toPowerSeries) (R := R)) := by
    simp [coeff_of_X₁_of_subst_X₁]
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := PowerSeries.exist_subst_inv _  h₀ (constantCoeff_of_subst_X₁ F)
  have eq_aux :
    (PowerSeries.subst g) ∘ (PowerSeries.subst (subst ![0, PowerSeries.X] F.toPowerSeries : PowerSeries R) (R := R)) ∘
    (PowerSeries.subst (subst ![0, PowerSeries.X] F.toPowerSeries : PowerSeries R) (R := R)) =
    (PowerSeries.subst g) ∘
    (PowerSeries.subst (subst ![0, PowerSeries.X] F.toPowerSeries : PowerSeries R) (R := R)) := by
    rw [self_comp_aux']
  simp [←Function.comp_assoc, hg₂] at eq_aux
  exact (PowerSeries.subst_eq_id_iff_eq_X (subst ![0, PowerSeries.X] F.toPowerSeries)
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_of_subst_X₁ F))).mp eq_aux

theorem zero_add {f : MvPowerSeries σ R} (h : constantCoeff f = 0) : 0 +[F] f = f := calc
  _ = PowerSeries.subst f (R := R) (subst ![0, PowerSeries.X] F.toPowerSeries) := by
    rw [PowerSeries.subst, subst_comp_subst_apply has_subst_X₁
    <| hasSubst_of_constantCoeff_zero fun s ↦ h]
    apply subst_congr
    funext s; fin_cases s
    · simp
      rw [←substAlgHom_apply <| hasSubst_of_constantCoeff_zero fun s ↦ h]
      exact Eq.symm <| map_zero <| substAlgHom <| hasSubst_of_constantCoeff_zero fun s ↦ h
    · simp
      rw [←PowerSeries.subst, PowerSeries.subst_X <| PowerSeries.HasSubst.of_constantCoeff_zero h]
  _ = _ := by
    rw [zero_left, PowerSeries.subst_X <| PowerSeries.HasSubst.of_constantCoeff_zero h]

theorem add_zero {f : MvPowerSeries σ R} (h : constantCoeff f = 0) : f +[F] 0 = f := calc
  _ = PowerSeries.subst f (R := R) (subst ![PowerSeries.X, 0] F.toPowerSeries) := by
    rw [PowerSeries.subst, subst_comp_subst_apply has_subst_X₀
    <| hasSubst_of_constantCoeff_zero fun s ↦ h]
    apply subst_congr
    funext s; fin_cases s
    · simp
      rw [←PowerSeries.subst, PowerSeries.subst_X <| PowerSeries.HasSubst.of_constantCoeff_zero h]
    · simp
      rw [←substAlgHom_apply <| hasSubst_of_constantCoeff_zero fun s ↦ h]
      exact Eq.symm <| map_zero <| substAlgHom <| hasSubst_of_constantCoeff_zero fun s ↦ h
  _ = _ := by
    rw [zero_right, PowerSeries.subst_X <| PowerSeries.HasSubst.of_constantCoeff_zero h]

lemma coeff_pow_X₀ {n : ℕ}(hn : n ≠ 1) : coeff (Finsupp.single 0 n) F.toPowerSeries = 0 := by
  calc
    _ = PowerSeries.coeff n (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
      rw [PowerSeries.coeff, coeff_subst has_subst_X₀, finsum_eq_single _ (single 0 n)]
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
    _ = 0 := by
      rw [zero_right, PowerSeries.coeff_X, if_neg hn]

lemma coeff_pow_X₁ {n : ℕ} (hn : n ≠ 1) : coeff (Finsupp.single 1 n) F.toPowerSeries = 0 := by
  calc
    _ = PowerSeries.coeff n (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
      rw [PowerSeries.coeff, coeff_subst has_subst_X₁, finsum_eq_single _ (single 1 n)]
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
    _ = 0 := by
      rw [zero_left, PowerSeries.coeff_X, if_neg hn]

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

/-- Let `G₁, G₂` be two formal group laws over `CommRing A`. A homomorphism (over `A`)
  `F (X, Y) → G (X, Y)` is a power series `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` with coefficients
  in `A` without constant term such that `α(F (X, Y)) = G (α (X), α (Y))`. -/
@[ext]
structure FormalGroupHom  (G₁ G₂ : FormalGroup R) where
  toPowerSeries : PowerSeries R
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  hom : toPowerSeries.subst (G₁.toPowerSeries) = G₂.toPowerSeries.subst (R := R) (toPowerSeries.toMvPowerSeries ·)

section FormalGroupIso

/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if there exists a
  homomorphism `β(X) : G (X, Y) → F (X, Y)` such that `α ∘ β = id,  β ∘ α = id`. -/
@[ext]
structure FormalGroupIso (G₁ G₂ : FormalGroup R) where
  toHom : FormalGroupHom G₁ G₂
  invHom : FormalGroupHom G₂ G₁
  left_inv : (PowerSeries.subst toHom.toPowerSeries) ∘ (PowerSeries.subst invHom.toPowerSeries) = id
  right_inv : (PowerSeries.subst invHom.toPowerSeries) ∘ (PowerSeries.subst toHom.toPowerSeries) = id

/-- An isomorphism `α(X) : F (X, Y) → G (X, Y)`, `α(X) = a₁ * X + a₂ * X ^ 2 + ⋯`
  is called strict isomorphism if `a₁ = 1`.-/
@[ext]
structure FormalGroupStrictIso (G₁ G₂ : FormalGroup R) extends FormalGroupIso G₁ G₂ where
  one_coeff_one : toHom.toPowerSeries.coeff 1 = 1

theorem FormalGroupStrictIso.ext_iff' (G₁ G₂ : FormalGroup R) (α β : FormalGroupStrictIso G₁ G₂) :
    α = β ↔ α.toHom = β.toHom := by
  rw [FormalGroupStrictIso.ext_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, FormalGroupHom.ext ?_⟩⟩
  obtain ⟨g, h₁, h₂⟩ := PowerSeries.exist_unique_subst_inv_left _ (by simp [β.one_coeff_one])
    β.toHom.zero_constantCoeff
  simp only [and_imp] at h₂
  rw [h₂ _ (h ▸ α.left_inv) α.invHom.zero_constantCoeff,
    h₂ _ β.left_inv β.invHom.zero_constantCoeff]

end FormalGroupIso

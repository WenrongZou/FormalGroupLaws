import FormalGroupLaws.Basic
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.TensorProduct.Basic
import FormalGroupLaws.AddInverse
import Mathlib.RingTheory.MvPowerSeries.Order

noncomputable section

/- Main Result : In this file, we prove that for any one dimensional formal group law `F(X, Y)`
  over coefficient ring `R`, `F(X, Y)` is commutative formal group law if and
  only if `R` doest contain a nonzero element which is both torsion and nilpotent.-/

variable {R : Type*} [CommRing R] (F : FormalGroup R) [Nontrivial R] {σ : Type*}

namespace FormalGroup

open Algebra Submodule MvPowerSeries TensorProduct LinearMap

omit [Nontrivial R] in
/-- For any formal group law `F(X,Y)`, `F(X,Y) = F(Y,X)` if and only if
  for any `i, j ∈ ℕ`, `a_ij = a_ji`, where `a_ij` is coefficient of `X^i Y^j`. -/
theorem comm_iff_coeff_symm :
  F.comm ↔ ∀ (i j : ℕ), coeff (coeff_two i j) F.toFun = coeff (coeff_two j i) F.toFun := by
  constructor
  -- forward direction
  · intro h i j
    obtain h' := MvPowerSeries.ext_iff.mp h (coeff_two i j)
    rw [h', coeff_subst has_subst_swap]
    simp
    have aux : (coeff (coeff_two i j)) ((X₁ (R := R)) ^ j * X₀ ^ i)  = 1 := by
      simp [coeff_two, X_pow_eq, monomial_mul_monomial]
      rw [coeff_monomial, if_pos (by rw [AddCommMagma.add_comm])]
    rw [finsum_eq_single _ (coeff_two j i)]
    · simp [aux]
    · intro n hn
      have aux₁ : (coeff (coeff_two i j)) ((X₁ (R := R)) ^ n 0 * X₀ ^ n 1) = 0 := by
        simp [X_pow_eq, monomial_mul_monomial]
        rw [coeff_monomial, if_neg]
        obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hn
        refine Finsupp.ne_iff.mpr ?_
        fin_cases a
        · simp at ha; use 1; simp [Ne.symm ha]
        · simp at ha; use 0; simp [Ne.symm ha]
      simp [aux₁]
  -- backward direction
  · intro h; ext n
    have n_eq : n = coeff_two (n 0) (n 1) := by
      refine Finsupp.ext ?_
      intro a; fin_cases a; all_goals simp [coeff_two]
    nth_rw 1 [n_eq]
    rw [h, coeff_subst has_subst_swap, finsum_eq_single _  (coeff_two (n 1) (n 0))]
    · simp
      have aux : (coeff n) ((X₁ (R := R)) ^ n 1 * X₀ ^ n 0) = 1 := by
        simp [X_pow_eq, monomial_mul_monomial]
        rw [coeff_monomial, if_pos]
        refine Finsupp.ext ?_
        intro a; fin_cases a; all_goals simp
      simp [aux]
    · intro d hd; simp
      have aux : (coeff n) ((X₁ (R := R)) ^ d 0 * X₀ ^ d 1) = 0 := by
        simp [X_pow_eq, monomial_mul_monomial]
        rw [coeff_monomial, if_neg]
        obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hd
        refine Finsupp.ne_iff.mpr ?_
        fin_cases a
        · simp at ha; use 1; simp [Ne.symm ha]
        · simp at ha; use 0; simp [Ne.symm ha]
      simp [aux]

omit [Nontrivial R] in
/-- For any formal group law `F(X,Y)`, `F(X,Y) = F(Y,X)` if and only if
  for any `i, j ∈ ℕ`, `a_ij - a_ji = 0`, where `a_ij` is coefficient of `X^i Y^j`. -/
theorem comm_iff_coeff_symm' :
  F.comm ↔ ∀ (i j : ℕ), coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun = 0 := by
  constructor
  · intro hF
    simp_rw [(comm_iff_coeff_symm F).mp hF]
    exact fun i j => by ring
  · intro h
    apply ((comm_iff_coeff_symm F).mpr)
    intro i j
    conv => rhs; rw [←add_zero ((coeff (coeff_two j i)) F.toFun), ←h i j]
    ring

/--  Over a coefficient ring `R` of characteristic zero,
if `R` contains no nonzero element that is both torsion and nilpotent,
then any one-dimensional formal group law over `R` is commutative. -/
theorem comm_of_char_zero_and_no_torsion_nilpotent (h : IsAddTorsionFree R) :
  ¬ ∃ r : R, r ≠ 0 ∧ IsNilpotent r ∧ addOrderOf r ≠ 0 → F.comm := by
  sorry

/-- Given a formal group law `F(X,Y)`, assume that `F(X,Y)` is not commutative, then
  there exist a nonzero formal group homomorphism from `F(X,Y)` to additive formal
  group law `Gₐ` or multiplicative formal group law `Gₘ`.-/
theorem exists_nonzero_hom_to_Ga_or_Gm_of_not_comm (h : ¬ F.comm) :
  (∃ (α : FormalGroupHom F (Gₐ (R := R))), α.toFun ≠ 0) ∨
  (∃ (α : FormalGroupHom F (Gₘ (R := R))), α.toFun ≠ 0) := by

  sorry

def commutator : MvPowerSeries (Fin 2) R :=
  X₀ +[F] X₁ +[F] (addInv F X₀) +[F] (addInv F X₁)

lemma HasSubst.powerseries_commutator : PowerSeries.HasSubst F.commutator := sorry

lemma add_addInv_eq_zero {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
  f +[F] addInv F f = 0 := by
  have eq_aux : PowerSeries.X +[F] addInv F PowerSeries.X = (0 : PowerSeries R)  := by
    have aux : addInv F PowerSeries.X = addInv_X F := by
      unfold addInv
      rw [←PowerSeries.map_algebraMap_eq_subst_X]
      simp
    rw [aux, X_add_addInv_X_eq_zero]
  calc
    _ = PowerSeries.subst f (PowerSeries.X +[F] addInv F PowerSeries.X) := by
      unfold add
      have has_subst₁ : HasSubst ![PowerSeries.X, addInv F PowerSeries.X] := by
        refine HasSubst.FinPairing ?_ ?_
        simp
        rw [addInv, PowerSeries.subst, constantCoeff_subst
          (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X'))]
        simp
        apply finsum_eq_zero_of_forall_eq_zero
        intro x
        by_cases hx : x = 0
        · simp [hx]
          exact rfl
        rw [zero_pow]
        simp
        by_contra hc
        have xeq : x = 0 := by
          exact Eq.symm (Finsupp.ext fun a ↦ _root_.id (Eq.symm hc))
        contradiction
      rw [PowerSeries.subst, subst_comp_subst_apply has_subst₁
        (PowerSeries.HasSubst.const <| PowerSeries.HasSubst.of_constantCoeff_zero hf)]
      apply subst_congr
      funext s; fin_cases s
      · simp
        rw [PowerSeries.X, subst_X <| hasSubst_of_constantCoeff_zero fun s ↦ hf]
      · simp
        unfold addInv
        rw [PowerSeries.subst, PowerSeries.subst, subst_comp_subst_apply
          (PowerSeries.HasSubst.const (PowerSeries.HasSubst.X'))
          (hasSubst_of_constantCoeff_zero fun s ↦ hf)]
        apply subst_congr
        funext s
        rw [PowerSeries.X, subst_X <| hasSubst_of_constantCoeff_zero fun s ↦ hf]
    _ = _ := by
      rw [eq_aux]
      ext n
      rw [PowerSeries.coeff_subst <| PowerSeries.HasSubst.of_constantCoeff_zero hf]
      simp



lemma add_addInv_eq_zero' (f : MvPowerSeries σ R) :
  addInv F f +[F] f = 0 := sorry

lemma zero_add_eq_self (f : MvPowerSeries σ R) :
  0 +[F] f = f := sorry

lemma zero_add_eq_self' (f : MvPowerSeries σ R) :
  f +[F] 0 = f := sorry

lemma comm_iff_commutator_eq_zero :
  F.comm ↔ commutator F = 0 := by
  constructor
  · intro hF
    have aux : constantCoeff (X₀ (R := R)) = 0 := by
      exact constantCoeff_X 0
    conv =>
      lhs
      rw [commutator, add_assoc X₀, add_comm hF X₁, ←add_assoc X₀,
        add_addInv_eq_zero _ (constantCoeff_X 0), add_assoc, add_addInv_eq_zero _ (constantCoeff_X 1), zero_add_eq_self]
  · intro h
    rw [commutator] at h
    unfold comm
    calc
      _ = X₀ +[F] X₁ +[F] addInv F X₀ +[F] addInv F X₁ +[F] X₁ +[F] X₀ := by
        rw [add_assoc <| X₀ +[F] X₁ +[F] addInv F X₀, add_addInv_eq_zero', zero_add_eq_self',
          add_assoc <| X₀ +[F] X₁, add_addInv_eq_zero', zero_add_eq_self']
        have aux : ![X₀, X₁] = (X : Fin 2 → MvPowerSeries (Fin 2) R) := by
          simp [@funext_iff]
        simp [add, aux, ←map_algebraMap_eq_subst_X]
      _ = X₁ +[F] X₀ := by
        rw [h, zero_add_eq_self]


-- variable (G G' : FormalGroup R) {α : FormalGroupHom G G'} in
-- scoped[FormalGroup] notation:65 α:65 " •[" G:0 "] " f:66 =>
--   PowerSeries.subst f α.toFun

lemma hom_add {G₁ G₂ : FormalGroup R} {α : FormalGroupHom G₁ G₂} (f g : MvPowerSeries σ R):
  PowerSeries.subst (f +[G₁] g) α.toFun = (PowerSeries.subst f α.toFun) +[G₂]
    (PowerSeries.subst g α.toFun) := sorry

/- Let `α` be a formal group homomorphism from `F(X,Y)` to `F'(X,Y)`, if `F'` is commutative
  then `α (commutator F) = 0` -/
lemma zero_of_target_comm {F' : FormalGroup R} (α : FormalGroupHom F F') (hF' : F'.comm):
  PowerSeries.subst (commutator F) α.toFun = 0 := by
  simp [commutator, hom_add]
  rw [add_assoc <| PowerSeries.subst X₀ α.toFun, add_comm hF' <| PowerSeries.subst X₁ α.toFun,
    ←add_assoc, ←hom_add, add_addInv_eq_zero _ (constantCoeff_X 0), add_assoc, ←hom_add,
    add_addInv_eq_zero _ (constantCoeff_X 1), ←hom_add,
    zero_add_eq_self]
  ext d
  simp [PowerSeries.coeff_subst PowerSeries.HasSubst.zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  by_cases hx : x = 0
  · simp [hx, α.zero_constantCoeff]
  · simp [zero_pow hx]

-- lemma MvPowerSeries.homogeneousComponent_pow_of_le_order {p n : ℕ} {f : MvPowerSeries.} :
--   homogeneousComponent


/-- Assume that `R` is an integral domain, `F(X,Y)` and `F'(X,Y)` are one dimensional
  formal group law over `R`, if `F'(X,Y)` is commutative and there exist a nonzero
  homomorphism from `F(X,Y)` to `F'(X,Y)`, then `F(X,Y)` is commutative.-/
theorem comm_of_exists_nonzero_hom_to_comm (F' : FormalGroup R) [IsDomain R]
  (α : FormalGroupHom F F') (ha : α.toFun ≠ 0) :
  F'.comm → F.comm := by
  intro hF'
  by_contra hc
  have commutator_neZero : commutator F ≠ 0 := by
    by_contra hc'
    obtain h := (comm_iff_commutator_eq_zero _).mpr hc'
    contradiction
  let m := MvPowerSeries.order (F.commutator)
  let r := PowerSeries.order α.toFun
  obtain a_eq := ne_zero_iff_order_finite.mp ha
  obtain meq := ne_zero_iff_order_finite.mp commutator_neZero
  obtain h := zero_of_target_comm F α hF'

  have exist_nonZero_coeff : ∃ d, (coeff d) (PowerSeries.subst F.commutator α.toFun) ≠ 0 := by
    obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order meq
    have exist_aux : ∃ (n : ℕ), (coeff (Finsupp.equivFunOnFinite.invFun ![n, m.toNat - n]))
      F.commutator ≠ 0 := by
      use d 0
      have eq_aux : m.toNat - d 0 = d 1 := by
        unfold Finsupp.degree at hd₂
        simp at hd₂
        rw [show m = F.commutator.order by rfl]
        have aux : ∑ x ∈ d.support, (d x : ℕ∞) = d 0 + d 1 := by
          calc
            _ = ∑ x : Fin 2, (d x : ℕ∞) := by
              refine Fintype.sum_subset <| fun i hi => Finsupp.mem_support_iff.mpr
                <| fun a ↦ hi (congrArg Nat.cast a)
            _ = _ := by
              rfl
        rw [aux] at hd₂
        have aux' : d 0 + d 1 = F.commutator.order.toNat := by
          rw [←hd₂]
          rfl
        rw [←aux']
        simp
      rw [eq_aux]
      have d_eq : (Finsupp.equivFunOnFinite.invFun ![d 0, d 1]) = d := by
        refine Finsupp.ext ?_
        intro i; fin_cases i
        all_goals simp
      simp [d_eq, hd₁]
    have decidable : DecidablePred fun n ↦ (coeff (Finsupp.equivFunOnFinite.invFun
      ![n, m.toNat - n])) F.commutator ≠ 0 := Classical.decPred fun n ↦
          ¬(coeff (Finsupp.equivFunOnFinite.symm ![n, m.toNat - n])) F.commutator = 0
    let n := Nat.find exist_aux
    let d₀ := (Finsupp.equivFunOnFinite.symm ![n, m.toNat - n])
    let d' := Finsupp.equivFunOnFinite.symm ![n * r.toNat, (m.toNat - n) * r.toNat]
    have d'_eq : d' = Finsupp.equivFunOnFinite.symm ![n * r.toNat, (m.toNat - n) * r.toNat] := rfl
    have mge : m.toNat ≥ n := by sorry
    use d'
    rw [PowerSeries.coeff_subst <| HasSubst.powerseries_commutator F]
    simp
    have eq_single : ∑ᶠ (d : ℕ), (PowerSeries.coeff d) α.toFun *
      (coeff d') (F.commutator ^ d) = (PowerSeries.coeff r.toNat) α.toFun *
      (coeff d') (F.commutator ^ r.toNat) := by
      apply finsum_eq_single
      intro x hx
      by_cases hxLe : x < r.toNat
      · simp [PowerSeries.coeff_of_lt_order_toNat x hxLe]
      · sorry
    rw [eq_single]

    sorry
  have ne_zero : PowerSeries.subst F.commutator α.toFun ≠ 0 := by
    by_contra hc
    have forall_coeff_eq_zero : ∀ d, (coeff d) (PowerSeries.subst F.commutator α.toFun) = 0 := by
      simp [hc]
    simp_all





  have order_aux : (order (PowerSeries.subst F.commutator α.toFun)).toNat =
    order (PowerSeries.subst F.commutator α.toFun):= by
    -- have aux : (PowerSeries.subst F.commutator α.toFun).order < ⊤ := by
    --   sorry
    obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order meq
    have exist_aux : ∃ (n : ℕ), (coeff (Finsupp.equivFunOnFinite.invFun ![n, m.toNat - n]))
      F.commutator ≠ 0 := by
      use d 0
      have eq_aux : m.toNat - d 0 = d 1 := by
        unfold Finsupp.degree at hd₂
        simp at hd₂
        rw [show m = F.commutator.order by rfl]
        have aux : ∑ x ∈ d.support, (d x : ℕ∞) = d 0 + d 1 := by
          calc
            _ = ∑ x : Fin 2, (d x : ℕ∞) := by
              refine Fintype.sum_subset <| fun i hi => Finsupp.mem_support_iff.mpr
                <| fun a ↦ hi (congrArg Nat.cast a)
            _ = _ := by
              rfl
        rw [aux] at hd₂
        have aux' : d 0 + d 1 = F.commutator.order.toNat := by
          rw [←hd₂]
          rfl
        rw [←aux']
        simp
      rw [eq_aux]
      have d_eq : (Finsupp.equivFunOnFinite.invFun ![d 0, d 1]) = d := by
        refine Finsupp.ext ?_
        intro i; fin_cases i
        all_goals simp
      simp [d_eq, hd₁]
    have decidable : DecidablePred fun n ↦ (coeff (Finsupp.equivFunOnFinite.invFun
      ![n, m.toNat - n])) F.commutator ≠ 0 := Classical.decPred fun n ↦
          ¬(coeff (Finsupp.equivFunOnFinite.symm ![n, m.toNat - n])) F.commutator = 0
    let n := Nat.find exist_aux
    let d₀ := (Finsupp.equivFunOnFinite.symm ![n, m.toNat - n])
    let d' := Finsupp.equivFunOnFinite.symm ![n * r.toNat, (m.toNat - n) * r.toNat]
    have d'_eq : d' = Finsupp.equivFunOnFinite.symm ![n * r.toNat, (m.toNat - n) * r.toNat] := rfl
    have mge : m.toNat ≥ n := by
      simp_all
    have neq : PowerSeries.subst F.commutator α.toFun ≠ 0 := by
      apply ne_zero_iff_exists_coeff_ne_zero_and_degree.mpr
      use (m.toNat * r.toNat), d'
      constructor
      ·
        rw [PowerSeries.coeff_subst <| HasSubst.powerseries_commutator F]
        simp
        have eq_single : ∑ᶠ (d : ℕ), (PowerSeries.coeff d) α.toFun *
          (coeff d') (F.commutator ^ d) = (PowerSeries.coeff r.toNat) α.toFun *
          (coeff d') (F.commutator ^ r.toNat) := by
          apply finsum_eq_single
          intro x hx
          by_cases hxLe : x < r.toNat
          · simp [PowerSeries.coeff_of_lt_order_toNat x hxLe]
          · simp_all only [ne_eq, ENat.coe_toNat_eq_self, order_eq_top_iff, not_false_eq_true]
        rw [eq_single]
        have coeff_ne₁ : (PowerSeries.coeff r.toNat) α.toFun ≠ 0 := PowerSeries.coeff_order ha
        have coeff_ne₂ : (coeff d') (F.commutator ^ r.toNat) ≠ 0 := by
          simp [coeff_pow]
          let l : ℕ →₀ (Fin 2) →₀ ℕ := {
            support := Finset.range r.toNat
            toFun := fun x => if x ∈ Finset.range r.toNat then
              d₀ else 0
            mem_support_toFun := by
              intro a
              constructor
              · intro h
                rw [if_pos h]
                (expose_names; exact fun a ↦ ne_zero h_1)
              · simp_all
          }
          have eq_aux : ∑ l ∈ (Finset.range r.toNat).finsuppAntidiag d',
            ∏ i ∈ Finset.range r.toNat, (coeff (l i)) F.commutator =
            ∏ i ∈ Finset.range r.toNat, (coeff (l i)) F.commutator := by
            refine Finset.sum_eq_single l ?_ ?_
            ·
              intro b hb bneq
              simp at hb
              obtain ⟨hb₁, hb₂⟩ := hb
              have sum_eq0 : ∑ i ∈ (Finset.range r.toNat), (b i 0) = n * r.toNat := by
                simp [show n * r.toNat = d' 0 by rfl, ←hb₁]
              have sum_eq1 : ∑ i ∈ (Finset.range r.toNat), (b i 1) = (m.toNat - n) * r.toNat := by
                simp [show (m.toNat - n) * r.toNat = d' 1 by rfl, ←hb₁]
              have exist_i :(∃ i ∈ Finset.range r.toNat, b i 0 < n) ∨
                (∃ i ∈ Finset.range r.toNat, b i 1 > m.toNat - n) := by
                by_contra hcontra
                simp at hcontra
                obtain ⟨hcontra, hcontra'⟩ := hcontra
                have le_aux : ∀ x < r.toNat, (b x) 0 ≤ n := by
                  by_contra h_le_aux
                  simp at h_le_aux
                  obtain ⟨x, hx, hx'⟩ := h_le_aux
                  have hcontra' : ∑ i ∈ Finset.range r.toNat, (b i) 0 >
                    n * r.toNat := by
                    calc
                      _ > ∑ i ∈ Finset.range r.toNat, n := by
                        apply Finset.sum_lt_sum (by simp_all)
                        use x
                        simp_all
                      _ = _ := by simp [Finset.sum_const, mul_comm]
                  linarith
                have forall_eq : ∀ x < r.toNat, b x 0 = n := by
                  intro i hi
                  nlinarith [hcontra i hi, le_aux i hi]
                have le_aux' : ∀ x < r.toNat, (b x) 1 ≥ m.toNat - n := by
                  by_contra h_le_aux
                  simp at h_le_aux
                  obtain ⟨x, hx, hx'⟩ := h_le_aux
                  have hcontra' : ∑ i ∈ Finset.range r.toNat, (b i) 0 >
                    n * r.toNat := by
                    calc
                      _ > ∑ i ∈ Finset.range r.toNat, n := by
                        apply Finset.sum_lt_sum (by simp_all)
                        use x
                        simp_all
                      _ = _ := by simp [Finset.sum_const, mul_comm]
                  linarith
                have forall_eq' : ∀ x < r.toNat, b x 1 = m.toNat - n := by
                  intro i hi
                  nlinarith [hcontra' i hi, le_aux' i hi]
                have b_eq_l : b = l := by
                  ext x i
                  by_cases hx : x < r.toNat
                  · fin_cases i
                    · simp [l, if_pos hx, d₀, forall_eq x hx]
                    · simp [l, if_pos hx, d₀, forall_eq' x hx]
                  · have b_eq_zero : b x = 0 := by
                      have x_not_mem : x ∉ Finset.range r.toNat := by
                        simp only [Finset.mem_range, not_lt]
                        linarith
                      exact Finsupp.notMem_support_iff.mp fun a ↦ x_not_mem (hb₂ a)
                    simp [b_eq_zero, l, if_neg hx]
                contradiction
              -- apply Finset.prod_eq_zero
              by_cases b_sum : ∀ i ∈ Finset.range r.toNat, b i 0 + b i 1 = m.toNat
              · obtain ⟨i, hi₁, hi₂⟩ | ⟨i, hi₁, hi₂⟩ := exist_i
                · apply Finset.prod_eq_zero (i := i) hi₁
                  obtain n_min := Nat.find_min exist_aux hi₂
                  simp at n_min
                  have eq_aux : m.toNat - (b i) 0 = b i 1 := by simp [←b_sum i hi₁]
                  rw [eq_aux] at n_min
                  simp_all
                · apply Finset.prod_eq_zero (i := i) hi₁
                  have lt_aux : b i 0 < n := by
                    rw [←b_sum i hi₁] at hi₂
                    omega
                  obtain n_min := Nat.find_min exist_aux lt_aux
                  simp at n_min
                  have eq_aux : m.toNat - (b i) 0 = b i 1 := by simp [←b_sum i hi₁]
                  rw [eq_aux] at n_min
                  simp_all
              ·
                have exist_lt_order : ∃ i ∈ Finset.range r.toNat, b i 0 + b i 1 < m.toNat := by
                  by_contra hcontra
                  simp at hcontra
                  simp at b_sum
                  obtain ⟨i, hi₁, hi₂⟩ := b_sum
                  have gt_aux : (b i) 0 + (b i) 1 > m.toNat := by
                    obtain h := hcontra i hi₁
                    omega
                  have gt_aux' : ∑ i ∈ Finset.range r.toNat, ((b i) 0 + (b i) 1)
                    > m.toNat * r.toNat:= by
                    calc
                      _ > ∑ i ∈ Finset.range r.toNat, m.toNat := by
                        apply Finset.sum_lt_sum (by simp_all)
                        exact ⟨i, by simp [hi₁], gt_aux⟩
                      _ = _ := by
                        simp [mul_comm]
                  have eq_aux : ∑ i ∈ Finset.range r.toNat, ((b i) 0 + (b i) 1) =
                    m.toNat * r.toNat := by
                    calc
                      _ = ((Finset.range r.toNat).sum ⇑b) 0 +
                        ((Finset.range r.toNat).sum ⇑b) 1 := by
                        simp [Finset.sum_add_distrib]
                      _ = _ := by
                        simp [hb₁, d']
                        rw [←add_mul]
                        congr
                        omega
                  linarith
                obtain ⟨i, hi₁, hi₂⟩ := exist_lt_order
                apply Finset.prod_eq_zero (i := i) hi₁
                have degree_lt : (b i).degree < F.commutator.order.toNat := by
                  calc
                    _ = b i 0 + b i 1 := by
                      unfold Finsupp.degree
                      simp_all
                    _ < _ := by
                      linarith
                refine coeff_of_lt_order ?_
                rw [←meq]
                exact ENat.coe_lt_coe.mpr degree_lt
            · have mem_aux : l ∈  (Finset.range r.toNat).finsuppAntidiag d' := by
                simp

                sorry
              simp [mem_aux]
          rw [eq_aux]
          have eq_aux' : ∏ i ∈ Finset.range r.toNat, (coeff (l i)) F.commutator
            = (coeff d₀) F.commutator ^ r.toNat := by
            calc
              _ = ∏ i ∈ Finset.range r.toNat, (coeff d₀) F.commutator := by
                refine Finset.prod_congr rfl ?_
                intro x hx
                unfold l
                simp at ⊢ hx
                rw [if_pos hx]
              _ = _ := Eq.symm <| Finset.pow_eq_prod_const ((coeff d₀) F.commutator) r.toNat
          -- have eq_aux' : ∏ i ∈ Finset.range r.toNat, (coeff (l i)) F.commutator
          --   = ∏ i ∈ Finset.range r.toNat, (coeff d₀) F.commutator := by
          --   refine Finset.prod_congr rfl ?_
          --   intro x hx
          --   unfold l
          --   simp at ⊢ hx
          --   rw [if_pos hx]
          rw [eq_aux']
          obtain n_find_spec := Nat.find_spec exist_aux
          have ne_aux : (coeff d₀) F.commutator ≠ 0 := by
            unfold d₀
            simp_all
          exact pow_ne_zero r.toNat n_find_spec
        exact (mul_ne_zero_iff_right coeff_ne₂).mpr coeff_ne₁

        -- have eq_single : ∑ᶠ (d : Unit →₀ ℕ), (coeff d) α.toFun
        --   * (coeff d') (F.commutator ^ d PUnit.unit) =
        --   coeff (Finsupp.equivFunOnFinite.symm (r.toNat : Unit → ℕ)), α.toFun
      ·

        sorry

    -- use this MvPowerSeries.exists_coeff_ne_zero_and_order
    sorry
  have ne_top : order (PowerSeries.subst F.commutator α.toFun) ≠ ⊤ := by
    exact ENat.coe_toNat_eq_self.mp order_aux
  obtain h₁ := order_eq_top_iff.mpr h
  contradiction




/-- Assume that `R` is an integral domain, any one dimensional formal group law is
  commutative. -/
theorem comm_of_isDomain [IsDomain R] : F.comm := by
  by_contra hc
  obtain ⟨α, ha⟩| ⟨α, ha⟩ := exists_nonzero_hom_to_Ga_or_Gm_of_not_comm F hc
  · exact hc ((comm_of_exists_nonzero_hom_to_comm _ _ α ha ) Gₐ.comm)
  · exact hc ((comm_of_exists_nonzero_hom_to_comm _ _ α ha ) Gₘ.comm)


/-- This is a counter example that given `r` is a nonzero nilpotent and `ℤ-torsion`,
  there is a non-commutative formal group law. -/
def counter_example_F (r : R) (rNil : IsNilpotent r) (rTor : IsOfFinAddOrder r)
  (rNeq : r ≠ 0) : FormalGroup R :=
  let n := addOrderOf r
  have ngtone : n ≠ 1 := by
    by_contra hn; simp [n] at hn; contradiction
  let p := Nat.minFac n
  let b := (n / p) • r
  have bNil : IsNilpotent b := IsNilpotent.smul rNil (n / p)
  let m := nilpotencyClass b
  let c := b ^ (m - 1)
  have bneq₀ : b ≠ 0 := by
    have pos_aux : n / p > 0 := Nat.div_pos_iff.mpr
      ⟨Nat.minFac_pos n, Nat.minFac_le (IsOfFinAddOrder.addOrderOf_pos rTor)⟩
    obtain neq := Nat.ne_zero_of_lt pos_aux
    refine nsmul_ne_zero_of_lt_addOrderOf neq (Nat.div_lt_self
      (IsOfFinAddOrder.addOrderOf_pos rTor) ?_)
    exact Nat.Prime.one_lt (Nat.minFac_prime_iff.mpr ngtone)
  {
  toFun := by
    let n := addOrderOf r
    have ngtone : n ≠ 1 := by
      by_contra hn; simp [n] at hn; contradiction
    obtain p := Nat.minFac n
    let b := (n / p) • r
    have bNil : IsNilpotent b := IsNilpotent.smul rNil (n / p)
    let m := nilpotencyClass b
    let c := b ^ (m - 1)
    exact X₀ + X₁ + (C c) * X₀ * X₁ ^ p
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp
    rw [coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp)),
      X₀, X, X_pow_eq, mul_assoc, monomial_mul_monomial]
    simp
    have aux' : ((addOrderOf r / (addOrderOf r).minFac) : MvPowerSeries (Fin 2) R) =
      C (addOrderOf r / (addOrderOf r).minFac) (R := R) := by
      exact rfl
    have aux'' : (C (addOrderOf r / (addOrderOf r).minFac : R) * C r)
      = C (((addOrderOf r / (addOrderOf r).minFac : R) * r)) (R := R) (σ := Fin 2) := by
      simp
    rw [aux', aux'', ←map_pow, coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    simp
    refine Nat.ne_zero_iff_zero_lt.mpr (Nat.minFac_pos _)
  lin_coeff_Y := by
    simp
    rw [coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp)),
      X₀, X, X_pow_eq, mul_assoc, monomial_mul_monomial]
    simp
    have aux' : ((addOrderOf r / (addOrderOf r).minFac) : MvPowerSeries (Fin 2) R) =
      C (addOrderOf r / (addOrderOf r).minFac) (R := R) := by
      exact rfl
    have aux'' : (C (addOrderOf r / (addOrderOf r).minFac : R) * C r)
      = C (((addOrderOf r / (addOrderOf r).minFac : R) * r)) (R := R) (σ := Fin 2) := by
      simp
    rw [aux', aux'', ←map_pow, coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    refine Finsupp.ne_iff.mpr ?_
    use 1
    simp
    by_contra hc
    obtain hc' := Nat.minFac_eq_one_iff.mp (Eq.symm hc)
    simp at hc'
    contradiction
  assoc := by
    simp only
    rw [show addOrderOf r = n by rfl, show (n / p) • r = b by rfl, show nilpotencyClass b = m by rfl,
      show n.minFac = p by rfl, show b ^ (m - 1) = c by rfl]
    obtain has_subst₁ := has_subst_aux₁ (X₀ + X₁ + c • X₀ * X₁ ^ p) (R := R) (by simp)
    obtain has_subst₂ := has_subst_aux₂ (X₀ + X₁ + c • (X₀ * X₁ ^ p)) (R := R)  (by simp)
    rw [←smul_eq_C_mul, subst_add has_subst₁, subst_add has_subst₁, subst_mul has_subst₁, subst_X has_subst₁,
      subst_X has_subst₁, subst_smul has_subst₁, subst_X has_subst₁,
      subst_pow has_subst₁, subst_X has_subst₁]
    simp
    simp [subst_add has_subst_XY, subst_smul has_subst_XY, subst_mul has_subst_XY,
      subst_pow has_subst_XY, subst_X has_subst_XY]
    simp_rw [subst_add has_subst₂, subst_smul has_subst₂, subst_mul has_subst₂,
      subst_pow has_subst₂, subst_X has_subst₂, subst_add has_subst_YZ,
      subst_smul has_subst_YZ, subst_mul has_subst_YZ, subst_pow has_subst_YZ,
      subst_X has_subst_YZ]
    have pPrime : p.Prime := Nat.minFac_prime_iff.mpr ngtone
    have mgetwo : m ≥ 2 := by
      obtain mneq₀ := pos_nilpotencyClass_iff.mpr bNil
      have mneq₁ : m ≠ 1 := by
        by_contra hc
        obtain hc' := nilpotencyClass_eq_one.mp hc
        contradiction
      omega
    have cpow_aux : c ^ 2 = 0 := by
      rw [show c = b ^ (m - 1) by rfl, ←pow_mul]
      have bNil' : b ^ m = 0 := pow_nilpotencyClass bNil
      have le_aux : m ≤ (m - 1) * 2 := by omega
      exact pow_eq_zero_of_le le_aux bNil'
    have aux : (C c (σ := Fin 3)) ^ 2  = 0 := by
      simp [←map_pow, cpow_aux]
    have cpow_zero : c ^ p = 0 := by
      exact pow_eq_zero_of_le (Nat.Prime.two_le pPrime) cpow_aux
    have cTor : p * c = 0 := by
      have aux' : p * b = 0 := by
        simp [show b = (n / p) • r by rfl, ←mul_assoc]
        have : (p : R) * ↑(n / p) = n := by
          norm_cast
          congr
          exact Nat.mul_div_cancel' (Nat.minFac_dvd n)
        obtain h₁ := addOrderOf_nsmul_eq_zero r
        simp at h₁
        rw [this, h₁]
      have add_aux : m - 1 = 1 + (m - 2) := by
        omega
      rw [show c = b ^ (m - 1) by rfl, add_aux, pow_add]
      ring_nf
      simp [aux']
    have eq_aux₁ : c • ((Y₀ + Y₁ + c • (Y₀ * Y₁ ^ p)) * Y₂ ^ p) =
      c • Y₀ * (Y₂ (R := R)) ^ p + c • Y₁ * Y₂ ^ p := by
      simp [smul_eq_C_mul]
      ring_nf
      simp [aux]
    have eq_aux₂ : c • (Y₀ * (Y₁ + Y₂ + c • (Y₁ * Y₂ ^ p)) ^ p) =
      c • Y₀ * (Y₁ (R := R)) ^ p + c • Y₀ * Y₂ ^ p := by
      simp [smul_eq_C_mul]
      ring_nf
      have C_mul_p_aux : C c * (p : MvPowerSeries (Fin 3) R) =
        C (p * c) := by
        simp [mul_comm]
      have eq_aux : (C c * (Y₁ (R := R)) * Y₂ ^ p + Y₁ + Y₂) ^ p =
        ∑ m ∈ Finset.range (p + 1), Y₁ ^ m * Y₂ ^ (p - m)
        * (p.choose m : MvPowerSeries (Fin 3) R) := by
        rw [add_pow, Finset.sum_congr rfl]
        intro i hi
        simp at hi
        by_cases hi_zero : i = 0
        · simp [hi_zero]
        by_cases hip : i = p
        · simp [hip]
          rw [add_pow, Finset.sum_eq_single 0]
          · simp
          · intro j hj₁ hj₂
            by_cases hjp : j = p
            · simp [hjp]
              rw [mul_pow, mul_pow, ←map_pow]
              simp [cpow_zero]
            simp at hj₁
            have pdvd : p ∣ p.choose j := Nat.Prime.dvd_choose_self pPrime (by omega) (by omega)
            obtain ⟨t, ht⟩ := pdvd
            rw [ht, show j = 1 + (j - 1) by omega, pow_add]
            simp
            calc
              _ = Y₁ * Y₂ ^ p * (C c * Y₁ * Y₂ ^ p) ^ (j - 1)
                * Y₁ ^ (p - (1 + (j - 1))) * (C c * ↑p * ↑t) := by
                ring
              _ = 0 := by
                simp [C_mul_p_aux, cTor]
          simp
        have pdvd : p ∣ p.choose i := Nat.Prime.dvd_choose_self pPrime hi_zero (by omega)
        obtain ⟨j, hj⟩ := pdvd
        rw [add_pow, Finset.sum_mul, Finset.sum_mul, Finset.sum_eq_single 0]
        · simp
        · intro b hb₁ hb₂
          nth_rw 1 [show b = b - 1 + 1 by omega]
          rw [hj, pow_add]
          calc
            _ = (C c * Y₁ * Y₂ ^ p) ^ (b - 1) * (Y₁ * Y₂ ^ p) * Y₁ ^ (i - b)
              * ↑(i.choose b) * Y₂ ^ (p - i) * ↑(C c * p * j) := by
              simp
              ring
            _ = 0 := by
              simp [C_mul_p_aux, cTor]
        · simp
      have pneq₀ : 0 ≠ p :=
          Ne.symm (Nat.Prime.ne_zero (Nat.minFac_prime_iff.mpr ngtone))

      rw [eq_aux, Finset.mul_sum, Finset.sum_eq_add_of_mem 0 p (by simp) (by simp) pneq₀]
      · simp
        ring
      · intro i hi₁ ⟨hi₂, hi₃⟩
        simp at hi₁
        have pdvd : p ∣ p.choose i := Nat.Prime.dvd_choose_self pPrime (by omega) (by omega)
        obtain ⟨t, ht⟩ := pdvd
        rw [ht]
        calc
          _ = (Y₀ (R := R)) * (Y₁ ^ i * Y₂ ^ (p - i) *
            ((C c (R := R)) * (p : MvPowerSeries (Fin 3) R))) * ↑t := by
            simp
            ring
          _ = 0 := by
            simp [C_mul_p_aux, cTor]
    simp
    simp_rw [eq_aux₁, eq_aux₂, smul_eq_C_mul]
    ring_nf
  }


/-- Given a coefficient ring `R`, if for any formal group law `F` over `R` is commutative,
  then this ring does not have a nonzero element is nilpotent and `ℤ`-torsion at the same time. -/
theorem no_nonzero_torsion_nilpotent_of_comm :
  (∀ (F : FormalGroup R), F.comm) →  ¬ (∃ r : R, IsNilpotent r ∧ addOrderOf r ≠ 0 ∧ r ≠ 0) := by
  contrapose
  intro h
  simp at h
  obtain ⟨r, rNil, rTor, rNeq⟩ := h
  simp
  use (counter_example_F r rNil rTor rNeq)
  intro hc
  let n := addOrderOf r
  have ngtone : n ≠ 1 := by
    by_contra hn; simp [n] at hn; contradiction
  let p := Nat.minFac n
  let b := (n / p) • r
  have bNil : IsNilpotent b := IsNilpotent.smul rNil (n / p)
  let m := nilpotencyClass b
  let c := b ^ (m - 1)
  have coeff_neq : (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
    (counter_example_F r rNil rTor rNeq).toFun ≠ (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
    (subst ![X₁,X₀] (counter_example_F r rNil rTor rNeq).toFun) := by
    simp [counter_example_F, show addOrderOf r = n by rfl, show (n / p) • r = b by rfl, show nilpotencyClass b = m by rfl,
      show n.minFac = p by rfl, show b ^ (m - 1) = c by rfl]
    have eq_aux : subst ![X₁,X₀] (X₀ + X₁ + C c * X₀ * X₁ ^ p) =
      (X₁) + X₀ + C c * X₁ * X₀ ^ p := by
      simp [subst_add has_subst_swap, ←smul_eq_C_mul, subst_mul has_subst_swap,
        subst_smul has_subst_swap, subst_pow has_subst_swap, subst_X has_subst_swap]
    rw [eq_aux, coeff_X, if_neg, coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp))]
    simp
    rw [coeff_X, coeff_X, if_neg (Finsupp.ne_iff.mpr (by use 0; simp)), if_neg ]
    simp [mul_assoc]
    have eq_aux₁ : (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
      ((X₀ (R := R)) * X₁ ^ p) = 1 := by
      simp [X_pow_eq, coeff_add_mul_monomial, coeff_X]
    have eq_aux₂ : (coeff (Finsupp.single 0 1 + Finsupp.single 1 p))
      ((X₁ (R := R)) * X₀ ^ p) = 0 := by
      rw [X_pow_eq, X₁, X, monomial_mul_monomial, coeff_monomial, if_neg]
      refine Finsupp.ne_iff.mpr ?_
      use 1
      simp
      exact Nat.Prime.ne_one (Nat.minFac_prime_iff.mpr ngtone)
    simp [eq_aux₁, eq_aux₂]
    exact pow_pred_nilpotencyClass bNil
    · simp
      exact (Nat.Prime.ne_zero (Nat.minFac_prime_iff.mpr ngtone))
    · refine Finsupp.ne_iff.mpr ?_
      use 1
      simp
      refine Nat.ne_zero_iff_zero_lt.mpr (Nat.minFac_pos (addOrderOf r))
  obtain hc' := MvPowerSeries.ext_iff.mp hc (Finsupp.single 0 1 + Finsupp.single 1 p)
  contradiction



variable (R) in
/--
The canonical `ℤ`-linear map from a ring `R` to `R ⊗[ℤ] ℚ`
that sends an element `r` to `r ⊗ 1`.
-/
def canonicalMapToTensorRat : R →ₐ[ℤ] (R ⊗[ℤ] ℚ) :=
  includeLeft

/--
The kernel of the canonical map `r ↦ r ⊗ 1` from a ring `R` to `R ⊗[ℤ] ℚ`
is precisely the `ℤ`-torsion submodule of `R`.
-/
theorem kernel_canonicalMapToTensorRat_eq_torsion :
  ker (canonicalMapToTensorRat R) = torsion ℤ R := by
  refine Submodule.ext ?_
  intro x
  constructor
  · intro hx
    refine (mem_torsion_iff x).mpr ?_
    have aux : (canonicalMapToTensorRat R) x = 0 := by
      exact hx
    simp [canonicalMapToTensorRat] at aux

    sorry
  · intro hx
    simp [canonicalMapToTensorRat]
    obtain ⟨a, ha⟩ := (mem_torsion_iff x).mp hx
    calc
      _ = (a • x) ⊗ₜ (1 / (a : ℚ)) := by
        rw [smul_tmul]
        have aux : (a • (1 / (a : ℚ))) = 1 := by
          calc
            _ = a * (a : ℚ)⁻¹ := by
              aesop
            _ = 1 := by
              simp
        rw [aux]
      _ = 0 := by
        simp only [ha, one_div, zero_tmul]


lemma lem2 :
  ∀ x, x ∈ torsion ℤ R ↔ addOrderOf x ≠ 0 := by
  intro x
  constructor
  ·
    intro hx
    simp at hx
    obtain ⟨a, ha₁, ha₂⟩ := hx

    sorry
  · sorry

lemma lem1 : ringChar (Localization.Away (0 : R)) = 0 := by
  refine (CharP.ringChar_zero_iff_CharZero (Localization.Away 0)).mpr ?_
  refine charZero_of_inj_zero ?_
  intro n hn
  sorry


/-- Given a coefficient ring `R`, for any one dimensional formal group law `F(X, Y)`
  over `R`, `F(X, Y)` is commutative formal group law if and
  only if `R` does not contain a nonzero element which is both torsion and nilpotent.-/
theorem comm_iff_no_nonzero_torsion_nilpotent :
  (∀ (F : FormalGroup R), F.comm) ↔ ¬ (∃ r : R,  IsNilpotent r ∧ addOrderOf r ≠ 0 ∧ r ≠ 0) := by
  constructor
  ·  exact fun a ↦ no_nonzero_torsion_nilpotent_of_comm a
  · intro hr F
    simp at hr
    have mem_ideal : ∀ (i j : ℕ), ∀ (I : Ideal R), I.IsPrime →
      (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun) ∈ I := by
      intro i j I hI
      let f := Ideal.Quotient.mk I
      let f_F := F.map f
      obtain h₁ := comm_of_isDomain f_F
      exact (Quotient.mk_eq_zero I).mp ((comm_iff_coeff_symm' f_F).mp h₁ i j)
    have mem_nilpotent : ∀ (i j : ℕ),
      IsNilpotent (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun) :=
      fun i j => nilpotent_iff_mem_prime.mpr (mem_ideal i j)
    have mem_torsion : ∀ (i j : ℕ),
      IsOfFinAddOrder (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun)  := by
      intro i j

      sorry
    have mem_zero : ∀ (i j : ℕ),
      (coeff (coeff_two i j) F.toFun - coeff (coeff_two j i) F.toFun) = 0 :=
      fun i j => hr _ (mem_nilpotent i j) (mem_torsion i j)
    exact (comm_iff_coeff_symm' F).mpr mem_zero

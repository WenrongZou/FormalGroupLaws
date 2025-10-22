import FormalGroupLaws.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators

noncomputable section

variable {R : Type*} [CommRing R] (f g : PowerSeries R) (F : FormalGroup R)
  (φ : MvPowerSeries (Fin 2) R) (n : ℕ)


open PowerSeries FormalGroup Finset

-- abbrev addInv_map : Fin 2 → PowerSeries R
--   | ⟨0, _⟩ => PowerSeries.X
--   | ⟨1, _⟩ => f

-- abbrev addInv_aux (F : FormalGroup R) : ℕ → R × (PowerSeries R)
--   | 0 => (0, 0)
--   | 1 => (-1, -PowerSeries.X)
--   | n + 1 => (- (PowerSeries.coeff (n + 1 : ℕ) (MvPowerSeries.subst
--     (addInv_map ((addInv_aux F n).2)) F.toFun)), (addInv_aux F n ).2 + PowerSeries.C
--     (- (PowerSeries.coeff (n + 1 : ℕ) (subst (addInv_map (addInv_aux F n).2) F.toFun)))
--     * (PowerSeries.X ^ (n + 1)))

abbrev addInv_aux (F : FormalGroup R): ℕ → R
  | 0 => 0
  | 1 => -1
  | n + 1 => - (coeff (n + 1 : ℕ) (MvPowerSeries.subst
    (subst_map₂ X (∑ i : Fin (n + 1), C (addInv_aux F i.1) * X ^ i.1)) F.toFun))

/-- Given a formal group law `F` over coefficient ring `R`, there exist unique power series `ι`,
  such that `F(X, ι(X)) = 0`. -/
def addInv := mk (fun n => (addInv_aux F n))

lemma Finset.sum_range_eq_sum_fin {β : Type*} [AddCommMonoid β] {n : ℕ}  (f : ℕ → β):
  ∑ i : Fin n, f i.1 = ∑ i ∈ range n, f i := by
  rw [sum_fin_eq_sum_range, sum_congr rfl]
  intro i hi
  simp at hi
  rw [dif_pos hi]


lemma addInv_trunc_aux :
  trunc (n + 1) (addInv F) = ∑ i : Fin (n + 1), Polynomial.C (addInv_aux F i.1)
  * Polynomial.X ^ i.1
  := by
  induction n with
  | zero => simp [addInv]
  | succ k ih =>
    rw [trunc] at ⊢ ih
    simp_all
    rw [Finset.sum_range_add, ih]
    simp [sum_range_eq_sum_fin (fun i => (Polynomial.C (R := R)) (addInv_aux F i)
      * Polynomial.X ^ i)] at ⊢ ih
    rw [sum_range_add _ (k + 1) 1]
    simp [Polynomial.X_pow_eq_monomial, addInv]



lemma coeff_subst_map₂_eq_subst_subst_map₂_trunc :
  coeff n (MvPowerSeries.subst (subst_map₂ f g) φ) =
  coeff n (MvPowerSeries.subst (subst_map₂ (trunc (n + 1) f) (trunc (n + 1) g)) φ) := by

  sorry

lemma coeff_subst_addInv_trunc :
  coeff n (MvPowerSeries.subst (subst_map₂ X (addInv F)) F.toFun) =
  coeff n (MvPowerSeries.subst (subst_map₂ X (trunc (n + 1) (addInv F))) F.toFun) := by

  sorry



lemma coeff_n_aux (n : ℕ):
  coeff n (MvPowerSeries.subst (subst_map₂ X (∑ i : Fin (n + 1),
  C (addInv_aux F i.1) * X ^ i.1)) F.toFun) = 0 := by

  sorry

/- Given a formal group law `F` over coefficient ring `R`, there exist a power series
  `addInv F`, such that `F(X, (addInv F)) = 0`. -/
theorem subst_addInv_eq_zero : MvPowerSeries.subst (subst_map₂ X (addInv F)) F.toFun = 0 := by
  ext n
  simp
  rw [←(coeff_n_aux F n), coeff_subst_addInv_trunc]
  congr! 3
  unfold trunc
  simp_rw [←Polynomial.coe_C, ←Polynomial.coe_X]
  rw [sum_range_eq_sum_fin (fun i => (Polynomial.C (addInv_aux F i) : PowerSeries R)
    * (Polynomial.X).toPowerSeries ^ i), Nat.Ico_zero_eq_range,
    ←Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_finset_sum, ←Polynomial.eval₂_C_X_eq_coe,
    sum_congr rfl]
  intro i hi
  rw [Polynomial.eval₂_C_X_eq_coe]
  simp [X_pow_eq, addInv]
  rw [←monomial_zero_eq_C_apply, monomial_mul_monomial]
  simp









  -- have aux : ∑ (x : Fin (n + 1)), ((Polynomial.C (addInv_aux F ↑x)) : PowerSeries R)
  --   * ↑Polynomial.X ^ ↑x
  --   ∑ (x : Fin (n + 1)), ((Polynomial.C (addInv_aux F ↑x)) * Polynomial.X ^ ↑x : PowerSeries R) := sorry


  -- obtain (_|_|n) := n
  -- · simp [addInv]
  -- · simp [addInv, trunc, Finset.sum_range, X_eq]
  --   unfold addInv_aux
  --   simp
  -- ·
  --   simp [trunc]
  --   rw [Finset.sum_range_add]










  -- rw [← this, coeff_subst', coeff_subst']
  -- · congr! 3 with m
  --   generalize hB : (∑ i : Fin (n + 1), (C R) (substInvFun P ↑i) * X ^ i.1) = B
  --   have : X ^ (n + 1) ∣ mk (substInvFun P) - B := by
  --     rw [X_pow_dvd_iff]
  --     intro m hm
  --     simp +contextual [← hB, coeff_X_pow, Finset.sum_eq_single (⟨m, hm⟩ : Fin (n + 1)),
  --       Fin.ext_iff, @eq_comm _ m]
  --   obtain ⟨Q, hQ⟩ := this.trans (sub_dvd_pow_sub_pow _ _ m)
  --   simp [substInv, sub_eq_iff_eq_add.mp hQ, coeff_X_pow_mul']
  -- · simp [HasSubst, X, zero_pow_eq, C, substInvFun]
  -- · show IsNilpotent (mk (substInvFun P) 0)
  --   simp [HasSubst, mk, substInvFun]



-- lemma addInv_aux_zero :
--   (addInv_aux F 0) = (0, 0) := by
--   unfold addInv_aux
--   simp

-- lemma addInv_aux_one :
--   (addInv_aux F 1) = (-1, -PowerSeries.X) := by
--   unfold addInv_aux
--   simp

-- lemma addInv_aux_n (n : ℕ) (hn : n ≠ 0) :
--   (addInv_aux F (n + 1)) = (- (PowerSeries.coeff (n + 1 : ℕ) (MvPowerSeries.subst (addInv_map ((addInv_aux F n).2)) F.toFun)),
--     (addInv_aux F n ).2 + PowerSeries.C (- (PowerSeries.coeff (n + 1 : ℕ) (subst (addInv_map (addInv_aux F n).2) F.toFun))) * (PowerSeries.X ^ (n + 1))) := by
--   conv =>
--     lhs
--     unfold addInv_aux
--   simp

-- lemma addInv_aux_trunc (n : ℕ)
--   : let ι : PowerSeries R :=  PowerSeries.mk (fun n => (addInv_aux F n).1)
--   PowerSeries.trunc' n ι = (addInv_aux F n).2
--   := by sorry




-- lemma addInv_aux_trunc₁ {A : Type*} [CommRing A] (F : FormalGroup A) (n : ℕ) (hn : n ≥ 1)
--   :
--   PowerSeries.trunc'_map n (addInv_map AddInv)  = (addInv_map (addInv_aux F n).2) := by
--   unfold addInv_map
--   simp
--   funext x
--   by_cases hx : x = 0
--   unfold PowerSeries.trunc'_map
--   simp [hx]
--   unfold PowerSeries.trunc'
--   ext m
--   simp [PowerSeries.coeff_truncFun']
--   intro hm₁
--   have hm' : m > 1 := by linarith
--   rw [PowerSeries.coeff_X, if_neg]
--   linarith
--   have hx : x = 1 := by omega
--   unfold PowerSeries.trunc'_map
--   simp [hx]
--   rw [addInv_aux_trunc]

-- -- lemma trunc'_of_mk {A : Type*} [CommRing A] (f : ℕ → A) (n : ℕ) :
-- --   PowerSeries.trunc' (n + 1) (PowerSeries.mk f) = PowerSeries.trunc'
-- --   n (PowerSeries.mk f) + (Polynomial.C (f (n + 1))) * (Polynomial.X) ^ (n + 1)


-- theorem inv_exist {A : Type*} [CommRing A] {F : FormalGroup A} :
-- ∃! (ι : PowerSeries A), PowerSeries.coeff  A 1 ι = - 1 ∧
-- MvPowerSeries.subst (addInv_map ι) F.toFun  = 0 := by
--   let ι : PowerSeries A :=  PowerSeries.mk (fun n => (addInv_aux F n).1)
--   use ι
--   constructor
--   -- prove `ι` satisfies the property
--   ·
--     constructor
--     unfold ι
--     unfold addInv_aux
--     simp
--     apply PowerSeries.eq_of_forall_trunc'_eq
--     intro n
--     have hsub : SubstDomain (addInv_map ι) := by sorry
--     rw [PowerSeries.trunc'_of_subst_mv _ _ _ hsub]
--     induction n with
--     | zero =>
--       simp




--       sorry
--     | succ k ih =>
--       by_cases hk : k = 0
--       rw [hk]
--       simp

--       sorry
--       simp
--       unfold ι
--       rw [addInv_aux_trunc₁ F (k + 1) (by omega)]
--       have aux₁ : (PowerSeries.trunc' (k + 1))
--         (subst (addInv_map (addInv_aux F (k + 1)).2) F.toFun) =
--         (PowerSeries.trunc' k (subst (addInv_map (addInv_aux F (k + 1)).2) F.toFun)) + Polynomial.C (PowerSeries.coeff A (k + 1) (subst (addInv_map (addInv_aux F (k + 1)).2) F.toFun)) * Polynomial.X ^ (k + 1) := by
--           sorry
--       rw [aux₁, PowerSeries.trunc'_of_subst_mv]
--       have aux₂ : (PowerSeries.trunc'_map k (addInv_map (addInv_aux F (k + 1)).2))
--         =  (PowerSeries.trunc'_map k (addInv_map ι)) := by sorry
--       rw [aux₂, ih]
--       simp
--       have zero_aux : (PowerSeries.coeff A (k + 1))
--         (subst (addInv_map (addInv_aux F (k + 1)).2) F.toFun) = 0 := by sorry
--       rw [zero_aux]
--       simp
--       -- prove substDomain
--       refine substDomain_of_constantCoeff_zero ?_
--       intro s

--       sorry


--   -- prove the uniqueness of `ι`.
--   ·
--     sorry

import FormalGroupLaws.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators

noncomputable section

variable {R : Type*} [CommRing R] (f g : PowerSeries R) (F : FormalGroup R) {σ : Type*}
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
def addInv_X := mk (fun n => (addInv_aux F n))

lemma Finset.sum_fin_eq_sum_range' {β : Type*} [AddCommMonoid β] {n : ℕ}  (f : ℕ → β):
  ∑ i : Fin n, f i.1 = ∑ i ∈ range n, f i := by
  rw [sum_fin_eq_sum_range, sum_congr rfl]
  intro i hi
  simp at hi
  rw [dif_pos hi]

lemma HasSubst.addInv_aux : MvPowerSeries.HasSubst (subst_map₂ X (addInv_X F)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro x; fin_cases x
  · simp [subst_map₂]
  · simp [subst_map₂, addInv_X]; rfl


lemma addInv_trunc_aux :
  trunc (n + 1) (addInv_X F) = ∑ i : Fin (n + 1), Polynomial.C (addInv_aux F i.1)
  * Polynomial.X ^ i.1
  := by
  induction n with
  | zero => simp [addInv_X]
  | succ k ih =>
    rw [trunc] at ⊢ ih
    simp_all
    rw [Finset.sum_range_add, ih]
    simp [sum_fin_eq_sum_range' (fun i => (Polynomial.C (R := R)) (addInv_aux F i)
      * Polynomial.X ^ i)] at ⊢ ih
    rw [sum_range_add _ (k + 1) 1]
    simp [Polynomial.X_pow_eq_monomial, addInv_X]



lemma coeff_subst_map₂_eq_subst_subst_map₂_trunc :
  coeff n (MvPowerSeries.subst (subst_map₂ f g) φ) =
  coeff n (MvPowerSeries.subst (subst_map₂ (trunc (n + 1) f) (trunc (n + 1) g)) φ) := by

  sorry

lemma coeff_subst_addInv_trunc (hn : n ≠ 0) :
  coeff n (MvPowerSeries.subst (subst_map₂ X (addInv_X F)) F.toFun) =
  coeff n (MvPowerSeries.subst (subst_map₂ X (trunc (n + 1) (addInv_X F))) F.toFun) := by
  have trunc_X_aux : trunc (n + 1) X = Polynomial.X (R := R):= by
    refine trunc_X_of ?_
    omega
  simp [coeff_subst_map₂_eq_subst_subst_map₂_trunc, trunc_X_aux]


lemma FormalGroup.coeff_X₀_pow {k : ℕ} (hk : k ≥ 2) :
  MvPowerSeries.coeff (Finsupp.single 0 k) F.toFun = 0 := by
  sorry



lemma FormalGroup.coeff_X₁_pow {k : ℕ} (hk : k ≥ 2) :
  MvPowerSeries.coeff (Finsupp.single 1 k) F.toFun = 0 := by
  sorry



lemma coeff_n_aux (n : ℕ):
  coeff n (MvPowerSeries.subst (subst_map₂ X (∑ i : Fin (n + 1),
  C (addInv_aux F i.1) * X ^ i.1)) F.toFun) = 0 := by
  rw [sum_fin_eq_sum_range' (fun i => (C (addInv_aux F i) * X ^ i))]
  induction n with
  | zero =>
    simp
    rw [constantCoeff, MvPowerSeries.constantCoeff_subst, show (addInv_aux F 0) = 0 by rfl]
    simp [subst_map₂]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d 0 ≠ 0
    · simp [hd₀]
    by_cases hd₁ : d 1 ≠ 0
    · simp [hd₁]
    have d_eq_zero : d = 0 := by ext x; fin_cases x <;> simp_all
    simp [d_eq_zero, F.zero_constantCoeff]
    · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      intro x
      fin_cases x
      all_goals simp [subst_map₂, show (addInv_aux F 0) = 0 by rfl]
  | succ k ih =>
    by_cases hk₀ : k = 0
    ·
      simp [hk₀]

      sorry
    have has_subst₁ (m : ℕ) : MvPowerSeries.HasSubst (subst_map₂ X (∑ i ∈ range (m + 1),
      C (addInv_aux F i) * X ^ i)) := by
      refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      intro x; fin_cases x
      · simp [subst_map₂]
      · simp [subst_map₂]
        refine sum_eq_zero ?_
        intro i hi
        by_cases hi₀ : i ≠ 0
        · simp [zero_pow hi₀]
        · simp_all
          rfl
    rw [coeff, MvPowerSeries.coeff_subst (has_subst₁ (k + 1))]
    simp_rw [PowerSeries.coeff_coe]
    simp [subst_map₂]
    generalize hB : ∑ i ∈ range (k + 1), C (addInv_aux F i) * X ^ i = B
    simp [sum_range_add, hB]
    obtain has_subst' := has_subst₁ k
    rw [hB] at has_subst'
    have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) (X ^ d 0 *
      (B + C (addInv_aux F (k + 1)) * X ^ (k + 1)) ^ d 1) = (coeff (k + 1)) (X ^ d 0 * B ^ d 1)
      + if d = Finsupp.single 1 1 then (addInv_aux F (k + 1)) else 0 := by
      split_ifs with hd
      · simp [hd, ←hB, coeff_X_pow]
      sorry
    simp_rw [eq_aux, mul_add]
    rw [finsum_add_distrib]
    nth_rw 2 [finsum_eq_single _ (Finsupp.single 1 1)]
    rw [if_pos (by simp), F.lin_coeff_Y, addInv_aux,
      sum_fin_eq_sum_range' (fun i => (C (addInv_aux F i) * X ^ i)), hB, coeff, MvPowerSeries.coeff_subst has_subst']
    simp
    · simp [hk₀]
    · intro d hd
      simp [if_neg hd]
    · obtain h := MvPowerSeries.coeff_subst_finite (has_subst₁ k) F.toFun
      simp [hB, subst_map₂] at h
      exact h (Finsupp.single () (k + 1))
    · have aux : (Function.support fun d ↦
        (MvPowerSeries.coeff d) F.toFun * if d = Finsupp.single 1 1 then addInv_aux F (k + 1) else 0)
        ⊆ {Finsupp.single 1 1} := by
        refine Function.support_subset_iff'.mpr ?_
        intro d hd
        simp at hd
        simp [if_neg hd]
      exact Set.Finite.subset (Set.finite_singleton (Finsupp.single 1 1)) aux




    -- have eq_aux {d : Fin 2 →₀ ℕ} : (coeff (k + 1)) (X ^ d 0 *
    --   (B + C (addInv_aux F (k + 1)) * X ^ (k + 1)) ^ d 1) = if d = Finsupp.single 1 1
    --   then (coeff (k + 1)) (X ^ d 0 * B ^ d 1) + (addInv_aux F (k + 1)) else (coeff (k + 1)) (X ^ d 0 * B ^ d 1) := by
    --   split_ifs with hd
    --   · simp [hd, ←hB, coeff_X_pow]
    --   sorry
    -- sorry
    -- sorry
    -- sorry

    /- -- by_cases hd₀ : d 0 = 0
      -- · simp [hd₀]
      --   rw [add_pow, map_sum, sum_eq_single (d 1)]
      --   · simp
      --   · intro i hi₁ hi₂



      -- rw [coeff_mul, coeff_mul]
      -- simp_rw [coeff_X_pow]
      -- rw [sum_congr rfl]
      -- intro x hx

      -- by_cases hx₁ : x.1 = d 0
      -- · simp [if_pos hx₁]
      --   simp at hx
      --   rw [add_pow, map_sum, sum_eq_single (d 1)]
      --   · simp
      --   · simp
      --     intro i hi₀ hi₁
      --     rw [mul_pow, ←mul_assoc, mul_comm (B ^ i), ←map_pow, mul_assoc, mul_assoc,
      --       coeff_C_mul, ←pow_mul, ]
      --     have eq_aux : (coeff x.2) (B ^ i * (X ^ ((k + 1) * (d 1 - i)))) = 0 := by
      --       rw [coeff_mul_X_pow', if_neg]
      --       simp
      --       have d_aux : d 1 - i ≥ 1 := by
      --         omega-/


      -- by_cases hd₀ : d 1 = 0
      -- · simp [hd₀]

      -- rw [coeff_mul, coeff_mul]
      -- simp_rw [coeff_X_pow]
      -- rw [sum_congr rfl]
      -- intro x hx
      -- by_cases hx₁ : x.1 = d 0
      -- · simp [if_pos hx₁]
      --   simp at hx
      --   rw [add_pow, map_sum, sum_eq_single (d 1)]
      --   · simp
      --   · simp
      --     intro i hi₀ hi₁
      --     rw [mul_pow, ←mul_assoc, mul_comm (B ^ i), ←map_pow, mul_assoc, mul_assoc,
      --       coeff_C_mul, ←pow_mul, ]
      --     have eq_aux : (coeff x.2) (B ^ i * (X ^ ((k + 1) * (d 1 - i)))) = 0 := by
      --       rw [coeff_mul_X_pow', if_neg]
      --       simp
      --       have d_aux : d 1 - i ≥ 1 := by
      --         omega


        --     sorry

        --   rw [coeff_mul_X_pow']

        --   sorry
        -- sorry

    --   simp [if_neg hx₁]
    -- simp_rw [eq_aux]

    -- have eq_aux {d : Fin 2 →₀ ℕ} : (MvPowerSeries.coeff d) F.toFun * (coeff (k + 1)) (X ^ d 0 *
    --   (B + C (addInv_aux F (k + 1)) * X ^ (k + 1)) ^ d 1) = if d = Finsupp.single 1 1
    --   then (MvPowerSeries.coeff d) F.toFun * (addInv_aux F (k + 1)) else
    --   (MvPowerSeries.coeff d) F.toFun * (coeff (k + 1)) (X ^ d 0 * B ^ d 1) := by
    --   split_ifs with hd₁
    --   · simp [hd₁, ←hB, coeff_X_pow]
    --   ·
    --     sorry


/- Given a formal group law `F` over coefficient ring `R`, there exist a power series
  `addInv F`, such that `F(X, (addInv F)) = 0`. -/
theorem subst_addInv_eq_zero : MvPowerSeries.subst (subst_map₂ X (addInv_X F)) F.toFun = 0 := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
    rw [constantCoeff, MvPowerSeries.constantCoeff_subst (HasSubst.addInv_aux _)]
    simp
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd₀ : d 0 ≠ 0
    · have eq_aux : constantCoeff (subst_map₂ X (addInv_X F) 0) = 0 := by
        simp [subst_map₂]
      simp [eq_aux, zero_pow hd₀]
    by_cases hd₁ : d 1 ≠ 0
    · have eq_aux : constantCoeff (subst_map₂ X (addInv_X F) 1) = 0 := by
        simp [subst_map₂, addInv_X]; rfl
      simp [eq_aux, zero_pow hd₁]
    simp_all
    have d_eq_zero : d = 0 := by
      ext x
      fin_cases x; all_goals simp [hd₀, hd₁]
    simp [d_eq_zero, F.zero_constantCoeff]
  simp
  rw [←(coeff_n_aux F n), coeff_subst_addInv_trunc _ _ hn]
  congr! 3
  unfold trunc
  simp_rw [←Polynomial.coe_C, ←Polynomial.coe_X]
  rw [sum_fin_eq_sum_range' (fun i => (Polynomial.C (addInv_aux F i) : PowerSeries R)
    * (Polynomial.X).toPowerSeries ^ i), Nat.Ico_zero_eq_range,
    ←Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_finset_sum, ←Polynomial.eval₂_C_X_eq_coe,
    sum_congr rfl]
  intro i hi
  rw [Polynomial.eval₂_C_X_eq_coe]
  simp [X_pow_eq, addInv_X]
  rw [←monomial_zero_eq_C_apply, monomial_mul_monomial]
  simp

-- /-- `-[F] f` means `FormalGroup.addInv F f`. -/
-- scoped[FormalGroup] notation:65 " -[" F:0 "] " f:66 =>
--   subst f addInv F

def addInv (F : FormalGroup R) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  subst f (addInv_X F)


/-- Given any formal group law `F`, `X + [F] addInv (X) = 0`. -/
theorem FormalGroup.X_add_addInv_X_eq_zero : X +[F] addInv_X (F) = 0 := by
  simp [add, subst_addInv_eq_zero]










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

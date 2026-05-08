module

-- import Mathlib.RingTheory.PowerSeries.Substitution
-- import Mathlib.RingTheory.PowerSeries.Trunc
-- import FormalGroupLaws.Basic
-- import FormalGroupLaws.LubinTateTheory.ConstructiveLem

-- open ValuativeRel MvPowerSeries Classical FormalGroup

-- universe u

-- -- TODO : use homogeneousComponent to define truncation of total degree

-- variable {K : Type u} [Field K] [ValuativeRel K] [UniformSpace K]
--   (π : 𝒪[K]) {R : Type*} [CommRing R]

-- variable {σ : Type*} {R : Type*} [CommRing R] {τ : Type*}  [IsNonarchimedeanLocalField K]

-- variable [DecidableEq σ] [Fintype σ] [DecidableEq τ] [Fintype τ]

-- noncomputable section

-- open LubinTateF

-- /-- This is a special case from the constructive lemma, namely for `f, g` in the class
--   `LubinTateF` and forall element `a : 𝒪[K]` there is a PowerSeries `ϕ`, such that
--   truncation of `ϕ` of degree 2 is `a * X`, and `g ∘ ϕ = ϕ ∘ f`-/
-- theorem constructive_lemma_poly
--   (f g : LubinTateF π) (a : 𝒪[K]) :
--   ∃! (ϕ : PowerSeries 𝒪[K]), (PowerSeries.trunc 2 ϕ)
--   = Polynomial.C a * Polynomial.X  ∧
--   PowerSeries.subst ϕ g.toPowerSeries = PowerSeries.subst f.toPowerSeries ϕ := by
--   let a := fun (x : Fin 2) => 1

--   sorry

-- /-- Given `g` a multi variate power series with two variables, `g (X, Y) ≡ g₂ (X, Y) mod (deg 2)`
--   as a multi variate power series with two variables, then `g (X, Y) ≡ g₂ (X, Y) mod (deg 2)`
--   as a multi variate power series with three variables, where `X, Y` is first two variables.-/
-- lemma truncTotalDegHom_of_subst' (g : MvPowerSeries (Fin 2) R) (hg : constantCoeff g = 0) :
--   truncTotalDegHom 2 (subst ![Y₀, Y₁] g) =
--   truncTotalDegHom 2 (subst ![Y₀, Y₁ (R := R)] (truncTotalDegHom 2 g) (R := R)) := by

--   sorry

-- /-- Given `g` a multi variate power series with two variables, `g (X, Y) ≡ g₂ (X, Y) mod (deg 2)`
--   as a multi variate power series with two variables, then `g (Y, Z) ≡ g₂ (Y, Z) mod (deg 2)`
--   as a multi variate power series with three variables, where `Y, Z` is last two variables.-/
-- lemma truncTotalDegHom_of_subst₂' (g : MvPowerSeries (Fin 2) R) (hg : constantCoeff g = 0):
--   truncTotalDegHom 2 (subst ![Y₁, Y₂] g) =
--   truncTotalDegHom 2 (subst ![Y₁, Y₂ (R := R)] (truncTotalDegHom 2 g) (R := R) ):= by
--   sorry

-- /-- Given `f, g` to be multi variate power series with two variable, let
--   `f₂(X, Y) ≡ f(X,Y) mod (deg 2)`, and the constant coefficient of `g` is zero,
--   then `f (g (X, Y), Z) ≡ f₂ (g (X, Y), Z) mod (deg 2)` -/
-- lemma truncTotalDegHom_of_subst (f g : MvPowerSeries (Fin 2) R) (hg : constantCoeff g = 0) :
--   truncTotalDegHom 2 (subst ![subst ![Y₀, Y₁] g, Y₂] f) =
--   truncTotalDegHom 2 (subst ![subst ![Y₀, Y₁] g, Y₂ (R := R)] (truncTotalDegHom 2 f) (R := R)) := by
--   sorry

-- /-- Given `f, g` to be multi variate power series with two variable, let
--   `f₂(X, Y) ≡ f(X,Y) mod (deg 2)`, and the constant coefficient of `g` is zero,
--   then `f (X, g (Y, Z)) ≡ f₂ (X, g (Y, Z)) mod (deg 2)` -/
-- lemma truncTotalDegHom_of_subst₂ (f g : MvPowerSeries (Fin 2) R) (hg : constantCoeff g = 0) :
--   truncTotalDegHom 2 (subst ![Y₀, subst ![Y₁, Y₂] g] f) =
--   truncTotalDegHom 2 (subst ![Y₀, subst ![Y₁, Y₂ (R := R)] g] (truncTotalDegHom 2 f) (R := R)) := by
--   sorry

-- theorem MvPowerSeries.truncTotalDeg.PowerSeries_subst_n (f : MvPowerSeries σ R) (g : PowerSeries R) (n : ℕ)
--   (hf : constantCoeff f = 0) : truncTotalDeg n (PowerSeries.subst f g) =
--   truncTotalDeg n (PowerSeries.subst f (PowerSeries.trunc n g).toPowerSeries) := by

--   sorry

-- theorem MvPowerSeries.truncTotalDeg.MvPowerSeries_subst_two
--   (f : σ → MvPowerSeries τ R) (g : MvPowerSeries σ R)
--   (hf : ∀ (x : σ), constantCoeff (f x) = 0) : truncTotalDeg 2 (subst f g) =
--   truncTotalDeg 2 (subst f (truncTotalDeg 2 g).toMvPowerSeries) := by sorry



-- lemma eq_single_of_sum_equal_one [Nonempty σ] {x : σ →₀ ℕ} (h : Finset.univ.sum x = 1) :
--   ∃ i : σ, x = Finsupp.single i 1 := by
--   let x_supp := x.support
--   have hx_zero : x ≠ 0 := by
--     by_contra hc
--     have sum_aux : Finset.univ.sum x = 0 := by
--       refine Fintype.sum_eq_zero ⇑x ?_
--       simp [hc]
--     linarith
--   have exist_aux : ∃ i, i ∈ x.support := by
--     refine Finset.Nonempty.exists_mem ?_
--     exact Finsupp.support_nonempty_iff.mpr hx_zero
--   obtain ⟨i, hi⟩ := exist_aux
--   have xi_ge : x i ≥ 1 := by
--     have aux : x i ≠ 0 := by
--       simp at hi
--       exact hi
--     omega
--   use i
--   refine Finsupp.eq_single_iff.mpr ?_
--   constructor
--   by_contra hc₁
--   have exist_aux' : ∃ j, j ∈ x.support ∧ j ≠ i := by
--     have nonempty_aux : (x.support \ {i}).Nonempty := by
--       exact Finset.sdiff_nonempty.mpr hc₁
--     obtain ⟨j, hj⟩ := nonempty_aux
--     use j
--     simp at hj
--     simp [hj]
--   obtain ⟨j, hj⟩ := exist_aux'
--   have xj_ge : x j ≥ 1 := by
--     have aux : x j ≠ 0 := by
--       simp at hj
--       exact hj.1
--     omega
--   have hc_aux : Finset.univ.sum ⇑x ≥ 2 := by
--     calc
--       _ = (Finset.univ.erase i).sum x + x i := by
--         exact Eq.symm (Finset.sum_erase_add Finset.univ ⇑x (by simp))
--       _ = ((Finset.univ.erase i).erase j).sum x + x j + x i := by
--         congr
--         refine Eq.symm (Finset.sum_erase_add (Finset.univ.erase i) ⇑x ?_)
--         exact Finset.mem_erase_of_ne_of_mem hj.2 (by simp)
--       _ ≥ x j + x i := by
--         have aux : ((Finset.univ.erase i).erase j).sum x ≥ 0 := by
--           exact Nat.zero_le (((Finset.univ.erase i).erase j).sum ⇑x)
--         omega
--       _ ≥ 2 := by
--         linarith
--   linarith
--   --
--   by_contra hc₁
--   have xi_pos : x i ≥ 2 := by
--     omega
--   have hc_aux : Finset.univ.sum ⇑x ≥ 2 := by
--     calc
--       _ = (Finset.univ.erase i).sum x + x i := by
--         exact Eq.symm (Finset.sum_erase_add Finset.univ ⇑x (by simp))
--       _ ≥ 2 := by
--         rw [show 2 = 0 + 2 by norm_num]
--         exact Nat.le_add_left_of_le xi_pos
--   linarith


-- /-- For any Multi-variable PowerSeries `f`, assume `d ≥ 1` , then constant coefficient of  truncation of
--   total degree `d` of `f` is equal to `f` -/
-- theorem constantCoeff_of_truncTotalDeg_ge_one (f : MvPowerSeries σ R) {d : ℕ} (hd : d ≥ 1):
--   constantCoeff f = MvPolynomial.constantCoeff (truncTotalDegHom d f) := by
--   simp [truncTotalDegHom, truncTotalDeg_eq, MvPolynomial.constantCoeff]
--   simp_rw [coeff_truncTotalDegEq]
--   rw [show constantCoeff f = (coeff 0) f by simp]
--   apply Eq.symm
--   rw [Finset.sum_eq_single 0]
--   simp
--   · intro x hx₁ hx₂
--     simp
--     intro hc
--     by_contra
--     exact hx₂ (Eq.symm hc)
--   · intro hx
--     simp
--     have hc : 0 ∈ Finset.range d := by
--       simp
--       linarith
--     exfalso
--     contradiction


-- theorem PowerSeries.trunc_of_subst_trunc (f : MvPowerSeries σ R) (map : σ → PowerSeries R)
--   (h_map : ∀ (x : σ), PowerSeries.constantCoeff (map x) = 0) [Nonempty σ] :
--   PowerSeries.trunc 2 (MvPowerSeries.subst map f) = PowerSeries.trunc 2 (MvPowerSeries.subst map
--   (truncTotalDeg 2 f).toMvPowerSeries) := by
--   ext d
--   by_cases hd : d < 2
--   ·
--     interval_cases d
--     /- the case `d = 0`-/
--     · simp [coeff_trunc]
--       rw [←coeff_zero_eq_constantCoeff, PowerSeries.coeff, MvPowerSeries.coeff_subst
--         (hasSubst_of_constantCoeff_zero h_map),
--         MvPowerSeries.coeff_subst (hasSubst_of_constantCoeff_zero h_map)]
--       simp
--       simp_rw [h_map]
--       have aux₁ : ∑ᶠ (d : σ →₀ ℕ), (MvPowerSeries.coeff d) f * ∏ x, 0 ^ d x
--         = MvPowerSeries.coeff 0 f * ∏ x, 0 ^ (0 : σ →₀ ℕ) x := by
--         apply finsum_eq_single
--         intro n hn
--         -- Nonempty σ
--         have exist_neq : ∃ x : σ, n x ≠ 0 := by
--           refine Decidable.not_forall.mp ?_
--           by_contra hc
--           have neq_zero : n = 0 := by
--             exact Finsupp.ext hc
--           contradiction
--         obtain ⟨x, hx⟩ := exist_neq
--         have zero_aux : ∏ x, (0 : R) ^ n x = 0 := by
--           have zero_pow_aux : (0 : R) ^ n x = 0 := by
--             exact zero_pow hx
--           have exist_zero : ∃ x : σ, (0 : R) ^ n x = 0 := by
--             use x
--           apply Finset.prod_eq_zero (i := x)
--           simp
--           exact zero_pow_aux
--         simp [zero_aux]
--       have aux₂ : ∑ᶠ (d : σ →₀ ℕ), MvPolynomial.coeff d (truncTotalDeg 2 f) * ∏ x, 0 ^ d x
--         = MvPolynomial.coeff 0 (truncTotalDeg 2 f) * ∏ x, 0 ^ (0 : σ →₀ ℕ) x := by
--         apply finsum_eq_single
--         intro n hn
--         -- Nonempty σ
--         have exist_neq : ∃ x : σ, n x ≠ 0 := by
--           refine Decidable.not_forall.mp ?_
--           by_contra hc
--           have neq_zero : n = 0 := by
--             exact Finsupp.ext hc
--           contradiction
--         obtain ⟨x, hx⟩ := exist_neq
--         have zero_aux : ∏ x, (0 : R) ^ n x = 0 := by
--           have zero_pow_aux : (0 : R) ^ n x = 0 := by
--             exact zero_pow hx
--           have exist_zero : ∃ x : σ, (0 : R) ^ n x = 0 := by
--             use x
--           apply Finset.prod_eq_zero (i := x)
--           simp
--           exact zero_pow_aux
--         simp [zero_aux]
--       simp [aux₁, aux₂, constantCoeff_of_truncTotalDeg_ge_one _ (show 2 ≥ 1 by norm_num),
--         truncTotalDegHom]
--       rfl
--     -- the case d = 1
--     obtain has_subst₁ :=  hasSubst_of_constantCoeff_zero h_map
--     rw [PowerSeries.coeff_trunc, if_pos (by norm_num), coeff, MvPowerSeries.coeff_subst has_subst₁,
--       PowerSeries.coeff_trunc, if_pos (by norm_num), coeff, MvPowerSeries.coeff_subst has_subst₁]
--     simp
--     let sum_fun := fun (d : σ →₀ ℕ) => (MvPowerSeries.coeff d) f * (coeff 1) (∏ a, map a ^ d a)
--     apply finsum_congr
--     intro x
--     by_cases hx_zero : x = 0
--     · simp [hx_zero]
--     by_cases hx : ∃ i : σ, x = Finsupp.single i 1
--     · obtain ⟨i, hi⟩ := hx
--       have eq_aux : (MvPowerSeries.coeff x) f = MvPolynomial.coeff x (truncTotalDeg 2 f) := by
--         rw [hi, coeff_truncTotalDeg, if_pos (by simp)]
--       rw [eq_aux]
--     have sum_ge_two : 2 ≤ Finset.univ.sum ⇑x := by
--       refine (Nat.two_le_iff (Finset.univ.sum ⇑x)).mpr ?_
--       refine And.symm ((fun {p q} ↦ not_or.mp) ?_)
--       intro hc
--       obtain hc | hc := hc
--       obtain hc' := eq_single_of_sum_equal_one hc
--       contradiction
--       have xeq : x = 0 := by
--         refine Finsupp.support_eq_empty.mp ?_
--         by_contra hc₁
--         have pos_aux : Finset.univ.sum ⇑x > 0 := by
--           have aux₁ : ∃ i, i ∈ x.support := by
--             refine Finset.Nonempty.exists_mem ?_
--             exact Finsupp.support_nonempty_iff.mpr hx_zero
--           obtain ⟨j, hj⟩ := aux₁
--           refine Finset.sum_pos' ?_ ?_
--           · intro i
--             norm_num
--           · use j
--             simp
--             simp at hj
--             omega
--         linarith
--       contradiction
--     have eq_aux₁ : (MvPowerSeries.coeff x) f * (coeff 1) (∏ a, map a ^ x a) = 0 := by
--       have aux : (coeff 1) (∏ a, map a ^ x a) = 0 := by
--         rw [coeff_prod]
--         refine Finset.sum_eq_zero ?_
--         intro l hl
--         simp at hl
--         have exist_aux : ∃ i, (coeff (l i)) (map i ^ x i) = 0 := by
--           obtain hl' := eq_single_of_sum_equal_one hl
--           obtain ⟨i, hi⟩ := hl'
--           have hi' : ∀ j : σ, j ≠ i → l j = 0 := by sorry

--           sorry
--         obtain ⟨i, hi⟩ := exist_aux
--         refine Finset.prod_eq_zero (by simp) hi
--       simp [aux]
--     rw [eq_aux₁, coeff_truncTotalDeg, if_neg (by simp [sum_ge_two])]
--     simp
--   simp [coeff_trunc, if_neg hd]


-- theorem PowerSeries.trunc_of_subst_trunc' (f : PowerSeries R) (g : PowerSeries R)
--   (h : PowerSeries.constantCoeff g = 0) :
--   trunc 2 (subst g f) = PowerSeries.trunc 2 (subst g (trunc 2 f).toPowerSeries) := by
--   sorry


-- /-- truncation of total degree `2` of multi variate power series `X (x : σ)` is `X (x : σ)`. -/
-- theorem truncTotalDegTwo.X {x : σ}  :
--   (truncTotalDeg 2 (X x)).toMvPowerSeries = X x (R := R) := by
--   ext d
--   simp [truncTotalDeg_eq, MvPolynomial.coeff_sum, coeff_truncTotalDegEq, coeff_X]
--   by_cases hd : d = Finsupp.single x 1
--   all_goals simp [hd]


-- /-- Given a formal group law `F (X, Y)` over ring `R`, `F (X, Y)≅ X + Y (mod deg 2)` -/
-- theorem FormalGroup.truncTotalDegTwo (F : FormalGroup R) :
--   ((truncTotalDegHom 2) F.toPowerSeries) = MvPolynomial.X 0 + MvPolynomial.X 1 := by
--   ext d
--   simp [truncTotalDegHom, truncTotalDeg_eq, MvPolynomial.coeff_sum, coeff_truncTotalDegEq]
--   by_cases hd : d = Finsupp.single 0 1
--   · simp [hd, F.lin_coeff_X]
--   · by_cases hd₁ : d = Finsupp.single 1 1
--     · simp [hd₁, F.lin_coeff_Y]
--     · simp [MvPolynomial.coeff_X', if_neg (Ne.symm hd), if_neg (Ne.symm hd₁)]
--       by_cases hd₂ : d = 0
--       · simp [hd₂, F.zero_constantCoeff]
--       · intro h
--         have heq : d 0 + d 1 = d 1 + d 0 := by ring_nf
--         interval_cases (d 0 + d 1)
--         · have d₀eq : d 0 = 0 := by linarith
--           have d₁eq : d 1 = 0 := by linarith
--           have deq_zero : d = 0 := by
--             ext x
--             fin_cases x
--             all_goals simp [d₀eq, d₁eq]
--           contradiction
--         · have d₁eq : (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by
--             omega
--           obtain deq | deq := d₁eq
--           · have hc : d = Finsupp.single 0 1 := by
--               ext x
--               fin_cases x
--               all_goals simp [deq]
--             contradiction
--           · have hc : d = Finsupp.single 1 1 := by
--               ext x
--               fin_cases x
--               all_goals simp [deq]
--             contradiction

-- /-- Given a multi variate power series `f` and an element `a ∈ R`, let  `fₙ ≡ f mod (deg n)`
--   then `a • f ≡ a • fₙ mod (deg n)`. -/
-- theorem truncTotalDeg_smul (f : MvPowerSeries σ R) {a : R} {n : ℕ} : truncTotalDeg n (a • f)
--   = a • truncTotalDeg n f := by
--   ext m
--   simp [coeff_truncTotalDeg]

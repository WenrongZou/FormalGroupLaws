import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution
import FormalGroupLaws.Basic
import FormalGroupLaws.SubstInv


noncomputable section

open MvPowerSeries Classical FormalGroup

variable {R : Type*} [CommRing R] {σ : Type*}

theorem PowerSeries.constantCoeff_def (f : PowerSeries R) :
    PowerSeries.constantCoeff f = MvPowerSeries.constantCoeff f := rfl

lemma subst_self (f : MvPowerSeries (Fin 2) R):
  f =
  MvPowerSeries.subst
    (fun x ↦
      match x with
      | ⟨0, _⟩ => X₀
      | ⟨1, _⟩ => X₁)
    f := by
  have eq_aux : MvPowerSeries.X = (fun (x : Fin 2) ↦
      match x with
      | ⟨0, isLt⟩ => X₀
      | ⟨1, isLt⟩ => X₁ (R := R)) := by
    funext x
    by_cases hx : x = 0
    simp [hx]
    have hx' : x = 1 := by omega
    simp [hx']
  rw [←eq_aux]
  simp [←map_algebraMap_eq_subst_X f]


-- need some theorem like associativity of substitution
theorem subst_assoc (f g: PowerSeries  R)
  (h : MvPowerSeries σ R) (hg : PowerSeries.HasSubst g) (hh : PowerSeries.HasSubst h) :
  PowerSeries.subst (PowerSeries.subst h g) f
    = PowerSeries.subst h (PowerSeries.subst g f) := by
  simp [←PowerSeries.subst_comp_subst hg hh]

lemma substDomain_aux {g : PowerSeries R} (hb3 : (PowerSeries.constantCoeff) g = 0)
    (G₁ : FormalGroup R) : PowerSeries.HasSubst (subst (g.toMvPowerSeries ·) G₁.toFun) := by
  refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
  rw [constantCoeff_subst]
  simp
  have eq_zero_aux : ∀ (d : Fin 2 →₀ ℕ), (coeff d) G₁.toFun *
      (constantCoeff (PowerSeries.subst (X (0 : Fin 2) (R := R)) g (S := R)) ^ d 0 *
    constantCoeff (PowerSeries.subst (X (1 : Fin 2)) g) ^ d 1) =
    0 := by
    intro d
    by_cases hd : d = 0
    · simp [hd, G₁.zero_constantCoeff]
    · by_cases hd₀ : d 0 ≠ 0
      · have zero_aux : constantCoeff (PowerSeries.subst (X (0 : Fin 2) (R := R)) g (S := R)) ^ d 0 = 0 := by
          rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.X 0)]
          have zero_aux' : ∑ᶠ (d : ℕ), (PowerSeries.coeff d) g • constantCoeff ((X (0 : Fin 2) (R := R)) ^ d) = 0 := by
            conv =>
              rhs
              rw [←finsum_zero (α := ℕ)]
            congr
            funext n
            simp
            by_cases hn : n = 0
            simp [hn, hb3]
            simp [hn]
          rw [zero_aux']
          exact (zero_pow hd₀)
        simp [zero_aux]
      ·
        have hd₁ : d 1 ≠ 0 := by
          by_contra h'
          simp at hd₀
          apply hd
          refine Eq.symm (Finsupp.ext ?_)
          intro a
          by_cases ha : a = 0
          simp [ha, hd₀]
          have ha' : a = 1 := by omega
          simp [ha', h']
        have zero_aux : constantCoeff (PowerSeries.subst (X (1 : Fin 2) (R := R)) g) ^ d 1 = 0 := by
          rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.X 1)]
          have zero_aux' : ∑ᶠ (d : ℕ), (PowerSeries.coeff d) g • constantCoeff ((X (1 : Fin 2) (R := R)) ^ d) = 0 := by
            conv =>
              rhs
              rw [←finsum_zero (α := ℕ)]
            congr
            funext n
            simp
            by_cases hn : n = 0
            simp [hn, hb3]
            simp [hn]
          rw [zero_aux']
          exact (zero_pow hd₁)
        simp [zero_aux]
  simp_rw [PowerSeries.toMvPowerSeries_apply, finsum_eq_zero_of_forall_eq_zero eq_zero_aux]
  refine hasSubst_of_constantCoeff_zero ?_
  intro x
  by_cases hx : x = 0
  simp [hx]
  have const_zero : (constantCoeff (PowerSeries.subst (X (0 : Fin 2) (R := R)) g)) = 0 := by
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.X 0)]
    simp
    conv =>
      rhs
      rw [←finsum_zero (α := ℕ)]
    congr
    funext d
    by_cases hd : d = 0
    simp [hd, hb3]
    simp [hd]
  rw [g.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _ hb3]
  rw [g.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _ hb3]

lemma isIso_iff_substDomain_aux {A : Type*} [CommRing A] {g : PowerSeries A}
  (hb3 : (PowerSeries.constantCoeff) g = 0)
  : HasSubst (g.toMvPowerSeries · (σ := Fin 2))  := by
  -- apply substDomain_of_constantCoeff_nilpotent
  refine hasSubst_of_constantCoeff_zero ?_
  -- do as a lemma every x : Fin 2 coeff is zero
  intro x
  by_cases hx : x = 0
  · rw [hx]
    have zero_aux : (constantCoeff (g.toMvPowerSeries (0 : Fin 2))) = 0 := by
      rw [g.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero
        (constantCoeff_X _) _ hb3]
    simp [zero_aux]
  · have hx' : x = 1 := by omega
    rw [hx']
    have zero_aux : ((constantCoeff) (g.toMvPowerSeries (1 : Fin 2))) = 0 := by
      rw [g.toMvPowerSeries_apply, PowerSeries.constantCoeff_subst_eq_zero
        (constantCoeff_X _) _ hb3]
    simp [zero_aux]


lemma isIso_iff_aux {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A}
  (α : FormalGroupHom G₁ G₂)  {g : PowerSeries A}
  (hb3 : (PowerSeries.constantCoeff) g = 0):
  MvPowerSeries.subst (PowerSeries.toMvPowerSeries · (PowerSeries.subst g α.toFun)) G₂.toFun =
  PowerSeries.subst (subst (g.toMvPowerSeries · ) G₁.toFun) α.toFun := by
  obtain h1 := α.hom
  have eq_aux : subst (g.toMvPowerSeries · ) (PowerSeries.subst G₁.toFun α.toFun)
    = subst (g.toMvPowerSeries · ) (subst (α.toFun.toMvPowerSeries ·)  G₂.toFun) := by
    rw [h1]
  -- rw [←subst_comp_subst (b := (sub_hom₂ g))] at eq_aux
  unfold PowerSeries.subst
  -- α (F (β (X), β(Y)))
  have eq_aux1 : subst (g.toMvPowerSeries · ) (PowerSeries.subst G₁.toFun α.toFun)
    = (PowerSeries.subst (subst (g.toMvPowerSeries · ) G₁.toFun) α.toFun) := by
    unfold PowerSeries.subst
    rw [←subst_comp_subst]
    simp only [Function.comp_apply]
    refine hasSubst_of_constantCoeff_zero ?_
    simp [G₁.zero_constantCoeff]
    exact isIso_iff_substDomain_aux hb3
  have eq_aux2 : subst (g.toMvPowerSeries · ) (subst  (α.toFun.toMvPowerSeries · ) G₂.toFun) =
    subst (PowerSeries.toMvPowerSeries ·  (PowerSeries.subst g α.toFun)) G₂.toFun := by
    rw [subst_comp_subst_apply (isIso_iff_substDomain_aux (α.zero_constantCoeff))
      (isIso_iff_substDomain_aux hb3)]
    unfold PowerSeries.subst
    apply subst_congr
    funext x
    fin_cases x
    · simp
      rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply,
        PowerSeries.subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
          (fun s ↦ constantCoeff_X 0)) (isIso_iff_substDomain_aux hb3)]
      conv_rhs =>
        rw [PowerSeries.subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s ↦ hb3)
        (hasSubst_of_constantCoeff_zero (fun s ↦ constantCoeff_X 0))]
      apply subst_congr
      funext t
      rw [subst_X (isIso_iff_substDomain_aux hb3), PowerSeries.toMvPowerSeries_apply,
        PowerSeries.subst]
    · simp
      rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.subst, PowerSeries.toMvPowerSeries_apply,
        PowerSeries.subst, subst_comp_subst_apply
        (hasSubst_of_constantCoeff_zero (fun s ↦ constantCoeff_X 1)) (isIso_iff_substDomain_aux hb3),
        subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun s ↦ hb3)
        (hasSubst_of_constantCoeff_zero (fun s ↦ constantCoeff_X 1))]
      apply subst_congr
      funext t
      rw [subst_X (isIso_iff_substDomain_aux hb3), PowerSeries.toMvPowerSeries_apply, PowerSeries.subst]
  rw [eq_aux1, eq_aux2] at eq_aux
  unfold PowerSeries.subst at eq_aux
  rw [←subst_comp_subst (hasSubst_of_constantCoeff_zero (fun s ↦ G₁.zero_constantCoeff))
    (isIso_iff_substDomain_aux hb3)] at eq_aux
  rw [←subst_comp_subst (hasSubst_of_constantCoeff_zero (fun s ↦ G₁.zero_constantCoeff))
    (isIso_iff_substDomain_aux hb3), eq_aux]


theorem isIso_of_isUnit_coeff_one {G₁ G₂ : FormalGroup R} (α : FormalGroupHom G₁ G₂)
  (h : IsUnit (PowerSeries.coeff 1 α.toFun)) :
  ∃ (α₁ : FormalGroupIso G₁ G₂), α₁.toHom = α := by
  obtain ⟨g, hg1, hg2, hg3⟩ := PowerSeries.exist_subst_inv α.toFun h α.zero_constantCoeff
  have has_subst₁ : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg3
  have has_subst₂ : PowerSeries.HasSubst α.toFun := PowerSeries.HasSubst.of_constantCoeff_zero' α.zero_constantCoeff
  have hom_aux : PowerSeries.subst G₂.toFun g = subst (g.toMvPowerSeries · ) G₁.toFun := by
    have eq_aux : G₂.toFun =
        MvPowerSeries.subst (PowerSeries.toMvPowerSeries ·  (PowerSeries.subst g α.toFun)) G₂.toFun := by
        rw [(PowerSeries.subst_comp_eq_id_iff g (PowerSeries.HasSubst.of_constantCoeff_zero' hg3)
          (PowerSeries.HasSubst.of_constantCoeff_zero' α.zero_constantCoeff)).mp hg2]
        nth_rw 1 [subst_self G₂.toFun]
        apply subst_congr
        funext s
        fin_cases s
        <;> simpa [PowerSeries.toMvPowerSeries_apply] using
            (PowerSeries.subst_X (PowerSeries.HasSubst.X _)).symm
    have eq_aux' : G₂.toFun
      = PowerSeries.subst (subst (g.toMvPowerSeries · ) G₁.toFun) α.toFun := by
      rw [eq_aux]
      obtain h' := α.hom
      refine (isIso_iff_aux α hg3)
    rw [eq_aux']
    -- maybe need to change f here to satisfies some property that f ∈ PowerSeries.SubstDomain
    have subst_aux : ∀ (f : MvPowerSeries (Fin 2) R), PowerSeries.HasSubst f →
      PowerSeries.subst (PowerSeries.subst f α.toFun) g = f := by
      intro f hf
      rw [subst_assoc g α.toFun f has_subst₂ hf, (PowerSeries.subst_comp_eq_id_iff α.toFun has_subst₂ has_subst₁).mp hg1, PowerSeries.subst_X hf]
    refine (subst_aux (MvPowerSeries.subst (g.toMvPowerSeries · ) G₁.toFun) ?_)
    -- need to prove SubstDomain namely, `PowerSeries.SubstDomain (subst (sub_hom₂ g) G₁.toFun)`
    -- make this to be a lemma
    exact (substDomain_aux hg3 G₁ )

  let β : FormalGroupIso G₁ G₂ :=
  {
    toHom := α
    invHom := by
      refine
      {
      toFun := g
      zero_constantCoeff := hg3
      hom := hom_aux
      }
    left_inv := by
      exact hg1
    right_inv := by
      exact hg2
  }
  use β





theorem isUnit_coeff_one_of_isIso {G₁ G₂ : FormalGroup R} (α : FormalGroupIso G₁ G₂) :
  IsUnit (PowerSeries.coeff 1 α.toHom.toFun) := by
  have subdomain_a : PowerSeries.HasSubst α.toHom.toFun := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    rw [←α.toHom.zero_constantCoeff]
    rfl
  have subdomain_b : PowerSeries.HasSubst α.invHom.toFun := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    rw [←α.invHom.zero_constantCoeff]
    rfl
  have h₁ : PowerSeries.subst α.invHom.toFun α.toHom.toFun = PowerSeries.X (R := R) := by
    refine (PowerSeries.subst_comp_eq_id_iff α.invHom.toFun subdomain_b subdomain_a).mp α.right_inv
  obtain coeff_eq := PowerSeries.ext_iff.mp h₁ 1
  simp at coeff_eq

  have coeff_eq_mul : (PowerSeries.coeff 1) (PowerSeries.subst α.invHom.toFun α.toHom.toFun)
    = (PowerSeries.coeff 1 α.toHom.toFun) • (PowerSeries.coeff 1 α.invHom.toFun) := by
    unfold PowerSeries.coeff

    rw [PowerSeries.coeff_subst subdomain_b α.toHom.toFun (Finsupp.single (Unit.unit : Unit) 1)]
    have supp_aux : ∑ᶠ (d : ℕ), (PowerSeries.coeff d) α.toHom.toFun • (coeff (Finsupp.single () 1)) (α.invHom.toFun ^ d)
      = (PowerSeries.coeff 1) α.toHom.toFun • (coeff (Finsupp.single () 1)) (α.invHom.toFun ^ 1) := by
      apply finsum_eq_single
      intro n hn
      by_cases hn_zero : n = 0
      · -- the case n = 0
        simp [hn_zero]
      · -- the case n ≠ 0

        have coeff_zero : (coeff (Finsupp.single () 1)) (α.invHom.toFun ^ n) = 0 := by
          have aux : (Finsupp.single () 1) () = 1 := by simp
          rw [←PowerSeries.coeff_def]
          have hn_ge : n ≥ 2 := by omega
          rw [PowerSeries.coeff_pow]
          have zero_aux : ∀ l ∈ (Finset.range n).finsuppAntidiag 1,
            ∏ i ∈ Finset.range n, (PowerSeries.coeff (l i)) α.invHom.toFun = 0 := by
            intro l hl
            have exist_zero : ∃ i ∈ (Finset.range n), l i = 0 := by
              by_contra h'

              simp at h'
              have : ∀ x < n, l x ≥ 1 := by
                intro x hx
                obtain hx' := h' x hx
                omega
              simp at hl
              obtain ⟨hl₁, hl₂⟩ := hl
              have ineq_aux : (Finset.range n).sum ⇑l ≥ n := by
                calc
                  _ ≥ (Finset.range n).sum 1 := by
                    refine Finset.sum_le_sum ?_
                    intro i hi
                    simp at hi
                    obtain ineq := this i hi
                    simpa
                  _ = n := by
                    simp
              nlinarith
            obtain ⟨i, hi, exist_zero⟩ := exist_zero

            apply (Finset.prod_eq_zero hi)
            rw [exist_zero]
            simp
            rw [α.invHom.zero_constantCoeff]

          exact (Finset.sum_eq_zero zero_aux)
          simp
        simp [coeff_zero]
    rw [supp_aux]
    simp
  rw [coeff_eq] at coeff_eq_mul
  unfold IsUnit
  let u : Rˣ :=
    {
      val := (PowerSeries.coeff 1) α.toHom.toFun
      inv := (PowerSeries.coeff 1) α.invHom.toFun
      val_inv := by
        simp [coeff_eq_mul]
      inv_val := by
        simp [coeff_eq_mul]
        ring_nf
    }
  use u


variable (f : PowerSeries R) (h : IsUnit (PowerSeries.coeff 1 f)) (hc : PowerSeries.constantCoeff f = 0)

def subst_invFun : PowerSeries R := choose (PowerSeries.exist_subst_inv f h hc)

def subst_invSpec := choose_spec (PowerSeries.exist_subst_inv f h hc)

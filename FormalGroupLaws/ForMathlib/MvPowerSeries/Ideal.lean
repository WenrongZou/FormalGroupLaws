module

public import FormalGroupLaws.ForMathlib.MvPowerSeries
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.SModEq.Basic

@[expose] public section

variable {R S σ τ : Type*} [CommRing R] [CommRing S] {I : Ideal R} {f g : MvPowerSeries σ R}
  {a : σ → MvPowerSeries τ R} [Algebra R S]

namespace MvPowerSeries

section

lemma SModEq.subst_left (h : f ≡ g [SMOD I.map C]) (ha : HasSubst a) :
    f.subst a ≡ g.subst a [SMOD I.map C] := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hkerσ : RingHom.ker (map q (σ := σ)) = I.map C := by
    rw [ker_map, Ideal.mk_ker]
  have hkerτ : RingHom.ker (map q (σ := τ)) = I.map C := by
    rw [ker_map, Ideal.mk_ker]
  have hmap : f.map q = g.map q := by
    rw [← sub_eq_zero, ← map_sub]
    exact RingHom.mem_ker.mp (hkerσ.symm ▸ SModEq.sub_mem.mp h)
  apply SModEq.sub_mem.mpr
  rw [← hkerτ, RingHom.mem_ker, map_sub, map_subst ha, map_subst ha, hmap, sub_self]

lemma SModEq.subst_right {b : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (hb : HasSubst b) (h : ∀ i, a i ≡ b i [SMOD I.map C]) :
    f.subst a ≡ f.subst b [SMOD I.map C] := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hkerτ : RingHom.ker (map q (σ := τ)) = I.map C := by
    rw [ker_map, Ideal.mk_ker]
  have hmap (i : σ) : (a i).map q = (b i).map q := by
    rw [← sub_eq_zero, ← map_sub]
    exact RingHom.mem_ker.mp (hkerτ.symm ▸ SModEq.sub_mem.mp (h i))
  apply SModEq.sub_mem.mpr
  simp [← hkerτ, RingHom.mem_ker, map_sub, map_subst ha, map_subst hb,
    hmap]

end

end MvPowerSeries

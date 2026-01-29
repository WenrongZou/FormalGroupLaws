import Mathlib.CategoryTheory.RepresentedBy
import FormalGroupLaws.Basic
import Mathlib.Algebra.Category.Ring.Basic

universe u v w

noncomputable section Universal

open CategoryTheory Functor

variable (L : Type*) [CommRing L] (U : FormalGroup L)
  -- (FGL : CommRingCat → Type)

def FGL : CommRingCat ⥤ Type where
  obj R := FormalGroup R
  map f := FormalGroup.map f.hom
  map_id R := by
    ext F : 1
    simp [F.map_id]
  map_comp f g := by
    ext F : 1
    simp [F.map_comp]

def FormalGroup.IsUniversalOver : Prop :=
    ∀ (R : Type*) [CommRing R], ∀ F, ∃! (φ : L →+* R), U.map φ = F

-- theorem FGL_representable (h : U.IsUniversalOver L) : FGL.IsRepresentedBy U := sorry

#check IsRepresentedBy

end Universal

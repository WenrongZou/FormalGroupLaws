import Mathlib.CategoryTheory.RepresentedBy
import FormalGroupLaws.Basic
import Mathlib.Algebra.Category.Ring.Basic

universe u v w

namespace FormalGroup

noncomputable section Universal

open CategoryTheory Functor CommRingCat

variable (R : Type u) [CommRing R] (U : FormalGroup R) {C : Type u} [Category.{v} C]
  -- (FGL : CommRingCat → Type)

def FGL : CommRingCat.{u} ⥤ Type u where
  obj R := FormalGroup R
  map f := FormalGroup.map f.hom
  map_id R := by
    ext F : 1
    simp [FormalGroup.map]
  map_comp f g := by
    ext F : 1
    simp [FormalGroup.map]

def IsUniversalOver : Prop :=
    ∀ (T : Type u) [CommRing T], ∀ F, ∃! (φ : R →+* T), U.map φ = F

-- def L := 

section

/--
A presheaf `F` is represented by `X` with universal element `x : F.obj X`
if the natural transformation `F ⟶ yoneda.obj X` induced by `x` is an isomorphism.
For better universe generality, we state this manually as for every `Y`, the
induced map `(X ⟶ Y) → F.obj Y` is bijective.
-/
@[mk_iff]
structure _root_.CategoryTheory.Functor.IsCorepresentedBy
    (F : C ⥤ Type w) {X : C} (x : F.obj X) : Prop where
  map_bijective {Y : C} : Function.Bijective (fun f : X ⟶ Y ↦ F.map f x)

end

-- theorem FGL_representable (h : U.IsUniversalOver L) : FGL.IsCorepresentedBy U (X := of L) := by
--   rw [CategoryTheory.Functor.isCorepresentedBy_iff]
--   intro Y
--   rw [Function.Bijective, Function.Injective, Function.Surjective]
--   constructor
--   · intro f g h_fg
--     obtain ⟨φ, hU_f, hU_f'⟩ := h Y (U.map f.hom)
--     refine hom_ext ?_
--     rw [hU_f' f.hom rfl, hU_f' g.hom h_fg.symm]
--   intro F
--   obtain ⟨f, hf₁, hf₂⟩ := h (of Y) F
--   exact ⟨(ofHom f), hf₁⟩

end Universal

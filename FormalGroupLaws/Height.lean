import FormalGroupLaws.Basic

variable {R : Type*} [CommRing R]

open PowerSeries

namespace FormalGroup

noncomputable
def nseries (F : FormalGroup R) : ℕ → PowerSeries R
| 0 => 0
| k + 1 => F.toFun.subst ![(nseries F k), X]

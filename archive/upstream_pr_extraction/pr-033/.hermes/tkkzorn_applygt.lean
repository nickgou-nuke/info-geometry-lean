import InfoGeometry.Physics.TKKZorn
import InfoGeometry.Canonical.ZornSpinor

open InfoGeometry.Physics.TKKZorn

namespace Scratch

variable {R : Type*} [CommRing R] [CharZero R]

example (X : InfoGeometry.Canonical.ZornMatrix R) (h : triality_projector X = 0) : X = 0 := by
  rcases X with ⟨a, b, x, y⟩
  have ha : b = 0 := by simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.a h
  have hb : a = 0 := by simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.b h
  have hx : y = 0 := by simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.x h
  have hy : x = 0 := by simpa [triality_projector] using congrArg InfoGeometry.Canonical.ZornMatrix.y h
  subst a b x y
  rfl

end Scratch

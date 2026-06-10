import Mathlib

namespace InfoGeometry.RiemannSymmetries

variable {F : Type*} [Field F] [CharZero F]

/--
The functional equation of the Riemann Zeta function in standard coordinates:
`s ↦ 1 - s`.
-/
def zetaInvolution (s : F) : F := 1 - s

/--
The standard chart fixed point is forced to be 1/2.
This shows that the "1/2" is intrinsically tied to the chosen coordinate representation of the involution.
-/
theorem fixed_point_standard (s : F) (h : zetaInvolution s = s) :
    s = (1 : F) / 2 := by
  dsimp [zetaInvolution] at h
  have h2 : s + s = 1 := by
    calc
      s + s = (1 - s) + s := by rw [h]
      _ = 1 := by ring
  calc
    s = (s + s) / 2 := by ring
    _ = 1 / 2 := by rw [h2]

/--
The coordinate shift to the true coordinate-free central axis.
Instead of `s`, we parameterize the space by `u` where `s = u + 1/2`.
-/
def centralAxisShift (u : F) : F := u + (1 : F) / 2

/--
In the shifted coordinate `u`, the Riemann functional equation involution
is revealed to be a pure, scale-free parity flip: `u ↦ -u`.
This proves that the "Critical Line" at 1/2 is structurally just the
origin (`u = 0`) of the symmetric chart, devoid of any special numerical significance.
-/
theorem involution_is_parity (u : F) :
    zetaInvolution (centralAxisShift u) = centralAxisShift (-u) := by
  dsimp [zetaInvolution, centralAxisShift]
  ring

end InfoGeometry.RiemannSymmetries

import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Quantum.ParitySupercharge

Parity-relative supercharge package on a real Majorana core.

This is the linear-core companion to the continuous `PiEven` / `PiOdd` language
in `RealMajorana`. It is the natural owner surface for the split-triality
kernel, whose oddness is measured against the parity involution `Π`, not
against the geometric involution `J`.
-/

namespace InfoGeometry.Quantum

open InfoGeometry.Quantum.RealMajoranaCategory

namespace RealMajoranaCategory.RealMajoranaCore

/-- Linear endomorphisms commuting with the core parity involution `Π`. -/
@[rep_depth krein]
def ParityEven (X : RealMajoranaCore) (A : X →ₗ[ℝ] X) : Prop :=
  A.comp X.Pi = X.Pi.comp A

/-- Linear endomorphisms anticommuting with the core parity involution `Π`. -/
@[rep_depth krein]
def ParityOdd (X : RealMajoranaCore) (A : X →ₗ[ℝ] X) : Prop :=
  A.comp X.Pi = -(X.Pi.comp A)

end RealMajoranaCore

/--
Parity-relative supercharge package on a real Majorana core.

The oddness condition is measured against the parity involution `Π`.
-/
@[rep_depth krein]
structure ParitySupercharge (X : RealMajoranaCore) where
  Q : X →ₗ[ℝ] X
  odd : RealMajoranaCore.ParityOdd X Q

namespace ParitySupercharge

/-- The even square/Hamiltonian induced by a parity supercharge. -/
@[rep_depth krein]
noncomputable def hamiltonian
    {X : RealMajoranaCore} (S : ParitySupercharge X) : X →ₗ[ℝ] X :=
  S.Q.comp S.Q

/-- The Hamiltonian induced by a parity supercharge commutes with `Π`. -/
@[rep_depth krein]
theorem hamiltonian_parityEven
    {X : RealMajoranaCore} (S : ParitySupercharge X) :
    RealMajoranaCore.ParityEven X S.hamiltonian := by
  change (S.Q.comp S.Q).comp X.Pi = X.Pi.comp (S.Q.comp S.Q)
  calc
    (S.Q.comp S.Q).comp X.Pi
        = S.Q.comp (S.Q.comp X.Pi) := by
            simp [LinearMap.comp_assoc]
    _ = S.Q.comp (-(X.Pi.comp S.Q)) := by
          rw [S.odd]
    _ = -((S.Q.comp X.Pi).comp S.Q) := by
          ext x
          simp [LinearMap.comp_assoc]
    _ = -((-(X.Pi.comp S.Q)).comp S.Q) := by
          rw [S.odd]
    _ = X.Pi.comp (S.Q.comp S.Q) := by
          ext x
          simp [LinearMap.comp_assoc]

end ParitySupercharge
end RealMajoranaCategory

end InfoGeometry.Quantum

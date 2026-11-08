import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized

/-!
# Corrected A₃₂: reconstruction of homogenized channels

The Laplacian is twice Jordan multiplication by V. Adding twice its inner
derivation produces four times left multiplication by V. These identities
generate all four homogenized channels without dividing by integers.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def laplacianLeftWeight (P A C X : B) : B :=
  hodgeLaplacianPhi P A C X + (2 : ℤ) • connV P A C X

variable {P : B} (hP : P * P = P)
include hP

theorem laplacianLeftWeight_eq (A C X : B) :
    laplacianLeftWeight P A C X = (4 : ℤ) • (genV P A C * X) :=
  hodgeLaplacianPhi_add_connection hP A C X

theorem hProjV_laplacian_generation (A C X : B) :
    (4 : ℤ) • hProjV P A C X =
      (2 : ℤ) • laplacianLeftWeight P A C (laplacianLeftWeight P A C X) +
      laplacianLeftWeight P A C (derivSqPhi P A C X) +
      laplacianLeftWeight P A C (derivSqJ P A C X) +
      (4 : ℤ) • derivSqSig P A C X := by
  simp only [laplacianLeftWeight_eq hP, hProjV, mul_smul_comm, mul_assoc]
  abel

theorem hProjPhi_laplacian_generation (A C X : B) :
    (4 : ℤ) • hProjPhi P A C X =
      laplacianLeftWeight P A C (derivSqPhi P A C X) -
      laplacianLeftWeight P A C (derivSqJ P A C X) -
      (4 : ℤ) • derivSqSig P A C X := by
  simp only [laplacianLeftWeight_eq hP, hProjPhi]
  abel

theorem hProjJ_laplacian_generation (A C X : B) :
    (4 : ℤ) • hProjJ P A C X =
      laplacianLeftWeight P A C (derivSqJ P A C X) -
      laplacianLeftWeight P A C (derivSqPhi P A C X) -
      (4 : ℤ) • derivSqSig P A C X := by
  simp only [laplacianLeftWeight_eq hP, hProjJ]
  abel

theorem hProjSig_laplacian_generation (A C X : B) :
    (4 : ℤ) • hProjSig P A C X =
      (4 : ℤ) • derivSqSig P A C X -
      laplacianLeftWeight P A C (derivSqPhi P A C X) -
      laplacianLeftWeight P A C (derivSqJ P A C X) := by
  simp only [laplacianLeftWeight_eq hP, hProjSig]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine

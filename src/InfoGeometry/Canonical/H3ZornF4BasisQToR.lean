import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge
import InfoGeometry.Algebra.BaezF4H3Zorn

noncomputable section

namespace InfoGeometry.Canonical.H3ZornF4BasisQToR

open InfoGeometry.Algebra
open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
open InfoGeometry.Canonical.H3ZornBasis

-- define Q version
def h3_diagQ₁ : H3Zorn ℚ := { α₁ := 1, α₂ := 0, α₃ := 0, a := 0, b := 0, c := 0 }

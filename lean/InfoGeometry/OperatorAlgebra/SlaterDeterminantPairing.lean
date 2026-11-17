/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.RectangularDeterminantOverlap
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Slater determinants from native exterior dual pairing

The column vectors of a rectangular matrix determine a native exterior blade.
The conjugate column covectors determine an exterior blade in the algebraic
dual. Mathlib's canonical pairing of these two exterior spaces evaluates to
the determinant of the occupied-frame overlap `Lᴴ * R`.

For a rectangular linear map `D`, applying its actual exterior map before
pairing gives `det (Lᴴ * D * R)`. The source and target ambient spaces need
not coincide. The ordered matrix products are never assumed to commute.

The construction works over a commutative star ring, including the real and
complex fields. It does not posit a complex exterior Hilbert-space instance,
a continuum fermion measure, a regularized determinant, or an anomaly theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SlaterDeterminantPairing

open scoped Matrix
open InfoGeometry.OperatorAlgebra.RectangularDeterminantOverlap

variable {𝕜 m : Type*} [CommRing 𝕜] [StarRing 𝕜] [Fintype m]

/-- The exterior product of the columns of an occupied frame. -/
def slaterBlade {k : ℕ} (R : Matrix m (Fin k) 𝕜) : ⋀[𝕜]^k (m → 𝕜) :=
  exteriorPower.ιMulti 𝕜 k (fun j i => R i j)

/-- The exterior product of the conjugate column covectors. The covector
is native `dotProductBilin` applied to the conjugated column. -/
def slaterDualBlade {k : ℕ} (L : Matrix m (Fin k) 𝕜) :
    ⋀[𝕜]^k (Module.Dual 𝕜 (m → 𝕜)) :=
  exteriorPower.ιMulti 𝕜 k
    (fun j => dotProductBilin 𝕜 𝕜 (fun i => star (L i j)))

/-- Evaluation of the genuine exterior dual blade on the primal blade. -/
def slaterPairing {k : ℕ} (L R : Matrix m (Fin k) 𝕜) : 𝕜 :=
  exteriorPower.pairingDual 𝕜 (m → 𝕜) k (slaterDualBlade L) (slaterBlade R)

/-- The determinant readout is proved from the actual exterior pairing.
The transpose arises from the dual-pairing convention and disappears under
the native determinant transpose theorem. -/
theorem slaterPairing_eq_det_overlap {k : ℕ} (L R : Matrix m (Fin k) 𝕜) :
    slaterPairing L R = (overlap L R).det := by
  unfold slaterPairing slaterDualBlade slaterBlade
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  change ((overlap L R).transpose).det = (overlap L R).det
  exact Matrix.det_transpose (overlap L R)

/-- Acting on a blade is the exterior functor applied to the actual
rectangular matrix linear map. -/
theorem slaterBlade_map {n : Type*} [Fintype n] {k : ℕ}
    (D : Matrix m n 𝕜) (R : Matrix n (Fin k) 𝕜) :
    exteriorPower.map k D.mulVecLin (slaterBlade R) = slaterBlade (D * R) := by
  exact exteriorPower.map_apply_ιMulti D.mulVecLin (fun j i => R i j)

/-- A genuine cross-space exterior amplitude has the compressed Dirac
matrix determinant as its scalar coordinate in the two occupied frames. -/
theorem pairing_slater_map_eq_det_compression {n : Type*} [Fintype n] {k : ℕ}
    (D : Matrix m n 𝕜) (L : Matrix m (Fin k) 𝕜) (R : Matrix n (Fin k) 𝕜) :
    exteriorPower.pairingDual 𝕜 (m → 𝕜) k (slaterDualBlade L)
        (exteriorPower.map k D.mulVecLin (slaterBlade R)) =
      (compression D L R).det := by
  rw [slaterBlade_map]
  change slaterPairing L (D * R) = (compression D L R).det
  rw [slaterPairing_eq_det_overlap]
  simp only [overlap, compression, Matrix.mul_assoc]

/-- The squared exterior amplitude is determined by the ambient range
matrices. The right frame is isometric; no nonsingularity of the overlap
or independence of the left columns is required. -/
theorem slaterPairing_star_mul_self [DecidableEq m] {k : ℕ}
    (L R : Matrix m (Fin k) 𝕜) (hR : Rᴴ * R = 1) :
    star (slaterPairing L R) * slaterPairing L R =
      (1 - frameRange R + frameRange R * frameRange L * frameRange R).det := by
  simpa only [slaterPairing_eq_det_overlap] using (det_projector_overlap L R hR).symm

/-- Occupied rank zero has vacuum amplitude one, with no nonemptiness
assumption on the ambient space. -/
theorem slaterPairing_empty (L R : Matrix m (Fin 0) 𝕜) :
    slaterPairing L R = 1 := by
  rw [slaterPairing_eq_det_overlap]
  exact Matrix.det_isEmpty

end InfoGeometry.OperatorAlgebra.SlaterDeterminantPairing

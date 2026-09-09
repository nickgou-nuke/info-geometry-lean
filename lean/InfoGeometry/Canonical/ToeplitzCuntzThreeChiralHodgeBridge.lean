import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.NativeToeplitzCuntzThree
import InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge

/-!
# Chiral-Hodge operators in the native three-colour Toeplitz-Cuntz carrier

The carrier has three colour generators and the Toeplitz defect as a fourth
sector.  This file derives the cyclic colour arrow, its star mirror, their
sum and difference, and the native defect resolution.  It does not identify
the defect with a De Rham differential.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeChiralHodgeBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Canonical.NativeToeplitzCuntzThree
open InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

abbrev Carrier := CuntzToeplitzAlg 3

def colorArrow : Carrier :=
  generator (0 : Fin 3) * star (generator (1 : Fin 3)) +
    generator (1 : Fin 3) * star (generator (2 : Fin 3)) +
    generator (2 : Fin 3) * star (generator (0 : Fin 3))

def colorArrowStar : Carrier := star colorArrow
def diracPlus : Carrier := colorArrow + colorArrowStar
def diracMinus : Carrier := colorArrow - colorArrowStar
def colorHamiltonian : Carrier := nativeToeplitzThreeGenerators.susyHamiltonian
def timeDefect : Carrier := nativeToeplitzThreeGenerators.P0

theorem colorArrowStar_star : star colorArrowStar = colorArrow := by
  simp [colorArrowStar]

theorem diracPlus_selfAdjoint : star diracPlus = diracPlus := by
  simp [diracPlus, colorArrowStar, add_comm]

theorem diracMinus_skewAdjoint : star diracMinus = -diracMinus := by
  simp [diracMinus, colorArrowStar, sub_eq_add_neg, add_comm]

theorem diracPlus_add_diracMinus :
    diracPlus + diracMinus = (2 : ℂ) • colorArrow := by
  dsimp [diracPlus, diracMinus]
  module

theorem diracPlus_sub_diracMinus :
    diracPlus - diracMinus = (2 : ℂ) • colorArrowStar := by
  dsimp [diracPlus, diracMinus]
  module

theorem color_defect_resolution :
    colorHamiltonian + timeDefect = (1 : Carrier) := by
  exact native_three_resolution

theorem timeDefect_is_projection :
    timeDefect * timeDefect = timeDefect := by
  change nativeToeplitzThreeGenerators.P0 *
      nativeToeplitzThreeGenerators.P0 = nativeToeplitzThreeGenerators.P0
  exact native_defect_is_projection

theorem timeDefect_selfAdjoint :
    star timeDefect = timeDefect := by
  exact native_defect_is_self_adjoint

theorem colorHamiltonian_timeDefect_zero :
    colorHamiltonian * timeDefect = 0 := by
  change nativeToeplitzThreeGenerators.susyHamiltonian *
      nativeToeplitzThreeGenerators.P0 = 0
  exact susyHamiltonian_defect_annihilation_right nativeToeplitzThreeGenerators

theorem timeDefect_colorHamiltonian_zero :
    timeDefect * colorHamiltonian = 0 := by
  change nativeToeplitzThreeGenerators.P0 *
      nativeToeplitzThreeGenerators.susyHamiltonian = 0
  exact susyHamiltonian_defect_annihilation_left nativeToeplitzThreeGenerators

/-! ## Native creation/annihilation sums and vacuum compression -/

def toeplitzCreationSum : Carrier :=
  nativeToeplitzThreeGenerators.V1 + nativeToeplitzThreeGenerators.V2 +
    nativeToeplitzThreeGenerators.V3

def toeplitzAnnihilationSum : Carrier := star toeplitzCreationSum

def toeplitzDiracPlus : Carrier :=
  toeplitzCreationSum + toeplitzAnnihilationSum

def toeplitzDiracMinus : Carrier :=
  toeplitzCreationSum - toeplitzAnnihilationSum

def toeplitzCommutatorDefect : Carrier :=
  toeplitzAnnihilationSum * toeplitzCreationSum -
    toeplitzCreationSum * toeplitzAnnihilationSum

/-! The reverse product contains six genuine off-diagonal channel terms. -/

def offDiagonalChannelMixing : Carrier :=
  nativeToeplitzThreeGenerators.V1 * star nativeToeplitzThreeGenerators.V2 +
    nativeToeplitzThreeGenerators.V1 * star nativeToeplitzThreeGenerators.V3 +
    nativeToeplitzThreeGenerators.V2 * star nativeToeplitzThreeGenerators.V1 +
    nativeToeplitzThreeGenerators.V2 * star nativeToeplitzThreeGenerators.V3 +
    nativeToeplitzThreeGenerators.V3 * star nativeToeplitzThreeGenerators.V1 +
    nativeToeplitzThreeGenerators.V3 * star nativeToeplitzThreeGenerators.V2

theorem p0_mul_v1 (g : ToeplitzCuntzThreeGenerators Carrier) :
    g.P0 * g.V1 = 0 := by
  have h := p0_p1_ortho g
  calc
    g.P0 * g.V1 = g.P0 * g.V1 * (star g.V1 * g.V1) := by rw [g.V1_isometry]; noncomm_ring
    _ = (g.P0 * (g.V1 * star g.V1)) * g.V1 := by noncomm_ring
    _ = g.P0 * g.P1 * g.V1 := rfl
    _ = 0 := by rw [h]; simp

theorem p0_mul_v2 (g : ToeplitzCuntzThreeGenerators Carrier) :
    g.P0 * g.V2 = 0 := by
  have h := p0_p2_ortho g
  calc
    g.P0 * g.V2 = g.P0 * g.V2 * (star g.V2 * g.V2) := by rw [g.V2_isometry]; noncomm_ring
    _ = (g.P0 * (g.V2 * star g.V2)) * g.V2 := by noncomm_ring
    _ = g.P0 * g.P2 * g.V2 := rfl
    _ = 0 := by rw [h]; simp

theorem p0_mul_v3 (g : ToeplitzCuntzThreeGenerators Carrier) :
    g.P0 * g.V3 = 0 := by
  have h := p0_p3_ortho g
  calc
    g.P0 * g.V3 = g.P0 * g.V3 * (star g.V3 * g.V3) := by rw [g.V3_isometry]; noncomm_ring
    _ = (g.P0 * (g.V3 * star g.V3)) * g.V3 := by noncomm_ring
    _ = g.P0 * g.P3 * g.V3 := rfl
    _ = 0 := by rw [h]; simp

theorem star_v1_mul_p0 (g : ToeplitzCuntzThreeGenerators Carrier) :
    star g.V1 * g.P0 = 0 := by
  have h := p1_p0_ortho g
  calc
    star g.V1 * g.P0 = (star g.V1 * g.V1) * (star g.V1 * g.P0) := by rw [g.V1_isometry]; noncomm_ring
    _ = star g.V1 * (g.P1 * g.P0) := by
      simp [ToeplitzCuntzThreeGenerators.P1, mul_assoc]
    _ = 0 := by rw [h]; simp

theorem star_v2_mul_p0 (g : ToeplitzCuntzThreeGenerators Carrier) :
    star g.V2 * g.P0 = 0 := by
  have h := p2_p0_ortho g
  calc
    star g.V2 * g.P0 = (star g.V2 * g.V2) * (star g.V2 * g.P0) := by rw [g.V2_isometry]; noncomm_ring
    _ = star g.V2 * (g.P2 * g.P0) := by
      simp [ToeplitzCuntzThreeGenerators.P2, mul_assoc]
    _ = 0 := by rw [h]; simp

theorem star_v3_mul_p0 (g : ToeplitzCuntzThreeGenerators Carrier) :
    star g.V3 * g.P0 = 0 := by
  have h := p3_p0_ortho g
  calc
    star g.V3 * g.P0 = (star g.V3 * g.V3) * (star g.V3 * g.P0) := by rw [g.V3_isometry]; noncomm_ring
    _ = star g.V3 * (g.P3 * g.P0) := by
      simp [ToeplitzCuntzThreeGenerators.P3, mul_assoc]
    _ = 0 := by rw [h]; simp

theorem native_vacuumDefect_creationSum_zero :
    timeDefect * toeplitzCreationSum = 0 := by
  change nativeToeplitzThreeGenerators.P0 *
      (nativeToeplitzThreeGenerators.V1 +
        nativeToeplitzThreeGenerators.V2 + nativeToeplitzThreeGenerators.V3) = 0
  rw [mul_add, mul_add, p0_mul_v1, p0_mul_v2, p0_mul_v3]
  simp

theorem native_annihilationSum_vacuumDefect_zero :
    toeplitzAnnihilationSum * timeDefect = 0 := by
  unfold toeplitzAnnihilationSum toeplitzCreationSum timeDefect
  have h1 := star_v1_mul_p0 nativeToeplitzThreeGenerators
  have h2 := star_v2_mul_p0 nativeToeplitzThreeGenerators
  have h3 := star_v3_mul_p0 nativeToeplitzThreeGenerators
  rw [star_add, star_add, add_mul, add_mul, h1, h2, h3]
  module

theorem native_annihilationSum_creationSum :
    toeplitzAnnihilationSum * toeplitzCreationSum = (3 : Carrier) := by
  have h_iso1 := nativeToeplitzThreeGenerators.V1_isometry
  have h_iso2 := nativeToeplitzThreeGenerators.V2_isometry
  have h_iso3 := nativeToeplitzThreeGenerators.V3_isometry
  have h12 := nativeToeplitzThreeGenerators.V1_V2_ortho
  have h21 := nativeToeplitzThreeGenerators.V2_V1_ortho
  have h23 := nativeToeplitzThreeGenerators.V2_V3_ortho
  have h32 := nativeToeplitzThreeGenerators.V3_V2_ortho
  have h13 := nativeToeplitzThreeGenerators.V1_V3_ortho
  have h31 := nativeToeplitzThreeGenerators.V3_V1_ortho
  unfold toeplitzAnnihilationSum toeplitzCreationSum
  rw [star_add, star_add]
  simp only [add_mul, mul_add]
  rw [h_iso1, h_iso2, h_iso3, h12, h21, h23, h32, h13, h31]
  abel_nf
  norm_num

theorem native_vacuumCompression_creation_annihilation :
    timeDefect * (toeplitzCreationSum * toeplitzAnnihilationSum) * timeDefect = 0 := by
  calc
    _ = (timeDefect * toeplitzCreationSum) * toeplitzAnnihilationSum * timeDefect := by noncomm_ring
    _ = 0 := by rw [native_vacuumDefect_creationSum_zero]; simp

theorem native_vacuumCompression_annihilation_creation :
    timeDefect * (toeplitzAnnihilationSum * toeplitzCreationSum) * timeDefect =
      (3 : Carrier) * timeDefect := by
  rw [native_annihilationSum_creationSum]
  have hp : timeDefect * timeDefect = timeDefect := timeDefect_is_projection
  calc
    timeDefect * (3 : Carrier) * timeDefect = (3 : Carrier) *
        (timeDefect * timeDefect) := by noncomm_ring
    _ = (3 : Carrier) * timeDefect := by rw [hp]

theorem native_vacuumCompression_diracPlus :
    timeDefect * toeplitzDiracPlus * timeDefect = 0 := by
  have hc : timeDefect * toeplitzCreationSum * timeDefect = 0 := by
    calc _ = (timeDefect * toeplitzCreationSum) * timeDefect := by rfl
         _ = 0 := by rw [native_vacuumDefect_creationSum_zero]; simp
  have ha : timeDefect * toeplitzAnnihilationSum * timeDefect = 0 := by
    calc _ = timeDefect * (toeplitzAnnihilationSum * timeDefect) := by noncomm_ring
         _ = 0 := by rw [native_annihilationSum_vacuumDefect_zero]; simp
  dsimp [toeplitzDiracPlus]
  rw [mul_add, add_mul, hc, ha]
  simp

theorem native_vacuumCompression_diracMinus :
    timeDefect * toeplitzDiracMinus * timeDefect = 0 := by
  have hc : timeDefect * toeplitzCreationSum * timeDefect = 0 := by
    calc _ = (timeDefect * toeplitzCreationSum) * timeDefect := by rfl
         _ = 0 := by rw [native_vacuumDefect_creationSum_zero]; simp
  have ha : timeDefect * toeplitzAnnihilationSum * timeDefect = 0 := by
    calc _ = timeDefect * (toeplitzAnnihilationSum * timeDefect) := by noncomm_ring
         _ = 0 := by rw [native_annihilationSum_vacuumDefect_zero]; simp
  dsimp [toeplitzDiracMinus]
  rw [mul_sub, sub_mul, hc, ha]
  simp

end InfoGeometry.Canonical.ToeplitzCuntzThreeChiralHodgeBridge

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge

/-!
# Exterior / right-regular split-octonion BdG intertwiner

The literal exterior basis and the genuine `uPlus/uMinus` circular Peirce basis
have the same `1+3+3+1` dimensions, but the CAR/Fock orientation fixes nontrivial
signs in degrees two and three.  This owner records that signed change of basis
as a genuine linear equivalence.

The basis convention is

`(1,e0,e1,e2,e012,e12,e02,e01)`

mapping to

`(uPlus,S0+,S1+,S2+,-uMinus,-S0-,+S1-,-S2-)`.

These signs are the ones generated recursively by right-regular creation from
the vacuum `uPlus`.  No multiplicative equivalence between exterior wedge and
split-octonion multiplication is asserted.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev V3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.V3
abbrev CZ :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn
abbrev Coord8 := Fin 8 → ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- Fock signs in the established Peirce ordering. -/
def bdgSign : Fin 8 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => -1
  | 5 => -1
  | 6 => 1
  | 7 => -1

@[simp] theorem bdgSign_sq (i : Fin 8) : bdgSign i * bdgSign i = 1 := by
  fin_cases i <;> norm_num [bdgSign]

/-- Diagonal sign change on the common eight-coordinate carrier. -/
def bdgCoordinateSignEquiv : Coord8 ≃ₗ[ℝ] Coord8 where
  toFun x i := bdgSign i * x i
  invFun x i := bdgSign i * x i
  left_inv x := by
    funext i
    rw [← mul_assoc, bdgSign_sq, one_mul]
  right_inv x := by
    funext i
    rw [← mul_assoc, bdgSign_sq, one_mul]
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem bdgCoordinateSignEquiv_single (i : Fin 8) :
    bdgCoordinateSignEquiv (Pi.single i (1 : ℝ)) =
      bdgSign i • Pi.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [bdgCoordinateSignEquiv, Pi.single_apply]
  · simp [bdgCoordinateSignEquiv, Pi.single_apply, h]

/-- The actual BdG/Fock carrier equivalence from the literal Mathlib exterior
algebra to the genuine `uPlus/uMinus` circular split-octonion frame. -/
noncomputable def exteriorBdGEquiv : Exterior3 ≃ₗ[ℝ] CZ :=
  exterior3SplitOctonionCoordinateEquiv.trans
    (bdgCoordinateSignEquiv.trans circularPeirceBasis.equivFun.symm)

/-- Basis-by-basis signed identification. -/
@[simp] theorem exteriorBdGEquiv_basis (j : Fin 8) :
    exteriorBdGEquiv (exterior3PeirceBasis j) =
      bdgSign j • circularPeirceBasis j := by
  rw [exteriorBdGEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    exterior3SplitOctonionCoordinateEquiv_basis,
    bdgCoordinateSignEquiv_single]
  rw [map_smul]
  simp

/-- The inverse has the same signs because every sign is `±1`. -/
@[simp] theorem exteriorBdGEquiv_symm_basis (j : Fin 8) :
    exteriorBdGEquiv.symm (circularPeirceBasis j) =
      bdgSign j • exterior3PeirceBasis j := by
  apply exteriorBdGEquiv.injective
  rw [exteriorBdGEquiv.apply_symm_apply, map_smul, exteriorBdGEquiv_basis,
    smul_smul]
  change (bdgSign j * bdgSign j) • circularPeirceBasis j = circularPeirceBasis j
  rw [bdgSign_sq]
  simp

/-- Transport of an exterior endomorphism through the signed BdG equivalence. -/
def bdgTransportEnd (T : Module.End ℝ Exterior3) : EndCZ :=
  InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
    exteriorBdGEquiv T

/-- Signed-BdG transported creation operator. -/
def bdgCreation (i : Fin 3) : EndCZ :=
  bdgTransportEnd (exteriorWedge3 (modeVector i))

/-- Signed-BdG transported annihilation operator. -/
def bdgAnnihilation (i : Fin 3) : EndCZ :=
  bdgTransportEnd (exteriorContract3 (modeCovector i))

/-- The signed carrier map intertwines exterior creation with its transported
operator by construction. -/
theorem bdgCreation_intertwines (i : Fin 3) :
    bdgCreation i ∘ₗ exteriorBdGEquiv.toLinearMap =
      exteriorBdGEquiv.toLinearMap ∘ₗ exteriorWedge3 (modeVector i) := by
  apply LinearMap.ext
  intro ψ
  simp [bdgCreation, bdgTransportEnd,
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric]

/-- The same carrier map intertwines contraction with transported annihilation. -/
theorem bdgAnnihilation_intertwines (i : Fin 3) :
    bdgAnnihilation i ∘ₗ exteriorBdGEquiv.toLinearMap =
      exteriorBdGEquiv.toLinearMap ∘ₗ exteriorContract3 (modeCovector i) := by
  apply LinearMap.ext
  intro ψ
  simp [bdgAnnihilation, bdgTransportEnd,
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric]

/-- The transported operators retain the exact CAR. -/
theorem bdgTransported_CAR (i : Fin 3) :
    bdgAnnihilation i * bdgCreation i + bdgCreation i * bdgAnnihilation i =
      (1 : EndCZ) := by
  change
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        exteriorBdGEquiv (exteriorContract3 (modeCovector i)) *
      InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        exteriorBdGEquiv (exteriorWedge3 (modeVector i)) +
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        exteriorBdGEquiv (exteriorWedge3 (modeVector i)) *
      InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        exteriorBdGEquiv (exteriorContract3 (modeCovector i)) = _
  let e := exteriorBdGEquiv
  let C := exteriorContract3 (modeCovector i)
  let W := exteriorWedge3 (modeVector i)
  apply LinearMap.ext
  intro x
  change e (C (W (e.symm x))) + e (W (C (e.symm x))) = x
  rw [← map_add]
  have hcar := exteriorContract3_wedge3_CAR (modeCovector i) (modeVector i)
  have hv : modeCovector i (modeVector i) = 1 := modeCovector_modeVector i
  have happ := LinearMap.congr_fun hcar (e.symm x)
  simp only [Module.End.mul_apply, LinearMap.add_apply] at happ
  rw [hv, one_smul] at happ
  rw [happ, e.apply_symm_apply]

/-- Endpoint equality with the genuine right-regular creation operator. -/
theorem bdgCreation_on_vacuum (i : Fin 3) :
    bdgCreation i uPlus = rightRegular (rootPlus i) uPlus := by
  rw [rightRegular_rootPlus_uPlus]
  change exteriorBdGEquiv
      (exteriorWedge3 (modeVector i) (exteriorBdGEquiv.symm uPlus)) = rootPlus i
  have h0 : circularPeirceBasis 0 = uPlus := circularPeirceBasis_zero
  rw [← h0, exteriorBdGEquiv_symm_basis]
  simp [bdgSign, exteriorWedge3, modeVector, exterior3PeirceBasis_eq_mathlibBasis,
    ExteriorAlgebra.basis_apply, exteriorPower.ιMulti_family]

/-- Endpoint equality with the genuine right-regular annihilation operator. -/
theorem bdgAnnihilation_on_vacuum (i : Fin 3) :
    bdgAnnihilation i uPlus = rightRegular (rootMinus i) uPlus := by
  rw [rightRegular_rootMinus_uPlus]
  change exteriorBdGEquiv
      (exteriorContract3 (modeCovector i) (exteriorBdGEquiv.symm uPlus)) = 0
  have h0 : circularPeirceBasis 0 = uPlus := circularPeirceBasis_zero
  rw [← h0, exteriorBdGEquiv_symm_basis]
  simp [bdgSign, exteriorContract3, modeCovector,
    exterior3PeirceBasis_eq_mathlibBasis, ExteriorAlgebra.basis_apply,
    exteriorPower.ιMulti_family]

end InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

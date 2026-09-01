import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading

/-!
# Exterior / right-regular split-octonion BdG intertwiner

This owner closes the CAR/Fock bridge between the literal Mathlib exterior
algebra `ExteriorAlgebra ℝ (Fin 3 → ℝ)` and the genuine `uPlus/uMinus`
circular split-octonion carrier.

There are two complementary descriptions of the carrier map.

1. `exteriorBdGEquiv` records the signed `1+3+3+1` basis convention

   `(1,e0,e1,e2,e012,e12,e02,e01)`

   mapping to

   `(uPlus,S0+,S1+,S2+,-uMinus,-S0-,+S1-,-S2-)`.

2. `fockBdGEquiv` is constructed intrinsically from the universal property of
   the exterior algebra.  The three degree-one generators act by right-regular
   multiplication with the three positive circular roots and the vacuum is
   `uPlus`.

The second construction gives the exact operator intertwiners

`Ad_U(creation_i) = R_(S_i+)`,
`Ad_U(annihilation_i) = R_(S_i-)`.

No multiplicative equivalence between exterior wedge multiplication and the
nonassociative split-octonion product is asserted.  The target representation
is the associative operator algebra `End(CZ)`.
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

open scoped BigOperators

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev V3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.V3
abbrev CZ :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn
abbrev Coord8 := Fin 8 → ℝ
abbrev EndCZ := Module.End ℝ CZ

/-! ## The signed coordinate realization -/

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

/-- Explicit signed basis equivalence from the literal exterior carrier to the
genuine circular Peirce carrier. -/
noncomputable def exteriorBdGEquiv : Exterior3 ≃ₗ[ℝ] CZ :=
  exterior3SplitOctonionCoordinateEquiv.trans
    (bdgCoordinateSignEquiv.trans circularPeirceBasis.equivFun.symm)

@[simp] theorem exteriorBdGEquiv_basis (j : Fin 8) :
    exteriorBdGEquiv (exterior3PeirceBasis j) =
      bdgSign j • circularPeirceBasis j := by
  rw [exteriorBdGEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    exterior3SplitOctonionCoordinateEquiv_basis,
    bdgCoordinateSignEquiv_single]
  rw [map_smul]
  simp

@[simp] theorem exteriorBdGEquiv_symm_basis (j : Fin 8) :
    exteriorBdGEquiv.symm (circularPeirceBasis j) =
      bdgSign j • exterior3PeirceBasis j := by
  apply exteriorBdGEquiv.injective
  rw [exteriorBdGEquiv.apply_symm_apply, map_smul, exteriorBdGEquiv_basis,
    smul_smul]
  change (bdgSign j * bdgSign j) • circularPeirceBasis j = circularPeirceBasis j
  rw [bdgSign_sq]
  simp

/-- Transport through the explicit signed basis equivalence. -/
def bdgTransportEnd (T : Module.End ℝ Exterior3) : EndCZ :=
  InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
    exteriorBdGEquiv T

def bdgCreation (i : Fin 3) : EndCZ :=
  bdgTransportEnd (exteriorWedge3 (modeVector i))

def bdgAnnihilation (i : Fin 3) : EndCZ :=
  bdgTransportEnd (exteriorContract3 (modeCovector i))

theorem bdgCreation_intertwines (i : Fin 3) :
    bdgCreation i ∘ₗ exteriorBdGEquiv.toLinearMap =
      exteriorBdGEquiv.toLinearMap ∘ₗ exteriorWedge3 (modeVector i) := by
  apply LinearMap.ext
  intro ψ
  simp [bdgCreation, bdgTransportEnd,
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric]

theorem bdgAnnihilation_intertwines (i : Fin 3) :
    bdgAnnihilation i ∘ₗ exteriorBdGEquiv.toLinearMap =
      exteriorBdGEquiv.toLinearMap ∘ₗ exteriorContract3 (modeCovector i) := by
  apply LinearMap.ext
  intro ψ
  simp [bdgAnnihilation, bdgTransportEnd,
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric]

/-! ## Universal exterior representation by right-regular creation -/

/-- Linear combination of the three positive circular roots. -/
noncomputable def rootPlusLinear : V3 →ₗ[ℝ] CZ where
  toFun v := ∑ i : Fin 3, v i • rootPlus i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]

@[simp] theorem rootPlusLinear_modeVector (i : Fin 3) :
    rootPlusLinear (modeVector i) = rootPlus i := by
  fin_cases i <;>
    simp [rootPlusLinear, modeVector, Fin.sum_univ_three, Pi.single_apply]

/-- Every linear combination of the positive circular root channels is
square-zero.  This is the isotropic three-plane behind the creation algebra. -/
theorem rootPlusLinear_sq_zero (v : V3) :
    rootPlusLinear v * rootPlusLinear v = (0 : CZ) := by
  ext k <;>
    simp [rootPlusLinear, Fin.sum_univ_three, rootPlus, chiralNull, ellBasis,
      quaternionBasis,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.iUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.jUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kQuaternionUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.mul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases k) <;> ring

/-- Right multiplication is linear in its multiplier. -/
noncomputable def rightRegularLinear : CZ →ₗ[ℝ] EndCZ where
  toFun := rightRegular
  map_add' a b := by
    apply LinearMap.ext
    intro x
    change x * (a + b) = x * a + x * b
    exact mul_add x a b
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    change x * (c • a) = c • (x * a)
    exact mul_smul_comm c x a

/-- Three-mode creation map into the associative endomorphism algebra. -/
noncomputable def rightCreationMap : V3 →ₗ[ℝ] EndCZ :=
  rightRegularLinear.comp rootPlusLinear

@[simp] theorem rightCreationMap_modeVector (i : Fin 3) :
    rightCreationMap (modeVector i) = rightRegular (rootPlus i) := by
  simp [rightCreationMap, rightRegularLinear]

/-- The creation map satisfies the exterior universal relation. -/
theorem rightCreationMap_sq_zero (v : V3) :
    rightCreationMap v * rightCreationMap v = (0 : EndCZ) := by
  change rightRegular (rootPlusLinear v) * rightRegular (rootPlusLinear v) = 0
  exact rightRegular_sq_zero_of_sq_zero (rootPlusLinear v) (rootPlusLinear_sq_zero v)

/-- Universal exterior-algebra representation generated by the right-regular
positive circular roots. -/
noncomputable def rightCreationRepresentation : Exterior3 →ₐ[ℝ] EndCZ :=
  ExteriorAlgebra.lift ℝ ⟨rightCreationMap, rightCreationMap_sq_zero⟩

@[simp] theorem rightCreationRepresentation_ι (v : V3) :
    rightCreationRepresentation (ExteriorAlgebra.ι ℝ v) = rightCreationMap v := by
  simp [rightCreationRepresentation]

@[simp] theorem rightCreationRepresentation_ι_mode (i : Fin 3) :
    rightCreationRepresentation (ExteriorAlgebra.ι ℝ (modeVector i)) =
      rightRegular (rootPlus i) := by
  rw [rightCreationRepresentation_ι, rightCreationMap_modeVector]

/-- Vacuum representation: an exterior state acts on the split-octonion
vacuum `uPlus`. -/
noncomputable def fockToZorn : Exterior3 →ₗ[ℝ] CZ where
  toFun ψ := rightCreationRepresentation ψ uPlus
  map_add' ψ ξ := by simp
  map_smul' c ψ := by simp

@[simp] theorem fockToZorn_one : fockToZorn (1 : Exterior3) = uPlus := by
  simp [fockToZorn]

/-- Creation intertwining follows directly from the universal algebra map. -/
theorem fockToZorn_creation (v : V3) (ψ : Exterior3) :
    fockToZorn (exteriorWedge3 v ψ) =
      rightCreationMap v (fockToZorn ψ) := by
  change rightCreationRepresentation (ExteriorAlgebra.ι ℝ v * ψ) uPlus = _
  rw [map_mul, rightCreationRepresentation_ι]
  rfl

/-- Mode form of the creation intertwiner. -/
theorem fockToZorn_creation_mode (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (exteriorWedge3 (modeVector i) ψ) =
      rightRegular (rootPlus i) (fockToZorn ψ) := by
  rw [fockToZorn_creation, rightCreationMap_modeVector]

/-- Mixed CAR between a fixed right-regular annihilation mode and an arbitrary
linear creation channel. -/
theorem rightAnnihilation_creationMap_CAR (i : Fin 3) (v : V3) :
    rightRegular (rootMinus i) * rightCreationMap v +
        rightCreationMap v * rightRegular (rootMinus i) =
      (modeCovector i v) • (1 : EndCZ) := by
  have hv : rightCreationMap v =
      ∑ j : Fin 3, v j • rightRegular (rootPlus j) := by
    apply LinearMap.ext
    intro x
    change x * rootPlusLinear v =
      (∑ j : Fin 3, v j • rightRegular (rootPlus j)) x
    simp [rootPlusLinear, rightRegular_apply, mul_sum, mul_smul_comm]
  rw [hv, Fin.sum_univ_three]
  fin_cases i
  · have h0 := rightRegular_root_mixed_CAR (0 : Fin 3) 0
    have h1 := rightRegular_root_mixed_CAR (0 : Fin 3) 1
    have h2 := rightRegular_root_mixed_CAR (0 : Fin 3) 2
    simp only [if_pos rfl] at h0
    norm_num at h1 h2
    have hcoord : modeCovector (0 : Fin 3) v = v 0 := by
      simp [modeCovector]
    rw [hcoord]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    noncomm_ring [h0, h1, h2]
  · have h0 := rightRegular_root_mixed_CAR (1 : Fin 3) 0
    have h1 := rightRegular_root_mixed_CAR (1 : Fin 3) 1
    have h2 := rightRegular_root_mixed_CAR (1 : Fin 3) 2
    norm_num at h0 h2
    simp only [if_pos rfl] at h1
    have hcoord : modeCovector (1 : Fin 3) v = v 1 := by
      simp [modeCovector]
    rw [hcoord]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    noncomm_ring [h0, h1, h2]
  · have h0 := rightRegular_root_mixed_CAR (2 : Fin 3) 0
    have h1 := rightRegular_root_mixed_CAR (2 : Fin 3) 1
    have h2 := rightRegular_root_mixed_CAR (2 : Fin 3) 2
    norm_num at h0 h1
    simp only [if_pos rfl] at h2
    have hcoord : modeCovector (2 : Fin 3) v = v 2 := by
      simp [modeCovector]
    rw [hcoord]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    noncomm_ring [h0, h1, h2]

/-- Annihilation intertwining follows from the contraction recursion and the
mixed CAR; no basis-by-basis assumption is used. -/
theorem fockToZorn_annihilation (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (exteriorContract3 (modeCovector i) ψ) =
      rightRegular (rootMinus i) (fockToZorn ψ) := by
  refine CliffordAlgebra.left_induction (Q := (0 : QuadraticForm ℝ V3)) ?_ ?_ ?_ ψ
  · intro r
    simp [fockToZorn, exteriorContract3, rightRegular_rootMinus_uPlus]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro x v hx
    rw [exteriorContract3_wedge3_apply]
    rw [map_sub, map_smul, fockToZorn_creation]
    rw [hx]
    have hcar := LinearMap.congr_fun (rightAnnihilation_creationMap_CAR i v)
      (fockToZorn x)
    simp only [Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, one_apply] at hcar
    change
      modeCovector i v • fockToZorn x -
          rightCreationMap v (rightRegular (rootMinus i) (fockToZorn x)) =
        rightRegular (rootMinus i) (rightCreationMap v (fockToZorn x))
    linarith

/-! ## Explicit preimages and bijectivity -/

private def ιMode (i : Fin 3) : Exterior3 :=
  ExteriorAlgebra.ι ℝ (modeVector i)

/-- Explicit exterior preimages of the genuine circular basis. -/
def fockPreimageBasis : Fin 8 → Exterior3
  | 0 => 1
  | 1 => ιMode 0
  | 2 => ιMode 1
  | 3 => ιMode 2
  | 4 => -(ιMode 0 * (ιMode 1 * ιMode 2))
  | 5 => -(ιMode 1 * ιMode 2)
  | 6 => ιMode 0 * ιMode 2
  | 7 => -(ιMode 0 * ιMode 1)

/-- The explicit Fock monomials hit the genuine circular basis exactly. -/
@[simp] theorem fockToZorn_preimageBasis (j : Fin 8) :
    fockToZorn (fockPreimageBasis j) = circularPeirceBasis j := by
  fin_cases j
  · simp [fockPreimageBasis, circularPeirceBasis_zero]
  · simp [fockPreimageBasis, ιMode, fockToZorn_creation_mode,
      circularPeirceBasis_one, rightRegular_rootPlus_uPlus]
  · simp [fockPreimageBasis, ιMode, fockToZorn_creation_mode,
      circularPeirceBasis_two, rightRegular_rootPlus_uPlus]
  · simp [fockPreimageBasis, ιMode, fockToZorn_creation_mode,
      circularPeirceBasis_three, rightRegular_rootPlus_uPlus]
  · simp [fockPreimageBasis, ιMode, map_neg, map_mul,
      rightCreationRepresentation_ι_mode, fockToZorn,
      Module.End.mul_apply, rightRegular_apply,
      rightRegular_rootPlus_uPlus,
      rootPlus_two_mul_rootPlus_one,
      rootMinus_mul_rootPlus, circularPeirceBasis_four]
  · simp [fockPreimageBasis, ιMode, map_neg, map_mul,
      rightCreationRepresentation_ι_mode, fockToZorn,
      Module.End.mul_apply, rightRegular_apply,
      rightRegular_rootPlus_uPlus,
      rootPlus_two_mul_rootPlus_one, circularPeirceBasis_five]
  · simp [fockPreimageBasis, ιMode, map_mul,
      rightCreationRepresentation_ι_mode, fockToZorn,
      Module.End.mul_apply, rightRegular_apply,
      rightRegular_rootPlus_uPlus,
      rootPlus_two_mul_rootPlus_zero, circularPeirceBasis_six]
  · simp [fockPreimageBasis, ιMode, map_neg, map_mul,
      rightCreationRepresentation_ι_mode, fockToZorn,
      Module.End.mul_apply, rightRegular_apply,
      rightRegular_rootPlus_uPlus,
      rootPlus_one_mul_rootPlus_zero, circularPeirceBasis_seven]

/-- The vacuum Fock map is surjective because it contains a full circular
basis in its image. -/
theorem fockToZorn_surjective : Function.Surjective fockToZorn := by
  intro z
  refine ⟨∑ j : Fin 8, (circularPeirceBasis.equivFun z j) • fockPreimageBasis j, ?_⟩
  rw [map_sum]
  simp_rw [map_smul, fockToZorn_preimageBasis]
  exact circularPeirceBasis.sum_equivFun z

instance cz_finiteDimensional : FiniteDimensional ℝ CZ :=
  Module.Basis.finiteDimensional_of_finite circularPeirceBasis

theorem cz_finrank : Module.finrank ℝ CZ = 8 := by
  rw [Module.finrank_eq_card_basis circularPeirceBasis]
  exact Fintype.card_fin 8

/-- Equal finite dimensions turn the explicit surjection into a bijection. -/
theorem fockToZorn_injective : Function.Injective fockToZorn := by
  have hdim : Module.finrank ℝ Exterior3 = Module.finrank ℝ CZ := by
    rw [exterior3_finrank, cz_finrank]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    fockToZorn_surjective

/-- Genuine Fock/BdG linear equivalence generated by the right-regular CAR
representation and vacuum. -/
noncomputable def fockBdGEquiv : Exterior3 ≃ₗ[ℝ] CZ :=
  LinearEquiv.ofBijective fockToZorn ⟨fockToZorn_injective, fockToZorn_surjective⟩

@[simp] theorem fockBdGEquiv_apply (ψ : Exterior3) :
    fockBdGEquiv ψ = fockToZorn ψ := rfl

/-- Exact global creation intertwiner. -/
theorem fockBdGEquiv_creation_intertwines (i : Fin 3) :
    rightRegular (rootPlus i) ∘ₗ fockBdGEquiv.toLinearMap =
      fockBdGEquiv.toLinearMap ∘ₗ exteriorWedge3 (modeVector i) := by
  apply LinearMap.ext
  intro ψ
  exact (fockToZorn_creation_mode i ψ).symm

/-- Exact global annihilation intertwiner. -/
theorem fockBdGEquiv_annihilation_intertwines (i : Fin 3) :
    rightRegular (rootMinus i) ∘ₗ fockBdGEquiv.toLinearMap =
      fockBdGEquiv.toLinearMap ∘ₗ exteriorContract3 (modeCovector i) := by
  apply LinearMap.ext
  intro ψ
  exact (fockToZorn_annihilation i ψ).symm

/-- Conjugating literal exterior creation by the Fock/BdG equivalence is
exactly right-regular multiplication by the positive circular root. -/
theorem fockBdG_conjugates_creation (i : Fin 3) :
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        fockBdGEquiv (exteriorWedge3 (modeVector i)) =
      rightRegular (rootPlus i) := by
  apply LinearMap.ext
  intro x
  change fockBdGEquiv
      (exteriorWedge3 (modeVector i) (fockBdGEquiv.symm x)) =
    rightRegular (rootPlus i) x
  rw [fockBdGEquiv_apply, fockToZorn_creation_mode,
    fockBdGEquiv.apply_symm_apply]

/-- Conjugating literal exterior annihilation by the same equivalence is
exactly right-regular multiplication by the negative circular root. -/
theorem fockBdG_conjugates_annihilation (i : Fin 3) :
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        fockBdGEquiv (exteriorContract3 (modeCovector i)) =
      rightRegular (rootMinus i) := by
  apply LinearMap.ext
  intro x
  change fockBdGEquiv
      (exteriorContract3 (modeCovector i) (fockBdGEquiv.symm x)) =
    rightRegular (rootMinus i) x
  rw [fockBdGEquiv_apply, fockToZorn_annihilation,
    fockBdGEquiv.apply_symm_apply]

/-- Final CAR/BdG operator packet. -/
theorem fockBdG_operator_packet (i : Fin 3) :
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        fockBdGEquiv (exteriorWedge3 (modeVector i)) = rightRegular (rootPlus i) ∧
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        fockBdGEquiv (exteriorContract3 (modeCovector i)) = rightRegular (rootMinus i) :=
  ⟨fockBdG_conjugates_creation i, fockBdG_conjugates_annihilation i⟩

end InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

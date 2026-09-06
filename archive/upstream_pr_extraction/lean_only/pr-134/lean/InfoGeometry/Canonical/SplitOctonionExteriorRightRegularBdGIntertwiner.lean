import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
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
open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev V3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.V3
abbrev CZ :=
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn
abbrev Coord8 := Fin 8 → ℝ
abbrev EndCZ := Module.End ℝ CZ

/-! ## The signed coordinate realization -/

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

def bdgCoordinateSignEquiv : Coord8 ≃ₗ[ℝ] Coord8 where
  toFun x i := bdgSign i * x i
  invFun x i := bdgSign i * x i
  left_inv x := by
    funext i
    change bdgSign i * (bdgSign i * x i) = x i
    rw [← mul_assoc, bdgSign_sq, one_mul]
  right_inv x := by
    funext i
    change bdgSign i * (bdgSign i * x i) = x i
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
      (bdgSign i : ℝ) • (Pi.single i (1 : ℝ) : Coord8) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [bdgCoordinateSignEquiv, Pi.single_apply]
  · simp [bdgCoordinateSignEquiv, Pi.single_apply, h]

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
  change circularPeirceBasis j =
    (bdgSign j * bdgSign j) • circularPeirceBasis j
  rw [bdgSign_sq]
  simp

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

noncomputable def rootPlusLinear : V3 →ₗ[ℝ] CZ where
  toFun v := ∑ i : Fin 3, v i • rootPlus i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul,
      smul_eq_mul]

@[simp] theorem rootPlusLinear_modeVector (i : Fin 3) :
    rootPlusLinear (modeVector i) = rootPlus i := by
  fin_cases i <;>
    simp [rootPlusLinear, modeVector, Fin.sum_univ_three, Pi.single_apply]

private theorem smul_mul_smul_anticommutator_zero
    (a b : ℝ) (x y : CZ) (hxy : x * y + y * x = 0) :
    (a • x) * (b • y) + (b • y) * (a • x) = 0 := by
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
  simp only [smul_smul]
  calc
    (a * b) • (x * y) + (b * a) • (y * x) =
        (a * b) • (x * y + y * x) := by module
    _ = 0 := by rw [hxy, smul_zero]

private theorem smul_sq_zero
    (a : ℝ) (x : CZ) (hx : x * x = 0) :
    (a • x) * (a • x) = 0 := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hx, smul_zero]

private theorem add_three_sq_zero
    (x y z : CZ)
    (hx : x * x = 0) (hy : y * y = 0) (hz : z * z = 0)
    (hxy : x * y + y * x = 0)
    (hxz : x * z + z * x = 0)
    (hyz : y * z + z * y = 0) :
    (x + y + z) * (x + y + z) = 0 := by
  calc
    (x + y + z) * (x + y + z) =
          (x * x + y * y + z * z) +
          (x * y + y * x) + (x * z + z * x) + (y * z + z * y) := by
      simp only [add_mul, mul_add, add_assoc, add_left_comm, add_comm]
    _ = 0 := by rw [hx, hy, hz, hxy, hxz, hyz]; simp

theorem rootPlusLinear_sq_zero (v : V3) :
    rootPlusLinear v * rootPlusLinear v = (0 : CZ) := by
  simp only [rootPlusLinear, Fin.sum_univ_three, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  have h01 := rootPlus_mul_rootPlus_anticommutator (0 : Fin 3) (1 : Fin 3)
  have h02 := rootPlus_mul_rootPlus_anticommutator (0 : Fin 3) (2 : Fin 3)
  have h10 := rootPlus_mul_rootPlus_anticommutator (1 : Fin 3) (0 : Fin 3)
  have h12 := rootPlus_mul_rootPlus_anticommutator (1 : Fin 3) (2 : Fin 3)
  have h20 := rootPlus_mul_rootPlus_anticommutator (2 : Fin 3) (0 : Fin 3)
  have h21 := rootPlus_mul_rootPlus_anticommutator (2 : Fin 3) (1 : Fin 3)
  have h01' := smul_mul_smul_anticommutator_zero (v 0) (v 1)
    (rootPlus 0) (rootPlus 1) h01
  have h02' := smul_mul_smul_anticommutator_zero (v 0) (v 2)
    (rootPlus 0) (rootPlus 2) h02
  have h12' := smul_mul_smul_anticommutator_zero (v 1) (v 2)
    (rootPlus 1) (rootPlus 2) h12
  apply add_three_sq_zero
  · exact smul_sq_zero (v 0) (rootPlus 0) (rootPlus_sq_zero 0)
  · exact smul_sq_zero (v 1) (rootPlus 1) (rootPlus_sq_zero 1)
  · exact smul_sq_zero (v 2) (rootPlus 2) (rootPlus_sq_zero 2)
  · exact h01'
  · exact h02'
  · exact h12'

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

noncomputable def rightCreationMap : V3 →ₗ[ℝ] EndCZ :=
  rightRegularLinear.comp rootPlusLinear

@[simp] theorem rightCreationMap_modeVector (i : Fin 3) :
    rightCreationMap (modeVector i) = rightRegular (rootPlus i) := by
  simp [rightCreationMap, rightRegularLinear]

theorem rightCreationMap_sq_zero (v : V3) :
    rightCreationMap v * rightCreationMap v = (0 : EndCZ) := by
  change rightRegular (rootPlusLinear v) * rightRegular (rootPlusLinear v) = 0
  exact rightRegular_sq_zero_of_sq_zero (rootPlusLinear v) (rootPlusLinear_sq_zero v)

noncomputable def rightCreationRepresentation : Exterior3 →ₐ[ℝ] EndCZ :=
  ExteriorAlgebra.lift ℝ ⟨rightCreationMap, fun v => rightCreationMap_sq_zero v⟩

@[simp] theorem rightCreationRepresentation_ι (v : V3) :
    rightCreationRepresentation (ExteriorAlgebra.ι ℝ v) = rightCreationMap v := by
  simp [rightCreationRepresentation]

@[simp] theorem rightCreationRepresentation_ι_mode (i : Fin 3) :
    rightCreationRepresentation (ExteriorAlgebra.ι ℝ (modeVector i)) =
      rightRegular (rootPlus i) := by
  rw [rightCreationRepresentation_ι, rightCreationMap_modeVector]

noncomputable def fockToZorn : Exterior3 →ₗ[ℝ] CZ where
  toFun ψ := rightCreationRepresentation ψ uPlus
  map_add' ψ ξ := by simp
  map_smul' c ψ := by simp

@[simp] theorem fockToZorn_one : fockToZorn (1 : Exterior3) = uPlus := by
  simp [fockToZorn]

@[simp] theorem fockToZorn_algebraMap (r : ℝ) :
    fockToZorn (algebraMap ℝ Exterior3 r) = r • uPlus := by
  simp [fockToZorn]

theorem fockToZorn_creation (v : V3) (ψ : Exterior3) :
    fockToZorn (exteriorWedge3 v ψ) =
      rightCreationMap v (fockToZorn ψ) := by
  change rightCreationRepresentation (ExteriorAlgebra.ι ℝ v * ψ) uPlus = _
  rw [map_mul, rightCreationRepresentation_ι]
  rfl

theorem fockToZorn_creation_mode (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (exteriorWedge3 (modeVector i) ψ) =
      rightRegular (rootPlus i) (fockToZorn ψ) := by
  rw [fockToZorn_creation, rightCreationMap_modeVector]

/-- Mixed CAR with an arbitrary creation vector, obtained by linearity from the
full three-mode delta packet. -/
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
    simp [rootPlusLinear, rightRegular_apply, Finset.mul_sum, mul_smul_comm]
  rw [hv]
  calc
    rightRegular (rootMinus i) *
          (∑ j : Fin 3, v j • rightRegular (rootPlus j)) +
        (∑ j : Fin 3, v j • rightRegular (rootPlus j)) *
          rightRegular (rootMinus i) =
      ∑ j : Fin 3, v j •
        (rightRegular (rootMinus i) * rightRegular (rootPlus j) +
          rightRegular (rootPlus j) * rightRegular (rootMinus i)) := by
            rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [mul_smul_comm, smul_mul_assoc, smul_add]
    _ = ∑ j : Fin 3, v j •
        ((if i = j then (1 : ℝ) else 0) • (1 : EndCZ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [rightRegular_root_anticommutator j i]
          by_cases h : i = j
          · simp [h, smul_add, smul_smul]
          · have h' : ¬ j = i := by
              intro hji
              exact h hji.symm
            simp [h, h', smul_add, smul_smul]
    _ = (modeCovector i v) • (1 : EndCZ) := by
          fin_cases i <;>
            simp [Fin.sum_univ_three, modeCovector, smul_smul]

theorem fockToZorn_annihilation (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (exteriorContract3 (modeCovector i) ψ) =
      rightRegular (rootMinus i) (fockToZorn ψ) := by
  refine CliffordAlgebra.left_induction (Q := (0 : QuadraticForm ℝ V3)) ?_ ?_ ?_ ψ
  · intro r
    rw [show exteriorContract3 (modeCovector i)
        (algebraMap ℝ Exterior3 r) = 0 by simp [exteriorContract3]]
    rw [map_zero, fockToZorn_algebraMap]
    change 0 = (r • uPlus) * rootMinus i
    rw [smul_mul_assoc, uPlus_mul_rootMinus i, smul_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro x v hx
    rw [← exteriorWedge3_apply]
    rw [exteriorContract3_wedge3_apply]
    rw [map_sub, map_smul, fockToZorn_creation]
    rw [hx]
    conv_rhs => rw [fockToZorn_creation]
    have hcar := LinearMap.congr_fun (rightAnnihilation_creationMap_CAR i v)
      (fockToZorn x)
    simp only [Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply] at hcar
    simpa [rightCreationMap, rightRegular_apply] using
      ((eq_sub_iff_add_eq).2 hcar).symm

/-! ## Explicit preimages and bijectivity -/

private def ιMode (i : Fin 3) : Exterior3 :=
  ExteriorAlgebra.ι ℝ (modeVector i)

theorem fockToZorn_ιMode (i : Fin 3) :
    fockToZorn (ιMode i) =
      rightRegular (rootPlus i) (fockToZorn (1 : Exterior3)) := by
  simpa [ιMode, exteriorWedge3] using
    (fockToZorn_creation_mode i (1 : Exterior3))

def fockPreimageBasis : Fin 8 → Exterior3
  | 0 => 1
  | 1 => ιMode 0
  | 2 => ιMode 1
  | 3 => ιMode 2
  | 4 => -(ιMode 0 * (ιMode 1 * ιMode 2))
  | 5 => -(ιMode 1 * ιMode 2)
  | 6 => ιMode 0 * ιMode 2
  | 7 => -(ιMode 0 * ιMode 1)

private theorem rightRegular_rootPlus012_uPlus :
    rightRegular (rootPlus 0)
        (rightRegular (rootPlus 1)
          (rightRegular (rootPlus 2) uPlus)) = -uMinus := by
  change ((uPlus * rootPlus 2) * rootPlus 1) * rootPlus 0 = -uMinus
  rw [uPlus_mul_rootPlus 2, rootPlus_two_mul_rootPlus_one, neg_mul,
    rootMinus_mul_rootPlus_delta]
  simp [uPlus_add_uMinus]

private theorem fock_basis_prod_4 :
    ((uPlus * rootPlus 2) * rootPlus 1) * rootPlus 0 = -uMinus := by
  rw [uPlus_mul_rootPlus, rootPlus_two_mul_rootPlus_one]
  simp only [neg_mul]
  rw [rootMinus_mul_rootPlus_delta]
  rfl

private theorem zornMul_rootMinus_rootPlus (i j : Fin 3) :
    rootMinus i * rootPlus j = (if i = j then uMinus else 0) := by
  exact rootMinus_mul_rootPlus_delta i j

private theorem fock_basis_prod_5 :
    (uPlus * rootPlus 2) * rootPlus 1 = -rootMinus 0 := by
  rw [uPlus_mul_rootPlus, rootPlus_two_mul_rootPlus_one]

private theorem fock_basis_prod_6 :
    (uPlus * rootPlus 2) * rootPlus 0 = rootMinus 1 := by
  rw [uPlus_mul_rootPlus, rootPlus_two_mul_rootPlus_zero]

private theorem fock_basis_prod_7 :
    (uPlus * rootPlus 1) * rootPlus 0 = -rootMinus 2 := by
  rw [uPlus_mul_rootPlus, rootPlus_one_mul_rootPlus_zero]

theorem fockToZorn_ιMode_mul (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (ιMode i * ψ) =
      rightRegular (rootPlus i) (fockToZorn ψ) := by
  change rightCreationRepresentation (ιMode i * ψ) uPlus = _
  change rightCreationRepresentation
    (ExteriorAlgebra.ι ℝ (modeVector i) * ψ) uPlus = _
  rw [map_mul, rightCreationRepresentation_ι_mode]
  rfl

@[simp] theorem fockToZorn_preimageBasis (j : Fin 8) :
    fockToZorn (fockPreimageBasis j) = circularPeirceBasis j := by
  fin_cases j
  · simp [fockPreimageBasis, frame, circularPeirceBasis_zero]
  · simp only [fockPreimageBasis]
    rw [fockToZorn_ιMode]
    simpa [fockToZorn_one, circularPeirceBasis_one, frame, rightRegular_apply] using
      (uPlus_mul_rootPlus 0)
  · simp only [fockPreimageBasis]
    rw [fockToZorn_ιMode]
    simpa [fockToZorn_one, circularPeirceBasis_two, frame, rightRegular_apply] using
      (uPlus_mul_rootPlus 1)
  · simp only [fockPreimageBasis]
    rw [fockToZorn_ιMode]
    simpa [fockToZorn_one, circularPeirceBasis_three, frame, rightRegular_apply] using
      (uPlus_mul_rootPlus 2)
  · simp only [fockPreimageBasis, map_neg]
    rw [fockToZorn_ιMode_mul, fockToZorn_ιMode_mul, fockToZorn_ιMode]
    rw [fockToZorn_one]
    simp only [rightRegular_apply]
    change -(((uPlus * rootPlus 2) * rootPlus 1) * rootPlus 0) = _
    simp [circularPeirceBasis_apply, frame]
    rw [← neg_neg uMinus]
    exact congrArg (fun x : CZ => -x) fock_basis_prod_4
  · simp only [fockPreimageBasis, map_neg]
    rw [fockToZorn_ιMode_mul, fockToZorn_ιMode]
    rw [fockToZorn_one]
    simp only [rightRegular_apply]
    change -((uPlus * rootPlus 2) * rootPlus 1) = _
    simp [circularPeirceBasis_apply, frame]
    rw [← neg_neg (rootMinus 0)]
    exact congrArg (fun x : CZ => -x) fock_basis_prod_5
  · simp only [fockPreimageBasis]
    rw [fockToZorn_ιMode_mul, fockToZorn_ιMode]
    rw [fockToZorn_one]
    change (uPlus * rootPlus 2) * rootPlus 0 = circularPeirceBasis (6 : Fin 8)
    rw [circularPeirceBasis_six]
    exact fock_basis_prod_6
  · simp only [fockPreimageBasis, map_neg]
    rw [fockToZorn_ιMode_mul, fockToZorn_ιMode]
    rw [fockToZorn_one]
    change -((uPlus * rootPlus 1) * rootPlus 0) = circularPeirceBasis (7 : Fin 8)
    simp [circularPeirceBasis_apply, frame]
    rw [← neg_neg (rootMinus 2)]
    exact congrArg (fun x : CZ => -x) fock_basis_prod_7

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

theorem fockToZorn_injective : Function.Injective fockToZorn := by
  have hdim : Module.finrank ℝ Exterior3 = Module.finrank ℝ CZ := by
    rw [exterior3_finrank, cz_finrank]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    fockToZorn_surjective

noncomputable def fockBdGEquiv : Exterior3 ≃ₗ[ℝ] CZ :=
  LinearEquiv.ofBijective fockToZorn ⟨fockToZorn_injective, fockToZorn_surjective⟩

@[simp] theorem fockBdGEquiv_apply (ψ : Exterior3) :
    fockBdGEquiv ψ = fockToZorn ψ := rfl

@[simp] theorem fockToZorn_symm_apply (x : CZ) :
    fockToZorn (fockBdGEquiv.symm x) = x := by
  change fockBdGEquiv (fockBdGEquiv.symm x) = x
  exact fockBdGEquiv.apply_symm_apply x

theorem fockBdGEquiv_creation_intertwines (i : Fin 3) :
    rightRegular (rootPlus i) ∘ₗ fockBdGEquiv.toLinearMap =
      fockBdGEquiv.toLinearMap ∘ₗ exteriorWedge3 (modeVector i) := by
  apply LinearMap.ext
  intro ψ
  simpa [fockBdGEquiv_apply] using (fockToZorn_creation_mode i ψ).symm

theorem fockBdGEquiv_annihilation_intertwines (i : Fin 3) :
    rightRegular (rootMinus i) ∘ₗ fockBdGEquiv.toLinearMap =
      fockBdGEquiv.toLinearMap ∘ₗ exteriorContract3 (modeCovector i) := by
  apply LinearMap.ext
  intro ψ
  simpa [fockBdGEquiv_apply] using (fockToZorn_annihilation i ψ).symm

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
    fockToZorn_symm_apply]

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
    fockToZorn_symm_apply]

theorem fockBdG_operator_packet (i : Fin 3) :
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        fockBdGEquiv (exteriorWedge3 (modeVector i)) = rightRegular (rootPlus i) ∧
    InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport.transportEndGeneric
        fockBdGEquiv (exteriorContract3 (modeCovector i)) = rightRegular (rootMinus i) :=
  ⟨fockBdG_conjugates_creation i, fockBdG_conjugates_annihilation i⟩

end InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner

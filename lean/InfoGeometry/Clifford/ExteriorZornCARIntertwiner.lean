import InfoGeometry.Clifford.ExteriorNegativeCliffordReflection
import InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
import InfoGeometry.Algebra.KingdonSplitOctonion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Exterior Fock space and the Zorn left-regular CAR representation

This map is defined by the exterior algebra universal property and the actual
left regular creation operators, evaluated on the lower Peirce vacuum vector.
Its intertwining properties are proved, not supplied as interface assumptions.

The exterior product is not identified with the Zorn product. The universal
algebra homomorphism takes values in the associative endomorphism algebra.
The resulting map of state carriers is linear and bijective.
-/

noncomputable section

set_option maxHeartbeats 1200000

namespace InfoGeometry.Clifford.ExteriorZornCARIntertwiner

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

local notation "Zorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "U" => InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ)
local notation "V" => InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis (R := ℝ)
local notation "polePlus" => InfoGeometry.Canonical.ZornMatrix.zornPlus (R := ℝ)
local notation "poleMinus" => InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)

/-- The whole native upper-vector Peirce slot as a linear map. -/
def upperVector : V3 →ₗ[ℝ] Zorn where
  toFun v := { a := 0, b := 0, x := v, y := 0 }
  map_add' v w := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;> simp
  map_smul' r v := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · change 0 = r * 0
      ring
    · change 0 = r * 0
      ring
    · funext k
      change r * v k = r * v k
      rfl
    · funext k
      change 0 = r * 0
      ring

/-- The three-mode regular creation map. -/
def creationMap : V3 →ₗ[ℝ] Module.End ℝ Zorn where
  toFun v := L (upperVector v)
  map_add' v w := by rw [map_add, L_add]
  map_smul' r v := by
    simpa using (L_smul r (upperVector v))

@[simp] theorem creationMap_basis (i : Fin 3) :
    creationMap (Pi.single i 1) = create i := rfl

theorem upperVector_sq (v : V3) : upperVector v * upperVector v = (0 : Zorn) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [upperVector, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals ring

theorem creationMap_sq (v : V3) : creationMap v * creationMap v = 0 := by
  change L (upperVector v) * L (upperVector v) = 0
  rw [regular_square, upperVector_sq, L_zero]

/-- Native exterior algebra lift into ASSOCIATIVE regular operators. -/
def creationLift : Exterior3 →ₐ[ℝ] Module.End ℝ Zorn :=
  CliffordAlgebra.lift (0 : QuadraticForm ℝ V3) ⟨creationMap, by
    intro v
    rw [creationMap_sq]
    simp⟩

@[simp] theorem creationLift_ι (v : V3) :
    creationLift (ExteriorAlgebra.ι ℝ v) = creationMap v := by
  exact CliffordAlgebra.lift_ι_apply _ _ _

/-- Evaluate the exterior creation representation on its actual vacuum vector. -/
def fockToZorn : Exterior3 →ₗ[ℝ] Zorn where
  toFun ψ := creationLift ψ poleMinus
  map_add' ψ χ := by simp
  map_smul' r ψ := by simp

@[simp] theorem fockToZorn_one : fockToZorn (1 : Exterior3) = poleMinus := by
  simp [fockToZorn]

/-- Every creation operator is intertwined, on every exterior state. -/
theorem fockToZorn_wedge (v : V3) (ψ : Exterior3) :
    fockToZorn (exteriorWedge3 v ψ) = creationMap v (fockToZorn ψ) := by
  change creationLift (ExteriorAlgebra.ι ℝ v * ψ) poleMinus = _
  rw [map_mul, Module.End.mul_apply, creationLift_ι]
  rfl

private theorem mixed_vector_raw (j : Fin 3) (v : V3) :
    V j * upperVector v + upperVector v * V j = v j • (1 : Zorn) := by
  fin_cases j
  all_goals apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [upperVector, InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply]
  all_goals
    simp only [InfoGeometry.Canonical.ZornMatrix.smul_a,
      InfoGeometry.Canonical.ZornMatrix.smul_b,
      InfoGeometry.Canonical.ZornMatrix.smul_x,
      InfoGeometry.Canonical.ZornMatrix.smul_y]
    simp
  all_goals ring

theorem creationMap_annihilate (j : Fin 3) (v : V3) :
    annihilate j * creationMap v + creationMap v * annihilate j =
      v j • (1 : Module.End ℝ Zorn) := by
  change L (V j) * L (upperVector v) + L (upperVector v) * L (V j) = _
  rw [regular_anticommutator, mixed_vector_raw, L_smul, L_one]

/-- Every native coordinate contraction is intertwined, not just its vacuum value. -/
theorem fockToZorn_contract (j : Fin 3) (ψ : Exterior3) :
    fockToZorn (exteriorContract3 (LinearMap.proj j) ψ) =
      annihilate j (fockToZorn ψ) := by
  refine CliffordAlgebra.left_induction (Q := (0 : QuadraticForm ℝ V3)) ?_ ?_ ?_ ψ
  · intro r
    have hVac := (regular_vacuum j).1
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [exteriorContract3, fockToZorn, hVac,
        InfoGeometry.Canonical.ZornMatrix.smul_a]
    · simp [exteriorContract3, fockToZorn, hVac,
        InfoGeometry.Canonical.ZornMatrix.smul_b]
    · funext k
      simp [exteriorContract3, fockToZorn, hVac,
        InfoGeometry.Canonical.ZornMatrix.smul_x]
    · funext k
      simp [exteriorContract3, fockToZorn, hVac,
        InfoGeometry.Canonical.ZornMatrix.smul_y]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro x v hx
    change fockToZorn (exteriorContract3 (LinearMap.proj j) (exteriorWedge3 v x)) = _
    rw [exteriorContract3_wedge3_apply, map_sub, map_smul, fockToZorn_wedge, hx]
    have h := congrArg (fun T : Module.End ℝ Zorn => T (fockToZorn x))
      (creationMap_annihilate j v)
    change annihilate j (creationMap v (fockToZorn x)) +
      creationMap v (annihilate j (fockToZorn x)) = v j • fockToZorn x at h
    change v j • fockToZorn x - creationMap v (annihilate j (fockToZorn x)) =
      annihilate j (fockToZorn (exteriorWedge3 v x))
    rw [fockToZorn_wedge]
    exact (eq_sub_of_add_eq h).symm

/-- Explicit preimage assembled from vacuum, singles, doubles, and the triple. -/
def fockPreimage (X : Zorn) : Exterior3 :=
  let e (i : Fin 3) := ExteriorAlgebra.ι ℝ (Pi.single i 1 : V3)
  X.b • 1 + X.x 0 • e 0 + X.x 1 • e 1 + X.x 2 • e 2 +
    X.y 0 • (e 1 * e 2) - X.y 1 • (e 0 * e 2) +
    X.y 2 • (e 0 * e 1) + X.a • (e 0 * e 1 * e 2)

/-- The preimage is checked against native Zorn multiplication with its actual signs. -/
theorem fockToZorn_preimage (X : Zorn) : fockToZorn (fockPreimage X) = X := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [fockPreimage, fockToZorn, map_add, map_sub, map_smul,
    map_mul, Module.End.mul_apply, creationMap_basis, create, L_apply,
    InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
    InfoGeometry.Canonical.ZornMatrix.zornMinus,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply]
  all_goals
    simp only [InfoGeometry.Canonical.ZornMatrix.smul_a,
      InfoGeometry.Canonical.ZornMatrix.smul_b,
      InfoGeometry.Canonical.ZornMatrix.smul_x,
      InfoGeometry.Canonical.ZornMatrix.smul_y]
    simp
    try ring

/-- Surjectivity is proved by the displayed explicit inverse formula. -/
theorem fockToZorn_surjective : Function.Surjective fockToZorn := by
  intro X
  exact ⟨fockPreimage X, fockToZorn_preimage X⟩

/-- Use the native exterior basis directly, avoiding the separate finite Peirce reindex proof. -/
theorem fockToZorn_injective : Function.Injective fockToZorn := by
  let zornFin8 : Zorn ≃ₗ[ℝ] (Fin 8 → ℝ) :=
    { toFun := fun X => ![X.a, X.b, X.x 0, X.x 1, X.x 2, X.y 0, X.y 1, X.y 2]
      invFun := fun c =>
        (⟨c 0, c 1, ![c 2, c 3, c 4], ![c 5, c 6, c 7]⟩ : Zorn)
      left_inv := by
        intro X
        apply InfoGeometry.Canonical.ZornMatrix.ext
        · rfl
        · rfl
        · funext i; fin_cases i <;> rfl
        · funext i; fin_cases i <;> rfl
      right_inv := by intro c; funext i; fin_cases i <;> rfl
      map_add' := by intro X Y; funext i; fin_cases i <;> rfl
      map_smul' := by intro r X; funext i; fin_cases i <;> rfl }
  let bZ : Module.Basis (Fin 8) ℝ Zorn :=
    (Pi.basisFun ℝ (Fin 8)).map zornFin8.symm
  letI : FiniteDimensional ℝ Exterior3 :=
    Module.Basis.finiteDimensional_of_finite exterior3BasisFinset
  letI : FiniteDimensional ℝ Zorn := Module.Basis.finiteDimensional_of_finite bZ
  have hdim : Module.finrank ℝ Exterior3 = Module.finrank ℝ Zorn := by
    rw [Module.finrank_eq_card_basis exterior3BasisFinset, Module.finrank_eq_card_basis bZ]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    fockToZorn_surjective

/-- A genuine state-space equivalence intertwining both sets of CAR operators. -/
def exteriorZornCARLinearEquiv : Exterior3 ≃ₗ[ℝ] Zorn :=
  LinearEquiv.ofBijective fockToZorn ⟨fockToZorn_injective, fockToZorn_surjective⟩

/-- Parity on this regular Fock model: the lower pole is even and the upper pole odd. -/
def regularParity : Module.End ℝ Zorn := L poleMinus - L polePlus

theorem regularParity_apply (X : Zorn) : regularParity X =
    { a := -X.a, b := X.b, x := -X.x, y := X.y } := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [regularParity, L_apply, InfoGeometry.Canonical.ZornMatrix.zornPlus,
    InfoGeometry.Canonical.ZornMatrix.zornMinus, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]

private theorem parity_creation (v : V3) (X : Zorn) :
    regularParity (creationMap v X) = -creationMap v (regularParity X) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [creationMap, regularParity_apply, upperVector, L_apply,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross] <;> ring

/-- Exterior even/odd degree is intertwined with the proved regular-action parity. -/
theorem fockToZorn_parity (ψ : Exterior3) :
    fockToZorn (exteriorGrade3 ψ) = regularParity (fockToZorn ψ) := by
  refine CliffordAlgebra.left_induction (Q := (0 : QuadraticForm ℝ V3)) ?_ ?_ ?_ ψ
  · intro r
    simp [fockToZorn, regularParity_apply, InfoGeometry.Canonical.ZornMatrix.zornMinus]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro x v hx
    change fockToZorn (exteriorGrade3 (exteriorWedge3 v x)) = _
    rw [exteriorGrade3_wedge, map_neg, fockToZorn_wedge, hx]
    change -(creationMap v (regularParity (fockToZorn x))) =
      regularParity (fockToZorn (exteriorWedge3 v x))
    rw [fockToZorn_wedge, parity_creation]

/-- The actual Fock equivalence in the repository's circular operator coordinates. -/
def exteriorCircularCARLinearEquiv : Exterior3 ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  exteriorZornCARLinearEquiv.trans circularCoordinateLinearEquiv

private theorem circularReadout_apply (T : Module.End ℝ Zorn) (X : Zorn) :
    circularOperatorReadout T (circularCoordinateLinearEquiv X) =
      circularCoordinateLinearEquiv (T X) := by
  simp [circularOperatorReadout, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

/-- The circular matrices are now intertwined with genuine wedge creation. -/
theorem circular_creation_intertwiner (v : V3) (ψ : Exterior3) :
    exteriorCircularCARLinearEquiv (exteriorWedge3 v ψ) =
      circularOperatorReadout (creationMap v) (exteriorCircularCARLinearEquiv ψ) := by
  change circularCoordinateLinearEquiv (fockToZorn (exteriorWedge3 v ψ)) =
    circularOperatorReadout (creationMap v) (circularCoordinateLinearEquiv (fockToZorn ψ))
  rw [fockToZorn_wedge, circularReadout_apply]

/-- The same map also intertwines annihilation on all states. -/
theorem circular_annihilation_intertwiner (j : Fin 3) (ψ : Exterior3) :
    exteriorCircularCARLinearEquiv (exteriorContract3 (LinearMap.proj j) ψ) =
      circularOperatorReadout (annihilate j) (exteriorCircularCARLinearEquiv ψ) := by
  change circularCoordinateLinearEquiv (fockToZorn (exteriorContract3 (LinearMap.proj j) ψ)) =
    circularOperatorReadout (annihilate j) (circularCoordinateLinearEquiv (fockToZorn ψ))
  rw [fockToZorn_contract, circularReadout_apply]

/-- Exterior even/odd degree agrees with the transported regular Fock parity. -/
theorem circular_parity_intertwiner (ψ : Exterior3) :
    exteriorCircularCARLinearEquiv (exteriorGrade3 ψ) =
      circularOperatorReadout regularParity (exteriorCircularCARLinearEquiv ψ) := by
  change circularCoordinateLinearEquiv (fockToZorn (exteriorGrade3 ψ)) =
    circularOperatorReadout regularParity (circularCoordinateLinearEquiv (fockToZorn ψ))
  rw [fockToZorn_parity, circularReadout_apply]

end InfoGeometry.Clifford.ExteriorZornCARIntertwiner

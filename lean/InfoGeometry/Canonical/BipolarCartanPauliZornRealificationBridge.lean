import InfoGeometry.Canonical.BipolarPauliZornPristineChain
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
import Mathlib.Tactic

/-!
# Realification of the bipolar Cartan--Pauli--Zorn chain

The preceding canonical owners already establish the intrinsic finite chain:

* `BipolarComplexCartanLine` identifies the trace-zero complex Cartan line;
* `BipolarPauliHestenesSolderingBridge` proves the actual four-entry Cartan
  action on the Hermitian Pauli matrix and the real/complex rank distinction;
* `BipolarPauliZornWittBridge` proves equality of the Pauli determinant, the
  corrected real Zorn norm, and the circular `(4,4)` Witt diagonal form;
* `BipolarPauliZornPristineChain` packages those results without asserting an
  algebra equivalence between the associative and nonassociative carriers.

This file adds only the missing realification layer. The repository-owned
injective ring map `realify : M₂(ℂ) → M₄(ℝ)` sends scalar multiplication by
`I` to a concrete real complex structure `J` with `J² = -1`. It therefore
realizes the single complex Cartan line as a two-directional real plane while
preserving multiplication, inverse identities, and the double-sided Pauli
action.

The matrix `J` is a finite realification of the scalar complex phase. No claim
is made that it is already a constructed grade-four pseudoscalar in a concrete
`Cl(1,3)` algebra, nor that the resulting real module is a Dirac or Nambu--Krein
module. Those are the next representation-theoretic frontiers.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarCartanPauliZornRealificationBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.BipolarComplexCartanLine
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
open InfoGeometry.Canonical.BipolarPauliZornWittBridge
open InfoGeometry.Canonical.BipolarPauliZornPristineChain
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Physics.ChiralCausalCone
open scoped Matrix

abbrev Matrix2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev Matrix4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-- Realification of the noncompact Cartan generator. -/
noncomputable def realifiedKboost : Matrix4R :=
  realify Kboost

/-- Realification of the compact Cartan generator. -/
noncomputable def realifiedKcirc : Matrix4R :=
  realify Kcirc

/-- Realification of the point-dependent logarithmic Cartan generator. -/
noncomputable def realifiedLogarithmicCartanGenerator
    (s : ℂ) : Matrix4R :=
  realify (bipolarLogarithmicCartan s)

/-- Multiplication by the real complex structure is exactly the realification
of multiplication by the scalar `I` on the complex Cartan line. -/
theorem realifiedKcirc_eq_complexStructure_mul_realifiedKboost :
    realifiedKcirc = complexStructure * realifiedKboost := by
  calc
    realifiedKcirc = realify (Complex.I • Kboost) := by
      unfold realifiedKcirc
      rw [Kcirc_eq_I_smul_Kboost]
    _ = realify (((Complex.I : ℂ) • (1 : Matrix2C)) * Kboost) := by
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Kboost, σ3c, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply]
    _ = realify ((Complex.I : ℂ) • (1 : Matrix2C)) * realify Kboost := by
      rw [realify_mul]
    _ = complexStructure * realifiedKboost := rfl

/-- Every realified complex matrix commutes with the real scalar-phase axis; in
particular this holds for the noncompact Cartan generator. -/
theorem realifiedKboost_commutes_complexStructure :
    realifiedKboost * complexStructure =
      complexStructure * realifiedKboost := by
  simpa [realifiedKboost] using
    realify_commutes_complexStructure Kboost

/-- Equivalent right-multiplication form of the compact Cartan generator. -/
theorem realifiedKcirc_eq_realifiedKboost_mul_complexStructure :
    realifiedKcirc = realifiedKboost * complexStructure := by
  calc
    realifiedKcirc = complexStructure * realifiedKboost :=
      realifiedKcirc_eq_complexStructure_mul_realifiedKboost
    _ = realifiedKboost * complexStructure :=
      realifiedKboost_commutes_complexStructure.symm

/-- Ring realification preserves the abelian Cartan commutator. -/
theorem realifiedKboost_Kcirc_commute :
    realifiedKboost * realifiedKcirc =
      realifiedKcirc * realifiedKboost := by
  have hcomm : Kboost * Kcirc = Kcirc * Kboost :=
    sub_eq_zero.mp Kboost_Kcirc_commute
  calc
    realifiedKboost * realifiedKcirc = realify (Kboost * Kcirc) := by
      simpa [realifiedKboost, realifiedKcirc] using
        (realify_mul Kboost Kcirc).symm
    _ = realify (Kcirc * Kboost) := by rw [hcomm]
    _ = realifiedKcirc * realifiedKboost := by
      simpa [realifiedKboost, realifiedKcirc] using
        realify_mul Kcirc Kboost

/-- Real scalar coordinates pass through realification exactly. -/
theorem realifiedLogarithmicCartanGenerator_split (s : ℂ) :
    realifiedLogarithmicCartanGenerator s =
      eta s • realifiedKboost + theta s • realifiedKcirc := by
  unfold realifiedLogarithmicCartanGenerator realifiedKboost realifiedKcirc
  simp only [bipolarLogarithmicCartan, logarithmicCartan,
    realify_add, realify_real_smul]

/-- Intrinsically real form of the coefficient `eta + I theta`. -/
theorem realifiedLogarithmicCartanGenerator_complexStructure_split (s : ℂ) :
    realifiedLogarithmicCartanGenerator s =
      eta s • realifiedKboost +
        theta s • (complexStructure * realifiedKboost) := by
  rw [realifiedLogarithmicCartanGenerator_split,
    realifiedKcirc_eq_complexStructure_mul_realifiedKboost]

/-- The realified logarithmic generator lies in the commutant of the real
complex structure. -/
theorem realifiedLogarithmicCartanGenerator_commutes_complexStructure
    (s : ℂ) :
    realifiedLogarithmicCartanGenerator s * complexStructure =
      complexStructure * realifiedLogarithmicCartanGenerator s := by
  simpa [realifiedLogarithmicCartanGenerator] using
    realify_commutes_complexStructure (bipolarLogarithmicCartan s)

/-- Realification of the finite half-log lift. -/
noncomputable def realifiedHalfLogLift (s : ℂ) : Matrix4R :=
  realify (halfLogLift s)

/-- Realification of the explicit two-sided inverse. -/
noncomputable def realifiedHalfLogLiftInv (s : ℂ) : Matrix4R :=
  realify (halfLogLiftInv s)

/-- The explicit right-inverse identity survives realification. -/
theorem realifiedHalfLogLift_mul_inv (s : ℂ) :
    realifiedHalfLogLift s * realifiedHalfLogLiftInv s = 1 := by
  calc
    realifiedHalfLogLift s * realifiedHalfLogLiftInv s =
        realify (halfLogLift s * halfLogLiftInv s) := by
      simpa [realifiedHalfLogLift, realifiedHalfLogLiftInv] using
        (realify_mul (halfLogLift s) (halfLogLiftInv s)).symm
    _ = realify 1 := by
      simpa [halfLogLiftInv] using
        congrArg realify (halfLogLift_mul_explicitInverse s)
    _ = 1 := realify_one

/-- The explicit left-inverse identity survives realification. -/
theorem realifiedHalfLogLift_inv_mul (s : ℂ) :
    realifiedHalfLogLiftInv s * realifiedHalfLogLift s = 1 := by
  calc
    realifiedHalfLogLiftInv s * realifiedHalfLogLift s =
        realify (halfLogLiftInv s * halfLogLift s) := by
      simpa [realifiedHalfLogLift, realifiedHalfLogLiftInv] using
        (realify_mul (halfLogLiftInv s) (halfLogLift s)).symm
    _ = realify 1 := by
      simpa [halfLogLiftInv] using
        congrArg realify (explicitInverse_mul_halfLogLift s)
    _ = 1 := realify_one

/-- The realified finite lift belongs to the complex-structure commutant. -/
theorem realifiedHalfLogLift_commutes_complexStructure (s : ℂ) :
    realifiedHalfLogLift s * complexStructure =
      complexStructure * realifiedHalfLogLift s := by
  simpa [realifiedHalfLogLift] using
    realify_commutes_complexStructure (halfLogLift s)

/-- Realification of the canonical Hermitian Pauli matrix. -/
noncomputable def realifiedPauliMatrix (P : PauliParavector) : Matrix4R :=
  realify P.pauliMatrix

/-- Realification of the bipolar double-sided Pauli action. -/
noncomputable def realifiedBipolarPauliAction
    (s : ℂ) (P : PauliParavector) : Matrix4R :=
  realify ((bipolarSolderingAction s (pauliHermitian P)).mat)

/-- Ring realification commutes with the complete double-sided Pauli action. -/
theorem realifiedBipolarPauliAction_factorization
    (s : ℂ) (P : PauliParavector) :
    realifiedBipolarPauliAction s P =
      realifiedHalfLogLift s * realifiedPauliMatrix P *
        realify (Matrix.conjTranspose (halfLogLift s)) := by
  change
    realify (halfLogLift s * (pauliHermitian P).mat *
      Matrix.conjTranspose (halfLogLift s)) =
      realify (halfLogLift s) * realify P.pauliMatrix *
        realify (Matrix.conjTranspose (halfLogLift s))
  rw [pauliHermitian_mat, realify_mul, realify_mul]

/-- The realified acted Pauli matrix remains in the complex-structure
commutant. -/
theorem realifiedBipolarPauliAction_commutes_complexStructure
    (s : ℂ) (P : PauliParavector) :
    realifiedBipolarPauliAction s P * complexStructure =
      complexStructure * realifiedBipolarPauliAction s P := by
  simpa [realifiedBipolarPauliAction] using
    realify_commutes_complexStructure
      ((bipolarSolderingAction s (pauliHermitian P)).mat)

/-- Consolidated finite chain: the previously proved Cartan--Pauli--Zorn packet
and its faithful real matrix realization. -/
theorem bipolar_cartan_pauli_zorn_realification_packet
    (s : ℂ) (P : PauliParavector) :
    (Kcirc = Complex.I • Kboost ∧
      (∀ a b : ℝ,
        (a : ℂ) • Kboost + (b : ℂ) • Kcirc = 0 →
          a = 0 ∧ b = 0) ∧
      bipolarLogarithmicCartan s ∈ cartanLine ∧
      Matrix.trace (bipolarLogarithmicCartan s) = 0 ∧
      (bipolarSolderingAction s (pauliHermitian P)).mat =
        matrixOfCartanCoordinates
          (bipolarCoordinateAction s (pauliCartanCoordinates P)) ∧
      InfoGeometry.Algebra.ZornMatrix.zornNorm (pauliZorn P) =
        P.minkowskiNormSq ∧
      circularWittQuadratic
          (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) =
        P.minkowskiNormSq ∧
      Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
        ((InfoGeometry.Algebra.ZornMatrix.zornNorm (pauliZorn P) : ℝ) : ℂ)) ∧
      realifiedKcirc = complexStructure * realifiedKboost ∧
      complexStructure * complexStructure = -(1 : Matrix4R) ∧
      realifiedLogarithmicCartanGenerator s =
        eta s • realifiedKboost +
          theta s • (complexStructure * realifiedKboost) ∧
      realifiedHalfLogLift s * realifiedHalfLogLiftInv s = 1 ∧
      realifiedBipolarPauliAction s P =
        realifiedHalfLogLift s * realifiedPauliMatrix P *
          realify (Matrix.conjTranspose (halfLogLift s)) := by
  exact ⟨bipolar_pauli_zorn_pristine_chain s P,
    realifiedKcirc_eq_complexStructure_mul_realifiedKboost,
    complexStructure_sq,
    realifiedLogarithmicCartanGenerator_complexStructure_split s,
    realifiedHalfLogLift_mul_inv s,
    realifiedBipolarPauliAction_factorization s P⟩

end InfoGeometry.Canonical.BipolarCartanPauliZornRealificationBridge

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
import InfoGeometry.Synthesis.SplitSedenionDerivationRepresentationSynthesis

/-!
# Parameter bracket for the concrete split-sedenion G₂ family

The bracket below is pulled back from the native commutator bracket on
`ZornVectorMatrix.Derivation`. The results concern the existing 14-parameter
family and its diagonal Cayley--Dickson lift. They do not classify all
split-sedenion derivations or assert a decomposition of their full derivation
algebra.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.SedenionG2ParameterBracket

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
open InfoGeometry.Synthesis.SplitSedenionDerivationRepresentationSynthesis
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-- Pull back the native derivation commutator to the fourteen coordinates. -/
def parameterBracket (p q : Params) : Params :=
  parameterLinearEquiv.symm
    (Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv q))

/-- The parameter bracket is read back as the native derivation bracket. -/
theorem parameterLinearEquiv_parameterBracket (p q : Params) :
    parameterLinearEquiv (parameterBracket p q) =
      Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv q) :=
  parameterLinearEquiv.apply_symm_apply _

private theorem parameterLinearEquiv_injective :
    Function.Injective parameterLinearEquiv :=
  parameterLinearEquiv.injective

/-- Skew symmetry transported from the native derivation commutator. -/
theorem parameterBracket_skew (p q : Params) :
    parameterBracket p q = - parameterBracket q p := by
  apply parameterLinearEquiv_injective
  rw [map_neg, parameterLinearEquiv_parameterBracket,
    parameterLinearEquiv_parameterBracket]
  exact Derivation.bracket_skew (parameterLinearEquiv p) (parameterLinearEquiv q)

/-- Additivity in the first parameter, transported from the native bracket. -/
theorem parameterBracket_add_left (p q r : Params) :
    parameterBracket (p + q) r =
      parameterBracket p r + parameterBracket q r := by
  apply parameterLinearEquiv_injective
  simp only [parameterLinearEquiv_parameterBracket, parameterLinearEquiv.map_add]
  change Derivation.bracket
      (Derivation.add (parameterLinearEquiv p) (parameterLinearEquiv q))
      (parameterLinearEquiv r) =
    Derivation.add
      (Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv r))
      (Derivation.bracket (parameterLinearEquiv q) (parameterLinearEquiv r))
  exact Derivation.bracket_add_left (parameterLinearEquiv p)
    (parameterLinearEquiv q) (parameterLinearEquiv r)

/-- Additivity in the second parameter, transported from the native bracket. -/
theorem parameterBracket_add_right (p q r : Params) :
    parameterBracket p (q + r) =
      parameterBracket p q + parameterBracket p r := by
  apply parameterLinearEquiv_injective
  simp only [parameterLinearEquiv_parameterBracket, parameterLinearEquiv.map_add]
  change Derivation.bracket (parameterLinearEquiv p)
      (Derivation.add (parameterLinearEquiv q) (parameterLinearEquiv r)) =
    Derivation.add
      (Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv q))
      (Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv r))
  exact Derivation.bracket_add_right (parameterLinearEquiv p)
    (parameterLinearEquiv q) (parameterLinearEquiv r)

/-- Real scalar linearity in the first parameter. -/
theorem parameterBracket_smul_left (a : ℝ) (p q : Params) :
    parameterBracket (a • p) q = a • parameterBracket p q := by
  apply parameterLinearEquiv_injective
  simp only [parameterLinearEquiv_parameterBracket, parameterLinearEquiv.map_smul]
  change Derivation.bracket
      (Derivation.smul a (parameterLinearEquiv p)) (parameterLinearEquiv q) =
    Derivation.smul a
      (Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv q))
  exact Derivation.bracket_smul_left a
    (parameterLinearEquiv p) (parameterLinearEquiv q)

/-- Real scalar linearity in the second parameter. -/
theorem parameterBracket_smul_right (a : ℝ) (p q : Params) :
    parameterBracket p (a • q) = a • parameterBracket p q := by
  apply parameterLinearEquiv_injective
  simp only [parameterLinearEquiv_parameterBracket, parameterLinearEquiv.map_smul]
  change Derivation.bracket (parameterLinearEquiv p)
      (Derivation.smul a (parameterLinearEquiv q)) =
    Derivation.smul a
      (Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv q))
  exact Derivation.bracket_smul_right a
    (parameterLinearEquiv p) (parameterLinearEquiv q)

/-- The cyclic Jacobi identity transported from the native derivations. -/
theorem parameterBracket_jacobi (p q r : Params) :
    parameterBracket p (parameterBracket q r) +
      (parameterBracket q (parameterBracket r p) +
        parameterBracket r (parameterBracket p q)) = 0 := by
  apply parameterLinearEquiv_injective
  simp only [parameterLinearEquiv_parameterBracket, parameterLinearEquiv.map_add,
    parameterLinearEquiv.map_zero]
  change Derivation.add
      (Derivation.bracket (parameterLinearEquiv p)
        (Derivation.bracket (parameterLinearEquiv q) (parameterLinearEquiv r)))
      (Derivation.add
        (Derivation.bracket (parameterLinearEquiv q)
          (Derivation.bracket (parameterLinearEquiv r) (parameterLinearEquiv p)))
        (Derivation.bracket (parameterLinearEquiv r)
          (Derivation.bracket (parameterLinearEquiv p) (parameterLinearEquiv q)))) =
    Derivation.zero
  exact Derivation.bracket_jacobi (parameterLinearEquiv p)
    (parameterLinearEquiv q) (parameterLinearEquiv r)

/-- The carrier equivalence transports componentwise subtraction. -/
private theorem zornVectorMatrixEquiv_sub (X Y : ZornVectorMatrix ℝ) :
    zornVectorMatrixEquiv (ZornVectorMatrix.sub X Y) =
      zornSub (zornVectorMatrixEquiv X) (zornVectorMatrixEquiv Y) := by
  cases X
  cases Y
  rfl

/-- The explicit Zorn subtraction agrees with addition of the negated second term. -/
private theorem zornSub_eq_zornAdd_smul_neg (x y : ZornSplitOctonion ℝ) :
    zornSub x y = zornAdd x (zornSmul (-1 : ℝ) y) := by
  ext <;> simp [zornSub, zornAdd, zornSmul] <;> ring

/-- The pulled-back parameter bracket acts as the pointwise commutator on the
Zorn split-octonion carrier. -/
theorem zornG2Derivation_parameterBracket (p q : Params)
    (x : ZornSplitOctonion ℝ) :
    zornG2Derivation (parameterBracket p q) x =
      zornSub (zornG2Derivation p (zornG2Derivation q x))
        (zornG2Derivation q (zornG2Derivation p x)) := by
  have h := congrArg
    (fun D : VDer => D (zornVectorMatrixEquiv.symm x))
    (parameterLinearEquiv_parameterBracket p q)
  change parameterAction (parameterBracket p q) (zornVectorMatrixEquiv.symm x) =
    ZornVectorMatrix.sub
      (parameterAction p (parameterAction q (zornVectorMatrixEquiv.symm x)))
      (parameterAction q (parameterAction p (zornVectorMatrixEquiv.symm x))) at h
  change zornVectorMatrixEquiv
      (parameterAction (parameterBracket p q) (zornVectorMatrixEquiv.symm x)) = _
  rw [h, zornVectorMatrixEquiv_sub]
  rfl

/-- The pulled-back parameter bracket acts as the pointwise commutator of the
diagonal Cayley--Dickson lifts on `SplitSedenion ℝ`. -/
theorem sedenionG2Derivation_parameterBracket (p q : Params)
    (x : SplitSedenion ℝ) :
    sedenionG2Derivation (parameterBracket p q) x =
      sedenionDerivationCommutator (sedenionG2Derivation p)
        (sedenionG2Derivation q) x := by
  rcases x with ⟨a, b⟩
  change
    (zornG2Derivation (parameterBracket p q) a,
      zornG2Derivation (parameterBracket p q) b) = _
  change
    (zornG2Derivation (parameterBracket p q) a,
      zornG2Derivation (parameterBracket p q) b) =
      (zornAdd (zornG2Derivation p (zornG2Derivation q a))
          (zornSmul (-1 : ℝ) (zornG2Derivation q (zornG2Derivation p a))),
        zornAdd (zornG2Derivation p (zornG2Derivation q b))
          (zornSmul (-1 : ℝ) (zornG2Derivation q (zornG2Derivation p b)))
      )
  apply Prod.ext
  · change zornG2Derivation (parameterBracket p q) a =
      zornAdd (zornG2Derivation p (zornG2Derivation q a))
        (zornSmul (-1 : ℝ) (zornG2Derivation q (zornG2Derivation p a)))
    rw [zornG2Derivation_parameterBracket]
    exact zornSub_eq_zornAdd_smul_neg _ _
  · change zornG2Derivation (parameterBracket p q) b =
      zornAdd (zornG2Derivation p (zornG2Derivation q b))
        (zornSmul (-1 : ℝ) (zornG2Derivation q (zornG2Derivation p b)))
    rw [zornG2Derivation_parameterBracket]
    exact zornSub_eq_zornAdd_smul_neg _ _

end InfoGeometry.Synthesis.SedenionG2ParameterBracket

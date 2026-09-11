import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ZornScalingFlow

/-!
# Chiral cone quartet in the Zorn carrier

The definitions below remain elements of the nonassociative Zorn carrier.
`leftRegular` gives their action by explicit left multiplication.  Since this
carrier intentionally has custom operations rather than native module
instances, the operator laws are recorded with those operations rather than
being misrepresented as a `LinearMap`.
-/

namespace InfoGeometry.Canonical.ChiralConeZornCarrier

open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev Zorn := InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn

def nPos : Zorn where
  a := 1; u := fun _ => 0; v := fun _ => 0; b := 0

def nNeg : Zorn where
  a := 0; u := fun _ => 0; v := fun _ => 0; b := 1

def sigmaPos (k : Fin 3) : Zorn := E_k k

def sigmaNeg (k : Fin 3) : Zorn := F_k k

/-- The honest operator lift at this stage: left multiplication on the Zorn
carrier.  We keep this as a function because `Zorn` is not given an
associative-ring structure. -/
def leftRegular (X : Zorn) : Zorn → Zorn := fun Y => zornMul X Y

@[simp] theorem leftRegular_apply (X Y : Zorn) :
    leftRegular X Y = zornMul X Y := rfl

theorem leftRegular_zornAdd (X Y Z : Zorn) :
    leftRegular X (zornAdd Y Z) =
      zornAdd (leftRegular X Y) (leftRegular X Z) := by
  exact zornMul_add X Y Z

theorem leftRegular_zornSmul (c : ℂ) (X Y : Zorn) :
    leftRegular X (zornSmul c Y) =
      zornSmul c (leftRegular X Y) := by
  exact zornMul_smul c X Y

/-- The four left-regular operators associated with a fixed colour. -/
def nPosOperator : Zorn → Zorn := leftRegular nPos

def nNegOperator : Zorn → Zorn := leftRegular nNeg

def sigmaPosOperator (k : Fin 3) : Zorn → Zorn := leftRegular (sigmaPos k)

def sigmaNegOperator (k : Fin 3) : Zorn → Zorn := leftRegular (sigmaNeg k)

@[simp] theorem nPosOperator_apply (X : Zorn) :
    nPosOperator X = zornMul nPos X := rfl

@[simp] theorem nNegOperator_apply (X : Zorn) :
    nNegOperator X = zornMul nNeg X := rfl

@[simp] theorem sigmaPosOperator_apply (k : Fin 3) (X : Zorn) :
    sigmaPosOperator k X = zornMul (sigmaPos k) X := rfl

@[simp] theorem sigmaNegOperator_apply (k : Fin 3) (X : Zorn) :
    sigmaNegOperator k X = zornMul (sigmaNeg k) X := rfl

theorem nPos_mul_nPos : zornMul nPos nPos = nPos := by
  apply zorn_ext
  · simp [nPos, zornMul, dot3]
  · funext i; fin_cases i <;> simp [nPos, zornMul, cross3]
  · funext i; fin_cases i <;> simp [nPos, zornMul, cross3]
  · simp [nPos, zornMul, dot3]

theorem nNeg_mul_nNeg : zornMul nNeg nNeg = nNeg := by
  apply zorn_ext
  · simp [nNeg, zornMul, dot3]
  · funext i; fin_cases i <;> simp [nNeg, zornMul, cross3]
  · funext i; fin_cases i <;> simp [nNeg, zornMul, cross3]
  · simp [nNeg, zornMul, dot3]

theorem nPos_mul_nNeg : zornMul nPos nNeg = zornZero := by
  apply zorn_ext
  · simp [nPos, nNeg, zornMul, zornZero, dot3]
  · funext i; fin_cases i <;> simp [nPos, nNeg, zornMul, zornZero, cross3]
  · funext i; fin_cases i <;> simp [nPos, nNeg, zornMul, zornZero, cross3]
  · simp [nPos, nNeg, zornMul, zornZero, dot3]

theorem nNeg_mul_nPos : zornMul nNeg nPos = zornZero := by
  apply zorn_ext
  · simp [nPos, nNeg, zornMul, zornZero, dot3]
  · funext i; fin_cases i <;> simp [nPos, nNeg, zornMul, zornZero, cross3]
  · funext i; fin_cases i <;> simp [nPos, nNeg, zornMul, zornZero, cross3]
  · simp [nPos, nNeg, zornMul, zornZero, dot3]

theorem nPos_add_nNeg : zornAdd nPos nNeg = I_zorn := by
  apply zorn_ext
  · simp [nPos, nNeg, I_zorn, zornAdd]
  · funext i; fin_cases i <;> simp [nPos, nNeg, I_zorn, zornAdd]
  · funext i; fin_cases i <;> simp [nPos, nNeg, I_zorn, zornAdd]
  · simp [nPos, nNeg, I_zorn, zornAdd]

theorem sigmaPos_mul_sigmaNeg (k : Fin 3) :
    zornMul (sigmaPos k) (sigmaNeg k) = nPos := by
  apply zorn_ext
  · fin_cases k <;>
      simp [sigmaPos, sigmaNeg, nPos, zornMul, E_k, F_k, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [sigmaPos, sigmaNeg, nPos, zornMul, E_k, F_k, e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [sigmaPos, sigmaNeg, nPos, zornMul, E_k, F_k, e_k, cross3]
  · simp [sigmaPos, sigmaNeg, nPos, zornMul, E_k, F_k, e_k, dot3]

theorem sigmaNeg_mul_sigmaPos (k : Fin 3) :
    zornMul (sigmaNeg k) (sigmaPos k) = nNeg := by
  apply zorn_ext
  · fin_cases k <;>
      simp [sigmaPos, sigmaNeg, nNeg, zornMul, E_k, F_k, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [sigmaPos, sigmaNeg, nNeg, zornMul, E_k, F_k, e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [sigmaPos, sigmaNeg, nNeg, zornMul, E_k, F_k, e_k, cross3]
  · fin_cases k <;>
      simp [sigmaPos, sigmaNeg, nNeg, zornMul, E_k, F_k, e_k, dot3]

theorem sigmaPos_sq (k : Fin 3) :
    zornMul (sigmaPos k) (sigmaPos k) = zornZero := by
  simpa [sigmaPos] using
    (InfoGeometry.Physics.ZornScalingFlow.upperNil_sq_zero (e_k k))

theorem sigmaNeg_sq (k : Fin 3) :
    zornMul (sigmaNeg k) (sigmaNeg k) = zornZero := by
  simpa [sigmaNeg] using
    (InfoGeometry.Physics.ZornScalingFlow.lowerNil_sq_zero (e_k k))

theorem chiralPlane_CAR (k : Fin 3) :
    zornAdd (zornMul (sigmaPos k) (sigmaNeg k))
      (zornMul (sigmaNeg k) (sigmaPos k)) = I_zorn := by
  rw [sigmaPos_mul_sigmaNeg, sigmaNeg_mul_sigmaPos, nPos_add_nNeg]

theorem nPos_commutator_sigmaPos (k : Fin 3) :
    zornSub (zornMul nPos (sigmaPos k))
      (zornMul (sigmaPos k) nPos) = sigmaPos k := by
  apply zorn_ext
  · simp [nPos, sigmaPos, zornSub, zornMul, E_k, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nPos, sigmaPos, zornSub, zornMul, E_k, e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nPos, sigmaPos, zornSub, zornMul, E_k, e_k, cross3]
  · simp [nPos, sigmaPos, zornSub, zornMul, E_k, e_k, dot3]

theorem nPos_commutator_sigmaNeg (k : Fin 3) :
    zornSub (zornMul nPos (sigmaNeg k))
      (zornMul (sigmaNeg k) nPos) = zornSub zornZero (sigmaNeg k) := by
  apply zorn_ext
  · simp [nPos, sigmaNeg, zornZero, zornSub, zornMul, F_k, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nPos, sigmaNeg, zornZero, zornSub, zornMul, F_k, e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nPos, sigmaNeg, zornZero, zornSub, zornMul, F_k, e_k, cross3]
  · simp [nPos, sigmaNeg, zornZero, zornSub, zornMul, F_k, e_k, dot3]

theorem nNeg_commutator_sigmaPos (k : Fin 3) :
    zornSub (zornMul nNeg (sigmaPos k))
      (zornMul (sigmaPos k) nNeg) = zornSub zornZero (sigmaPos k) := by
  apply zorn_ext
  · simp [nNeg, sigmaPos, zornZero, zornSub, zornMul, E_k, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nNeg, sigmaPos, zornZero, zornSub, zornMul, E_k, e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nNeg, sigmaPos, zornZero, zornSub, zornMul, E_k, e_k, cross3]
  · simp [nNeg, sigmaPos, zornZero, zornSub, zornMul, E_k, e_k, dot3]

theorem nNeg_commutator_sigmaNeg (k : Fin 3) :
    zornSub (zornMul nNeg (sigmaNeg k))
      (zornMul (sigmaNeg k) nNeg) = sigmaNeg k := by
  apply zorn_ext
  · simp [nNeg, sigmaNeg, zornSub, zornMul, F_k, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nNeg, sigmaNeg, zornSub, zornMul, F_k, e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [nNeg, sigmaNeg, zornSub, zornMul, F_k, e_k, cross3]
  · simp [nNeg, sigmaNeg, zornSub, zornMul, F_k, e_k, dot3]

end InfoGeometry.Canonical.ChiralConeZornCarrier

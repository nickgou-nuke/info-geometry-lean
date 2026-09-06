import InfoGeometry.Arithmetic.RHQuantumStabilityBridge

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbert

open InfoGeometry.Arithmetic.RHQuantumStabilityBridge

def finiteSymmetrizedDilation {n : Type*} [Fintype n]
    (position momentum : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (position * momentum + momentum * position)

theorem finiteSymmetrizedDilation_transpose
    {n : Type*} [Fintype n]
    (position momentum : Matrix n n ℝ)
    (hposition : position.transpose = position)
    (hmomentum : momentum.transpose = momentum) :
    (finiteSymmetrizedDilation position momentum).transpose =
      finiteSymmetrizedDilation position momentum := by
  unfold finiteSymmetrizedDilation
  simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
    hposition, hmomentum]
  rw [add_comm]

/-! ## 1. Berry--Keating / Majorana operator data -/

/--
Mellin/Plancherel normalization packet for the Berry--Keating sector.

The critical line is attributed to the unitary Mellin spectrum of the
Berry--Keating dilation sector, not to ordinary Fock-space summability of
Dirichlet coefficients.
-/
structure MellinPlancherelCriticalLineData
    (MellinWave MellinNorm : Type) where
  realPart : ℝ
  imaginaryHeight : ℝ
  mellinWave : MellinWave
  mellinNorm : MellinNorm
  realPart_eq_half : realPart = (1 / 2 : ℝ)

namespace MellinPlancherelCriticalLineData

variable {MellinWave MellinNorm : Type}
variable (P : MellinPlancherelCriticalLineData MellinWave MellinNorm)

/-- The packet places the real part on the critical line. -/
theorem criticalLine : IsCriticalLineRealPart P.realPart := by
  simpa [IsCriticalLineRealPart] using P.realPart_eq_half

/-- Concrete model: Mellin-Plancherel packet on the critical line Re(s) = 1/2.
The critical-line proof is definitional because `IsCriticalLineRealPart σ`
is the equality `σ = 1 / 2`. -/
def mkCriticalLine (MellinWave MellinNorm : Type)
    (mellinWave : MellinWave) (mellinNorm : MellinNorm) (imaginaryHeight : ℝ) :
    MellinPlancherelCriticalLineData MellinWave MellinNorm where
  realPart := 1/2
  imaginaryHeight := imaginaryHeight
  mellinWave := mellinWave
  mellinNorm := mellinNorm
  realPart_eq_half := by rfl

end MellinPlancherelCriticalLineData

/--
Formal Berry--Keating operator packet.

The intended model is a symmetrized dilation operator of the form
`(xp + px) / 2`, but this structure is intentionally abstract: domain,
closure, boundary conditions, and self-adjoint extension data are analytic
choices supplied by a concrete owner.
-/
structure BerryKeatingOperatorData
    (Carrier Operator Domain : Type) where
  carrier : Carrier
  domain : Domain
  position : Operator
  momentum : Operator
  symmetrizedDilation : Operator

namespace BerryKeatingOperatorData

end BerryKeatingOperatorData

/--
Majorana modification of a Berry--Keating spectral operator.

The `majoranaDirac` field is the candidate real operator whose zero modes are
to be compared with zeta zero data.  The square-root normalization and
split-Clifford/CAR compatibility are supplied as laws by the concrete model.
-/
structure MajoranaBerryKeatingOperatorData
    (Carrier Operator Domain Mode : Type) where
  berryKeating : BerryKeatingOperatorData Carrier Operator Domain
  majoranaMode : Mode → Operator
  thermalOperator : Mode → Operator
  majoranaDirac : Operator
  squareRootEnergyCoefficient : Mode → ℝ

namespace MajoranaBerryKeatingOperatorData

end MajoranaBerryKeatingOperatorData

end InfoGeometry.Arithmetic.MajoranaPolyaHilbert

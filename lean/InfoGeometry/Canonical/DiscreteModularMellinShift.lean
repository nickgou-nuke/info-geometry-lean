import InfoGeometry.Canonical.TypeIIILambdaCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Krein.Superphysics
import InfoGeometry.Meta.Architecture

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DiscreteModularSpectrum
open InfoGeometry.Canonical.TypeIIILambdaCore
open InfoGeometry.Krein

/-!
# InfoGeometry.Canonical.DiscreteModularMellinShift

Doubled-real Krein translation of the Super-Mellin shift surface.

The old complex phrase `exp(iθ)` is represented here only as a real doubled
operator `cos θ · Id + sin θ · K`, where `K = clockAxis = J ∘ ε` on
`DoubledSpace E`.  The central charge itself is not a scalar phase in this
file: the central channel is the operator-valued Drazin lane carried by
`TypeIIILambdaCore.SuperMellinAlgebra`.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.DiscreteModularMellinShift

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Kop" => InfoGeometry.Krein.clockAxis (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- The real doubled replacement for multiplication by the complex scalar `a + i b`. -/
@[rep_depth krein]
noncomputable def doubledRealComplexScalar (a b : ℝ) : EndH :=
  a • ContinuousLinearMap.id ℝ H₂ + b • Kop

/-- The real doubled replacement for the complex phase `exp(iθ)`. -/
@[rep_depth krein]
noncomputable def doubledRealPhaseOperator (θ : ℝ) : EndH :=
  doubledRealComplexScalar (E := E) (Real.cos θ) (Real.sin θ)

/-- The imaginary unit in the doubled-real translation is the Hestenes axis `K = J ∘ ε`. -/
@[rep_depth krein]
theorem doubledRealComplexScalar_zero_one_eq_clockAxis :
    doubledRealComplexScalar (E := E) 0 1 = Kop := by
  simp [doubledRealComplexScalar]

/-- The real unit scalar translates to the identity operator. -/
@[rep_depth krein]
theorem doubledRealComplexScalar_one_zero_eq_id :
    doubledRealComplexScalar (E := E) 1 0 = ContinuousLinearMap.id ℝ H₂ := by
  simp [doubledRealComplexScalar]

/-- The zero phase is the identity operator on the doubled-real carrier. -/
@[rep_depth krein]
theorem doubledRealPhaseOperator_zero :
    doubledRealPhaseOperator (E := E) 0 = ContinuousLinearMap.id ℝ H₂ := by
  simp [doubledRealPhaseOperator, doubledRealComplexScalar]

/-- The doubled-real imaginary axis squares to `-Id`. -/
@[rep_depth krein]
theorem doubledRealComplexAxis_sq :
    (InfoGeometry.Krein.clockAxis (E := E)).comp (InfoGeometry.Krein.clockAxis (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂) :=
  clockAxis_sq (E := E)

/-- Historical packet readback: the canonical doubled-real Majorana
conjugation is the repo-owned modular swap `J`. -/
@[rep_depth krein, simp]
theorem doubledRealMajoranaPacket_J_eq_modular_j :
    InfoGeometry.Core.canonicalMajoranaJ (E := E) = modular_j (E := E) :=
  rfl

/-- Historical packet readback: the canonical doubled-real Majorana grading
is the repo-owned spectral sign `ε`. -/
@[rep_depth krein, simp]
theorem doubledRealMajoranaPacket_eps_eq_spectral_epsilon :
    InfoGeometry.Core.canonicalMajoranaEps (E := E) =
      spectral_epsilon (E := E) :=
  rfl

/-- Historical packet readback: the canonical doubled-real Majorana phase
axis is `K = J ∘ ε = clockAxis`. -/
@[rep_depth krein, simp]
theorem doubledRealMajoranaPacket_K_eq_clockAxis :
    InfoGeometry.Core.canonicalMajoranaK (E := E) = Kop :=
  rfl

/-- Canonical doubled-real Majorana root laws backing the Mellin translation. -/
@[rep_depth krein]
theorem doubledRealMajorana_root_laws :
    (modular_j (E := E)).comp (modular_j (E := E)) =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (complex_i (E := E)).comp (complex_i (E := E)) =
        -(ContinuousLinearMap.id ℝ H₂) :=
  ⟨modular_j_involution (E := E),
    spectral_epsilon_involution (E := E),
    complex_i_sq (E := E)⟩

/--
Mellin shift operator on the doubled-real Type `III_λ` lattice.

This records lattice hopping only.  Operatorial central charge data is carried
separately by `TypeIIILambdaCore.SuperMellinAlgebra`.
-/
@[rep_depth operator]
structure DoubledRealMellinShiftOperator
    (CIK : CertifiedInverseKernel H₂)
    (L : TypeIIILambdaCore.ModularLambdaLattice E CIK) where
  /-- One-step real bounded equivalence on the doubled carrier. -/
  shift : H₂ ≃L[ℝ] H₂
  /-- Discrete Weyl covariance over the Mellin boost lattice. -/
  weyl_covariance : ∀ (k : ℤ) (A : EndH),
    (shift : EndH) * L.lattice.discreteBoost k A * (shift.symm : EndH) =
      L.lattice.discreteBoost (k + 1) A

/--
Doubled-real Super-Mellin packet.

The `operatorial` field is the canonical Type `III_λ` Super-Mellin algebra with
operator-valued Drazin central channel.  The `shift` field records the explicit
real doubled lattice hop.  No scalar central charge is introduced here.
-/
structure DoubledRealSuperMellinAlgebra
    (CIK : CertifiedInverseKernel H₂)
    (L : TypeIIILambdaCore.ModularLambdaLattice E CIK) where
  shift : DoubledRealMellinShiftOperator CIK L
  supercharge : TypeIIILambdaCore.MellinSupercharge (E := E) (CIK := CIK) L
  /-- Operator-valued central channel, not a scalar phase. -/
  centralOperator : EndH
  central_isDrazinLaneCentral :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK centralOperator
  central_isDefectSupported :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
      CIK centralOperator
  supercharge_mem_chiralCone :
    InfoGeometry.Canonical.ChiralOperatorConeClosure.IsInChiralOperatorCone
      CIK supercharge.Q
  superHamiltonian_split :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK =
      L.lattice.K0 + centralOperator

namespace DoubledRealSuperMellinAlgebra

variable {CIK : CertifiedInverseKernel H₂}
variable {L : TypeIIILambdaCore.ModularLambdaLattice E CIK}

/-- The central channel remains operatorial and Drazin-lane central. -/
@[rep_depth operator]
theorem centralOperator_isDrazinLaneCentral
    (A : DoubledRealSuperMellinAlgebra CIK L) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK A.centralOperator :=
  A.central_isDrazinLaneCentral

/-- The central channel remains supported on the Drazin defect block. -/
@[rep_depth operator]
theorem centralOperator_isDefectSupported
    (A : DoubledRealSuperMellinAlgebra CIK L) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
      CIK A.centralOperator :=
  A.central_isDefectSupported

/-- The Super-Mellin root remains in the repo-owned chiral cone. -/
@[rep_depth operator]
theorem supercharge_in_chiralCone
    (A : DoubledRealSuperMellinAlgebra CIK L) :
    InfoGeometry.Canonical.ChiralOperatorConeClosure.IsInChiralOperatorCone
      CIK A.supercharge.Q :=
  A.supercharge_mem_chiralCone

/-- The Drazin superHamiltonian split is preserved on the doubled-real packet. -/
@[rep_depth operator]
theorem superHamiltonian_eq_K0_plus_centralOperator
    (A : DoubledRealSuperMellinAlgebra CIK L) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK =
      L.lattice.K0 + A.centralOperator :=
  A.superHamiltonian_split

end DoubledRealSuperMellinAlgebra

/--
Minimal Clifford/Super-Mellin block packet on the doubled-real lane.

This is the conservative owner-adjacent packet for the next realization step:

* a total operator splits into bosonic and fermionic blocks;
* the discrete Mellin shift acts on the bosonic block by a full doubled-real
  phase;
* the same shift acts on the fermionic block by a half-phase.

No complex phase scalar is introduced.  The shift action is expressed entirely
through the repo-owned doubled-real phase operator.
-/
@[rep_depth operator]
structure CliffordSuperMellinPacket
    (CIK : CertifiedInverseKernel H₂)
    (L : TypeIIILambdaCore.ModularLambdaLattice E CIK) where
  algebra : DoubledRealSuperMellinAlgebra CIK L
  totalOperator : EndH
  bosonicBlock : EndH
  fermionicBlock : EndH
  phaseAngle : ℝ
  total_eq_blocks :
    totalOperator = bosonicBlock + fermionicBlock
  shiftActsOnBosonicBlock :
    ((algebra.shift.shift : EndH) * bosonicBlock * (algebra.shift.shift.symm : EndH)) =
      doubledRealPhaseOperator (E := E) phaseAngle * bosonicBlock
  shiftActsOnFermionicBlock :
    ((algebra.shift.shift : EndH) * fermionicBlock * (algebra.shift.shift.symm : EndH)) =
      doubledRealPhaseOperator (E := E) (phaseAngle / 2) * fermionicBlock

namespace CliffordSuperMellinPacket

variable {CIK : CertifiedInverseKernel H₂}
variable {L : TypeIIILambdaCore.ModularLambdaLattice E CIK}

/-- The central channel remains operatorial and Drazin-lane central on the block packet. -/
@[rep_depth operator]
theorem centralOperator_isDrazinLaneCentral
    (A : CliffordSuperMellinPacket (E := E) CIK L) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentralK
      CIK A.algebra.centralOperator :=
  A.algebra.centralOperator_isDrazinLaneCentral

/-- The central channel remains defect-supported on the block packet. -/
@[rep_depth operator]
theorem centralOperator_isDefectSupported
    (A : CliffordSuperMellinPacket (E := E) CIK L) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.IsDefectSupportedK
      CIK A.algebra.centralOperator :=
  A.algebra.centralOperator_isDefectSupported

end CliffordSuperMellinPacket

end InfoGeometry.Canonical.DiscreteModularMellinShift

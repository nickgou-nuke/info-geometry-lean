import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.ModularSuperchargeClosure
import InfoGeometry.Canonical.OperatorDictionary
import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularHamiltonianDoubledBridge

Co-owner bridge for the true modular Hamiltonian in the repo-native doubled
Krein/Hestenes lane.

This file does not introduce a new Hamiltonian ontology. It rewrites the owned
Tomita package into explicit `J, ε, J∘ε` equalities on the doubled carrier and
keeps the `K = -log Δ` meaning via the exponential certificate.
-/

namespace InfoGeometry.Canonical.ModularHamiltonianDoubledBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorDictionary
open InfoGeometry.Canonical.ModularSuperchargeClosure
open InfoGeometry.Canonical.RealTomitaCore

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
The doubled/Hestenes expression for the owned modular Hamiltonian surface.
This is a representation surface, not a new owner definition.
-/
@[rep_depth krein]
noncomputable def modularHamiltonianDoubledExpr
    (T : RealTomitaCore.RealModularLogData (E := E)) : EndH :=
  T.deltaLog.comp (complex_i (E := E))

omit [CompleteSpace E] in
/--
Core bridge theorem: the owned modular Hamiltonian equals its doubled/Hestenes
expression.
-/
@[rep_depth krein]
theorem modularHamiltonian_eq_doubledExpr
    (T : RealTomitaCore.RealModularLogData (E := E)) :
    T.generator = modularHamiltonianDoubledExpr (E := E) T := by
  simp [RealTomitaCore.RealModularLogData.generator, modularHamiltonianDoubledExpr,
    BogoliubovTransport.modularTransportGenerator]

omit [CompleteSpace E] in
/--
Equivalent split-axis form `A = δ ∘ J ∘ ε`.
-/
@[rep_depth krein]
theorem modularHamiltonian_eq_phaseAxisForm
    (T : RealTomitaCore.RealModularLogData (E := E)) :
    T.generator
      = T.deltaLog.comp ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
  calc
    T.generator = modularHamiltonianDoubledExpr (E := E) T :=
      modularHamiltonian_eq_doubledExpr (E := E) T
    _ = T.deltaLog.comp ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
        rw [modularHamiltonianDoubledExpr]
        rfl

/-- The canonical Tomita package is an explicit `exp/log` witness on doubled space. -/
@[rep_depth transport]
theorem canonicalTomitaLogData_exp_deltaLog
    (CIK : CertifiedInverseKernel H₂) :
    NormedSpace.exp ((canonicalTomitaLogData (E := E) CIK).deltaLog)
      = (canonicalTomitaLogData (E := E) CIK).Delta :=
  (canonicalTomitaLogData (E := E) CIK).exp_deltaLog

/-- Equivalent form: `Δ = exp(δ)` on the same doubled carrier lane. -/
@[rep_depth transport]
theorem canonicalTomitaLogData_Delta_eq_exp_deltaLog
    (CIK : CertifiedInverseKernel H₂) :
    (canonicalTomitaLogData (E := E) CIK).Delta
      = NormedSpace.exp ((canonicalTomitaLogData (E := E) CIK).deltaLog) := by
  simpa using (canonicalTomitaLogData_exp_deltaLog (E := E) CIK).symm

/--
`K = -log Δ` in repo language:
if `K := -δ`, then `exp(-K) = Δ` for the canonical Tomita package.
-/
@[rep_depth transport]
theorem canonicalTomita_modularHamiltonian_exp_neg_eq_Delta
    (CIK : CertifiedInverseKernel H₂) :
    let K : EndH := -((canonicalTomitaLogData (E := E) CIK).deltaLog)
    NormedSpace.exp (-K) = (canonicalTomitaLogData (E := E) CIK).Delta := by
  intro K
  have hExp :
      NormedSpace.exp ((canonicalTomitaLogData (E := E) CIK).deltaLog)
        = (canonicalTomitaLogData (E := E) CIK).Delta :=
    canonicalTomitaLogData_exp_deltaLog (E := E) CIK
  simpa [K] using hExp

/-- The canonical modular seed is the projected-even doubled expression. -/
@[rep_depth transport]
theorem canonicalTomita_deltaLog_eq_neg_superHamiltonian_comp_phaseAxisK
    (CIK : CertifiedInverseKernel H₂) :
    (canonicalTomitaLogData (E := E) CIK).deltaLog
      = -(DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK).comp
          (phaseAxisK (E := E)) := by
  simp [canonicalTomitaLogData, canonicalModularSeed, phaseAxisK]

/-- True modular generator in doubled language: `A = δ ∘ (J ∘ ε)`. -/
@[rep_depth transport]
theorem canonicalTomita_generator_eq_deltaLog_comp_phaseAxisK
    (CIK : CertifiedInverseKernel H₂) :
    (canonicalTomitaLogData (E := E) CIK).generator
      = ((canonicalTomitaLogData (E := E) CIK).deltaLog).comp
          (phaseAxisK (E := E)) := by
  unfold RealTomitaCore.RealModularLogData.generator
  unfold BogoliubovTransport.modularTransportGenerator
  simp [phaseAxisK]

/--
Canonical-seed specialization of the core bridge theorem.
-/
@[rep_depth transport]
theorem canonicalTomita_generator_eq_doubledExpr
    (CIK : CertifiedInverseKernel H₂) :
    (canonicalTomitaLogData (E := E) CIK).generator
      = modularHamiltonianDoubledExpr (E := E) (canonicalTomitaLogData (E := E) CIK) := by
  exact modularHamiltonian_eq_doubledExpr (E := E) (canonicalTomitaLogData (E := E) CIK)

/-- True modular generator in split form: `A = δ ∘ J ∘ ε`. -/
@[rep_depth transport]
theorem canonicalTomita_generator_eq_deltaLog_comp_modular_j_comp_spectral_epsilon
    (CIK : CertifiedInverseKernel H₂) :
    (canonicalTomitaLogData (E := E) CIK).generator
      = ((canonicalTomitaLogData (E := E) CIK).deltaLog).comp
          ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
  calc
    (canonicalTomitaLogData (E := E) CIK).generator
        = ((canonicalTomitaLogData (E := E) CIK).deltaLog).comp (phaseAxisK (E := E)) :=
          canonicalTomita_generator_eq_deltaLog_comp_phaseAxisK (E := E) CIK
    _ = ((canonicalTomitaLogData (E := E) CIK).deltaLog).comp
          ((modular_j (E := E)).comp (spectral_epsilon (E := E))) := by
          rw [phaseAxisK_eq_modular_j_comp_spectral_epsilon (E := E)]

/-- Canonical real Tomita flow is exactly `exp(t • A)` in doubled language. -/
@[rep_depth transport]
theorem canonicalTomita_flow_eq_exp_time_generator
    (CIK : CertifiedInverseKernel H₂) (t : ℝ) :
    (canonicalTomitaLogData (E := E) CIK).flow t
      = NormedSpace.exp (t • (canonicalTomitaLogData (E := E) CIK).generator) := by
  simp [RealTomitaCore.RealModularLogData.flow, RealTomitaCore.RealModularLogData.generator,
    BogoliubovTransport.modularTransportFlow]

/--
The modular automorphism action is explicit generator conjugation on the
same doubled carrier.
-/
@[rep_depth transport]
theorem canonicalTomita_adjointFlow_eq_exp_generator_conjugation
    (CIK : CertifiedInverseKernel H₂) (t : ℝ) (A : EndH) :
    (canonicalTomitaLogData (E := E) CIK).adjointFlow t A
      = NormedSpace.exp (t • (canonicalTomitaLogData (E := E) CIK).generator)
          * A
          * NormedSpace.exp ((-t) • (canonicalTomitaLogData (E := E) CIK).generator) := by
  unfold RealTomitaCore.RealModularLogData.adjointFlow
  rw [canonicalTomita_flow_eq_exp_time_generator (E := E) CIK t]
  rw [canonicalTomita_flow_eq_exp_time_generator (E := E) CIK (-t)]

/--
Owner closure hook: projected-even super-Hamiltonian equals the canonical true
modular generator on the same certified lane.
-/
@[rep_depth transport]
theorem projectedEven_superHamiltonian_eq_canonicalTomita_generator
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      = (canonicalTomitaLogData (E := E) CIK).generator :=
  superHamiltonian_eq_canonicalTomitaGenerator (E := E) CIK

/--
Owner-lane closure in explicit doubled-expression form.
-/
@[rep_depth transport]
theorem projectedEven_superHamiltonian_eq_doubledExpr
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
      = modularHamiltonianDoubledExpr (E := E) (canonicalTomitaLogData (E := E) CIK) := by
  calc
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK
        = (canonicalTomitaLogData (E := E) CIK).generator :=
          projectedEven_superHamiltonian_eq_canonicalTomita_generator (E := E) CIK
    _ = modularHamiltonianDoubledExpr (E := E) (canonicalTomitaLogData (E := E) CIK) :=
          canonicalTomita_generator_eq_doubledExpr (E := E) CIK

end Core

end InfoGeometry.Canonical.ModularHamiltonianDoubledBridge

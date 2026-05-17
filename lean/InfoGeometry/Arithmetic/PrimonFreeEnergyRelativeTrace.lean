import Mathlib
import InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace

Witness-gated free-energy and relative-trace socket for the MBK/primon program.

This file records the theorem-safe version of the conceptual passage

`Majorana Witten character 1 / ζ  →  free energy log ζ  →  relative trace`.

It deliberately does **not** assert convexity of a zeta potential, identify
Riemann zeros with minima, prove Connes' trace formula, or prove RH.  Those are
separate analytic/spectral witnesses.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace

open InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter

/-! ## 1. Finite positive free-energy lane -/

/-- Free energy of a positive partition readout. -/
def freeEnergy (Z : ℝ) : ℝ :=
  -Real.log Z

/--
Finite inversion identity for the free energy.

If `ZF * ZB = 1` and both readouts are positive, then the fermionic free
energy `-log ZF` is `log ZB`.
-/
theorem freeEnergy_eq_log_dual_of_mul_eq_one
    {ZF ZB : ℝ}
    (hZF : 0 < ZF)
    (hZB : 0 < ZB)
    (hmul : ZF * ZB = 1) :
    freeEnergy ZF = Real.log ZB := by
  unfold freeEnergy
  have hlog_mul :
      Real.log (ZF * ZB) = Real.log ZF + Real.log ZB :=
    Real.log_mul (ne_of_gt hZF) (ne_of_gt hZB)
  rw [hmul] at hlog_mul
  simp only [Real.log_one] at hlog_mul
  linarith

/--
Finite product free energy for a finite primon Majorana character.

This is only defined as a real log readout; positivity must be supplied when
using analytic log identities.
-/
def finiteMajoranaFreeEnergy (P : Finset ℕ) (s : ℝ) : ℝ :=
  freeEnergy (finiteWittenCharacter P s)

/-! ## 2. Determinant-line inversion lane -/

/--
Determinant-line inversion.

This is the finite real shadow of the passage

`Z ↦ Z⁻¹`.

It is not an analytic continuation theorem and it does not identify the
resulting inverse with an infinite Euler product.
-/
def determinantLineInversion (Z : ℝ) : ℝ :=
  Z⁻¹

/--
The determinant-line inversion is involutive.
-/
theorem determinantLineInversion_involutive
    (Z : ℝ) :
    determinantLineInversion (determinantLineInversion Z) = Z := by
  simp [determinantLineInversion]

/--
Positive determinant-line inversion turns free energy into the logarithm of the
dual determinant.

This is the precise finite real form of

`-log (Z⁻¹) = log Z`.
-/
theorem freeEnergy_determinantLineInversion_eq_log
    {Z : ℝ}
    (hZ : 0 < Z) :
    freeEnergy (determinantLineInversion Z) = Real.log Z := by
  unfold determinantLineInversion
  exact freeEnergy_eq_log_dual_of_mul_eq_one (inv_pos.mpr hZ) hZ (inv_mul_cancel₀ (ne_of_gt hZ))

/--
Weyl--Möbius inversion socket on the determinant line.

The arithmetic slogans

`ζ ↔ 1/ζ`, `log Z ↦ -log Z`, `e₋ ↔ e₊`, and `H ↦ -H`

are kept as supplied laws.  This packet does not prove the Riemann functional
equation, a scattering determinant identity, or RH.
-/
@[socket_debt_tag]
structure WeylMobiusDeterminantInversionSocket
    (DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout : Type*) where
  determinantLine : DeterminantLine
  inversion : Inversion
  logCoordinate : LogCoordinate
  generator : Generator
  stableEndpoint : StableEndpoint
  unstableEndpoint : UnstableEndpoint
  bosonicReadout : BosonicReadout
  fermionicReadout : FermionicReadout
  determinant_inversion_law : Prop
  determinant_inversion_certificate :
    determinant_inversion_law
  log_sign_flip_law : Prop
  log_sign_flip_certificate :
    log_sign_flip_law
  generator_sign_flip_law : Prop
  generator_sign_flip_certificate :
    generator_sign_flip_law
  endpoints_exchanged_law : Prop
  endpoints_exchanged_certificate :
    endpoints_exchanged_law
  boson_fermion_inverse_law : Prop
  boson_fermion_inverse_certificate :
    boson_fermion_inverse_law
  /--
  Guardrail: zero/pole exchange is a determinant-chart statement, not a
  zero-mode theorem for the inverse determinant.
  -/
  poleZeroExchange_not_zeroModeTheorem_guard : Type*

namespace WeylMobiusDeterminantInversionSocket

/-- Re-export of the supplied determinant inversion law. -/
theorem determinant_inversion
    {DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout : Type*}
    (S : WeylMobiusDeterminantInversionSocket
      DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout) :
    S.determinant_inversion_law :=
  S.determinant_inversion_certificate

/-- Re-export of the supplied logarithmic sign-flip law. -/
theorem log_sign_flip
    {DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout : Type*}
    (S : WeylMobiusDeterminantInversionSocket
      DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout) :
    S.log_sign_flip_law :=
  S.log_sign_flip_certificate

/-- Re-export of the supplied endpoint-exchange law. -/
theorem endpoints_exchanged
    {DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout : Type*}
    (S : WeylMobiusDeterminantInversionSocket
      DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout) :
    S.endpoints_exchanged_law :=
  S.endpoints_exchanged_certificate

/-- Re-export of the supplied boson/fermion inverse determinant law. -/
theorem boson_fermion_inverse
    {DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout : Type*}
    (S : WeylMobiusDeterminantInversionSocket
      DeterminantLine Inversion LogCoordinate Generator StableEndpoint
      UnstableEndpoint BosonicReadout FermionicReadout) :
    S.boson_fermion_inverse_law :=
  S.boson_fermion_inverse_certificate

end WeylMobiusDeterminantInversionSocket

/-! ## 3. Stable/unstable Gibbs chart socket -/

/--
Stable/unstable Gibbs chart socket.

The stable chart is the positive Gibbs/KL minimization chart.  The inverted
chart `e^{-tV} ↦ e^{+tV}` is represented separately, because for unbounded
potentials it may fail to have a normalizable minimizer.
-/
@[socket_debt_tag]
structure StableUnstableGibbsChartSocket
    (ReferenceMeasure Potential StableDensity UnstableDensity StableFunctional
      UnstableFunctional StableMinimizer BoundaryReadout FlowReadout : Type*) where
  referenceMeasure : ReferenceMeasure
  potential : Potential
  stableDensity : StableDensity
  unstableDensity : UnstableDensity
  stableFunctional : StableFunctional
  unstableFunctional : UnstableFunctional
  stableMinimizer : StableMinimizer
  boundaryReadout : BoundaryReadout
  flowReadout : FlowReadout
  stable_gibbs_minimizer_law : Prop
  stable_gibbs_minimizer_certificate :
    stable_gibbs_minimizer_law
  inverted_chart_law : Prop
  inverted_chart_certificate :
    inverted_chart_law
  unstable_boundary_law : Prop
  unstable_boundary_certificate :
    unstable_boundary_law
  logarithmic_barrier_law : Prop
  logarithmic_barrier_certificate :
    logarithmic_barrier_law
  /--
  Guardrail: the boundary/singularity is not reached by an ordinary positive
  probability flow without a separate completion or relative determinant chart.
  -/
  boundary_not_crossed_by_positiveFlow_guard : Type*

namespace StableUnstableGibbsChartSocket

/-- Re-export of the supplied stable Gibbs minimizer law. -/
theorem stable_gibbs_minimizer
    {ReferenceMeasure Potential StableDensity UnstableDensity StableFunctional
      UnstableFunctional StableMinimizer BoundaryReadout FlowReadout : Type*}
    (S : StableUnstableGibbsChartSocket
      ReferenceMeasure Potential StableDensity UnstableDensity StableFunctional
      UnstableFunctional StableMinimizer BoundaryReadout FlowReadout) :
    S.stable_gibbs_minimizer_law :=
  S.stable_gibbs_minimizer_certificate

/-- Re-export of the supplied inverted chart law. -/
theorem inverted_chart
    {ReferenceMeasure Potential StableDensity UnstableDensity StableFunctional
      UnstableFunctional StableMinimizer BoundaryReadout FlowReadout : Type*}
    (S : StableUnstableGibbsChartSocket
      ReferenceMeasure Potential StableDensity UnstableDensity StableFunctional
      UnstableFunctional StableMinimizer BoundaryReadout FlowReadout) :
    S.inverted_chart_law :=
  S.inverted_chart_certificate

/-- Re-export of the supplied unstable boundary law. -/
theorem unstable_boundary
    {ReferenceMeasure Potential StableDensity UnstableDensity StableFunctional
      UnstableFunctional StableMinimizer BoundaryReadout FlowReadout : Type*}
    (S : StableUnstableGibbsChartSocket
      ReferenceMeasure Potential StableDensity UnstableDensity StableFunctional
      UnstableFunctional StableMinimizer BoundaryReadout FlowReadout) :
    S.unstable_boundary_law :=
  S.unstable_boundary_certificate

end StableUnstableGibbsChartSocket

/-! ## 4. Relative trace signature socket -/

/--
Relative-trace signature packet.

The Riemann--Weil explicit formula has a prime-orbit term with the opposite
sign from the naive positive Gutzwiller orbit contribution.  This packet
records a supplied explanation through a boson-minus-fermion or relative
supertrace readout.
-/
@[socket_debt_tag]
structure RelativeTraceSignatureSocket
    (BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout : Type*) where
  bosonicTrace : BosonicTrace
  fermionicTrace : FermionicTrace
  relativeTrace : RelativeTrace
  primeOrbitReadout : PrimeOrbitReadout
  explicitFormulaReadout : ExplicitFormulaReadout
  relativeTrace_formula_law : Prop
  relativeTrace_formula_certificate :
    relativeTrace_formula_law
  fermionic_primeOrbit_minusSign_law : Prop
  fermionic_primeOrbit_minusSign_certificate :
    fermionic_primeOrbit_minusSign_law
  relativeTrace_matches_explicitFormula_law : Prop
  relativeTrace_matches_explicitFormula_certificate :
    relativeTrace_matches_explicitFormula_law
  /-- Guardrail: the sign is not obtained from a naive positive trace. -/
  not_naive_positive_trace_guard : Type*

namespace RelativeTraceSignatureSocket

/-- Re-export of the supplied relative-trace formula law. -/
theorem relativeTrace_formula
    {BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout : Type*}
    (S : RelativeTraceSignatureSocket
      BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout ExplicitFormulaReadout) :
    S.relativeTrace_formula_law :=
  S.relativeTrace_formula_certificate

/-- Re-export of the supplied prime-orbit minus-sign law. -/
theorem fermionic_primeOrbit_minusSign
    {BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout : Type*}
    (S : RelativeTraceSignatureSocket
      BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout ExplicitFormulaReadout) :
    S.fermionic_primeOrbit_minusSign_law :=
  S.fermionic_primeOrbit_minusSign_certificate

/-- Re-export of the supplied explicit-formula matching law. -/
theorem relativeTrace_matches_explicitFormula
    {BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout : Type*}
    (S : RelativeTraceSignatureSocket
      BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout ExplicitFormulaReadout) :
    S.relativeTrace_matches_explicitFormula_law :=
  S.relativeTrace_matches_explicitFormula_certificate

end RelativeTraceSignatureSocket

/-! ## 5. Möbius inversion / free-energy socket -/

/--
Free-energy inversion socket.

The finite Majorana/Pfaffian Witten character belongs to the inverse-zeta
channel.  Passing to `-log` gives the free-energy/log-zeta channel only after
positivity, branch, and regularization choices are supplied.
-/
@[socket_debt_tag]
structure MobiusFreeEnergyInversionSocket
    (SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout : Type*) where
  parameter : SpectralParameter
  majoranaPartition : MajoranaPartition
  dualPartition : DualPartition
  freeEnergyReadout : FreeEnergyReadout
  branchData : BranchData
  singularityReadout : SingularityReadout
  majorana_inverseZeta_law : Prop
  majorana_inverseZeta_certificate :
    majorana_inverseZeta_law
  freeEnergy_logDual_law : Prop
  freeEnergy_logDual_certificate :
    freeEnergy_logDual_law
  zetaZeros_are_logSingularities_law : Prop
  zetaZeros_are_logSingularities_certificate :
    zetaZeros_are_logSingularities_law
  /--
  Guardrail: zeta zeros are not automatically minima of a real convex
  potential.  That requires a separate KL/convexity witness.
  -/
  zeros_not_minima_without_convexityWitness_guard : Type*

namespace MobiusFreeEnergyInversionSocket

/-- Re-export: Majorana partition is the inverse-zeta channel. -/
theorem majorana_inverseZeta
    {SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout : Type*}
    (S : MobiusFreeEnergyInversionSocket
      SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout) :
    S.majorana_inverseZeta_law :=
  S.majorana_inverseZeta_certificate

/-- Re-export: free energy gives the logarithmic dual channel. -/
theorem freeEnergy_logDual
    {SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout : Type*}
    (S : MobiusFreeEnergyInversionSocket
      SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout) :
    S.freeEnergy_logDual_law :=
  S.freeEnergy_logDual_certificate

/-- Re-export: zeros of zeta are logarithmic singularities in this channel. -/
theorem zetaZeros_are_logSingularities
    {SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout : Type*}
    (S : MobiusFreeEnergyInversionSocket
      SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout) :
    S.zetaZeros_are_logSingularities_law :=
  S.zetaZeros_are_logSingularities_certificate

end MobiusFreeEnergyInversionSocket

/-! ## 6. Mellin inversion and KL/convex equilibrium sockets -/

/--
Mellin inversion/parity socket.

The geometric inversion `x ↦ 1/x` becomes `u ↦ -u` in logarithmic coordinate.
Any identification with the functional equation or the critical-axis symmetry
is supplied as witness data.
-/
@[socket_debt_tag]
structure MellinInversionParitySocket
    (ScaleCoordinate LogCoordinate SpectralParameter ParityOperator
      FunctionalEquationReadout : Type*) where
  scaleCoordinate : ScaleCoordinate
  logCoordinate : LogCoordinate
  parameter : SpectralParameter
  parityOperator : ParityOperator
  functionalEquationReadout : FunctionalEquationReadout
  scale_inversion_law : Prop
  scale_inversion_certificate :
    scale_inversion_law
  log_parity_law : Prop
  log_parity_certificate :
    log_parity_law
  functionalEquation_symmetry_law : Prop
  functionalEquation_symmetry_certificate :
    functionalEquation_symmetry_law
  criticalAxis_fixed_law : Prop
  criticalAxis_fixed_certificate :
    criticalAxis_fixed_law

namespace MellinInversionParitySocket

/-- Re-export of the supplied `u ↦ -u` parity law. -/
theorem log_parity
    {ScaleCoordinate LogCoordinate SpectralParameter ParityOperator
      FunctionalEquationReadout : Type*}
    (S : MellinInversionParitySocket
      ScaleCoordinate LogCoordinate SpectralParameter ParityOperator
      FunctionalEquationReadout) :
    S.log_parity_law :=
  S.log_parity_certificate

/-- Re-export of the supplied functional-equation symmetry law. -/
theorem functionalEquation_symmetry
    {ScaleCoordinate LogCoordinate SpectralParameter ParityOperator
      FunctionalEquationReadout : Type*}
    (S : MellinInversionParitySocket
      ScaleCoordinate LogCoordinate SpectralParameter ParityOperator
      FunctionalEquationReadout) :
    S.functionalEquation_symmetry_law :=
  S.functionalEquation_symmetry_certificate

end MellinInversionParitySocket

/--
KL/optimal-transport equilibrium socket.

This is intentionally a witness interface.  It is not generally true that a
zeta/free-energy landscape is convex or that zeta zeros are minima; a concrete
model must supply the KL functional, convexity, and equilibrium theorem.
-/
@[socket_debt_tag]
structure KLEquilibriumSocket
    (SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout : Type*) where
  sourceDistribution : SourceDistribution
  targetDistribution : TargetDistribution
  transportPlan : TransportPlan
  klReadout : KLReadout
  potential : Potential
  equilibriumSet : EquilibriumSet
  criticalLineReadout : CriticalLineReadout
  kl_represents_freeEnergy_law : Prop
  kl_represents_freeEnergy_certificate :
    kl_represents_freeEnergy_law
  convexity_law : Prop
  convexity_certificate :
    convexity_law
  equilibrium_criticalLine_law : Prop
  equilibrium_criticalLine_certificate :
    equilibrium_criticalLine_law
  /-- Guardrail: convexity and uniqueness are analytic hypotheses, not formal analogy. -/
  convexity_not_automatic_guard : Type*

namespace KLEquilibriumSocket

/-- Re-export of the supplied KL/free-energy law. -/
theorem kl_represents_freeEnergy
    {SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout : Type*}
    (S : KLEquilibriumSocket
      SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout) :
    S.kl_represents_freeEnergy_law :=
  S.kl_represents_freeEnergy_certificate

/-- Re-export of the supplied convexity law. -/
theorem convexity
    {SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout : Type*}
    (S : KLEquilibriumSocket
      SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout) :
    S.convexity_law :=
  S.convexity_certificate

/-- Re-export of the supplied equilibrium/critical-line law. -/
theorem equilibrium_criticalLine
    {SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout : Type*}
    (S : KLEquilibriumSocket
      SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout) :
    S.equilibrium_criticalLine_law :=
  S.equilibrium_criticalLine_certificate

end KLEquilibriumSocket

/-! ## 7. Five-graded balance socket -/

/--
Five-graded symmetry balance socket.

The `e⁺/e⁻` UV/IR language is represented only as supplied Lie/gradation data.
It does not prove a representation-theoretic zero-mode theorem.
-/
@[socket_debt_tag]
structure FiveGradedMobiusBalanceSocket
    (LieAlgebra GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout
      ZeroModeReadout : Type*) where
  lieAlgebra : LieAlgebra
  gradeMinus : GradeMinus
  gradeZero : GradeZero
  gradePlus : GradePlus
  ePlus : EPlus
  eMinus : EMinus
  balanceReadout : BalanceReadout
  zeroModeReadout : ZeroModeReadout
  ePlus_uv_law : Prop
  ePlus_uv_certificate :
    ePlus_uv_law
  eMinus_ir_law : Prop
  eMinus_ir_certificate :
    eMinus_ir_law
  balance_on_gradeZero_law : Prop
  balance_on_gradeZero_certificate :
    balance_on_gradeZero_law
  /-- Guardrail: zero-mode protection requires a concrete representation theorem. -/
  zeroModeProtection_requires_representationWitness_guard : Type*

namespace FiveGradedMobiusBalanceSocket

/-- Re-export of the supplied grade-zero balance law. -/
theorem balance_on_gradeZero
    {LieAlgebra GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout
      ZeroModeReadout : Type*}
    (S : FiveGradedMobiusBalanceSocket
      LieAlgebra GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout
      ZeroModeReadout) :
    S.balance_on_gradeZero_law :=
  S.balance_on_gradeZero_certificate

end FiveGradedMobiusBalanceSocket

/-! ## 8. Composite research-manifest packet -/

/--
Composite relative-trace/free-energy research packet.

This packages the conceptual MBK/Connes/free-energy program while keeping all
global analysis obligations explicit.
-/
structure PrimonFreeEnergyRelativeTraceManifest
    (BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout SpectralParameter MajoranaPartition DualPartition
      FreeEnergyReadout BranchData SingularityReadout ScaleCoordinate LogCoordinate
      ParityOperator FunctionalEquationReadout SourceDistribution TargetDistribution
      TransportPlan KLReadout Potential EquilibriumSet CriticalLineReadout LieAlgebra
      GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout ZeroModeReadout :
      Type*) where
  relativeTrace :
    RelativeTraceSignatureSocket
      BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout ExplicitFormulaReadout
  freeEnergy :
    MobiusFreeEnergyInversionSocket
      SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout
      BranchData SingularityReadout
  mellinInversion :
    MellinInversionParitySocket
      ScaleCoordinate LogCoordinate SpectralParameter ParityOperator
      FunctionalEquationReadout
  klEquilibrium :
    KLEquilibriumSocket
      SourceDistribution TargetDistribution TransportPlan KLReadout
      Potential EquilibriumSet CriticalLineReadout
  fiveGradedBalance :
    FiveGradedMobiusBalanceSocket
      LieAlgebra GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout
      ZeroModeReadout
  /-- Guardrail: this is a research-manifest packet, not an RH proof. -/
  not_RH_proof_guard : Type*

namespace PrimonFreeEnergyRelativeTraceManifest

/-- The manifest includes the explicit-formula relative-trace witness. -/
theorem relativeTrace_matches_explicitFormula
    {BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout SpectralParameter MajoranaPartition DualPartition
      FreeEnergyReadout BranchData SingularityReadout ScaleCoordinate LogCoordinate
      ParityOperator FunctionalEquationReadout SourceDistribution TargetDistribution
      TransportPlan KLReadout Potential EquilibriumSet CriticalLineReadout LieAlgebra
      GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout ZeroModeReadout :
      Type*}
    (M : PrimonFreeEnergyRelativeTraceManifest
      BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout ExplicitFormulaReadout
      SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout BranchData
      SingularityReadout ScaleCoordinate LogCoordinate ParityOperator
      FunctionalEquationReadout SourceDistribution TargetDistribution TransportPlan
      KLReadout Potential EquilibriumSet CriticalLineReadout LieAlgebra GradeMinus
      GradeZero GradePlus EPlus EMinus BalanceReadout ZeroModeReadout) :
    M.relativeTrace.relativeTrace_matches_explicitFormula_law :=
  M.relativeTrace.relativeTrace_matches_explicitFormula_certificate

/-- The manifest includes the free-energy/log-dual witness. -/
theorem freeEnergy_logDual
    {BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout SpectralParameter MajoranaPartition DualPartition
      FreeEnergyReadout BranchData SingularityReadout ScaleCoordinate LogCoordinate
      ParityOperator FunctionalEquationReadout SourceDistribution TargetDistribution
      TransportPlan KLReadout Potential EquilibriumSet CriticalLineReadout LieAlgebra
      GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout ZeroModeReadout :
      Type*}
    (M : PrimonFreeEnergyRelativeTraceManifest
      BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout ExplicitFormulaReadout
      SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout BranchData
      SingularityReadout ScaleCoordinate LogCoordinate ParityOperator
      FunctionalEquationReadout SourceDistribution TargetDistribution TransportPlan
      KLReadout Potential EquilibriumSet CriticalLineReadout LieAlgebra GradeMinus
      GradeZero GradePlus EPlus EMinus BalanceReadout ZeroModeReadout) :
    M.freeEnergy.freeEnergy_logDual_law :=
  M.freeEnergy.freeEnergy_logDual_certificate

/-- The manifest includes the KL equilibrium/critical-line witness. -/
theorem equilibrium_criticalLine
    {BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout
      ExplicitFormulaReadout SpectralParameter MajoranaPartition DualPartition
      FreeEnergyReadout BranchData SingularityReadout ScaleCoordinate LogCoordinate
      ParityOperator FunctionalEquationReadout SourceDistribution TargetDistribution
      TransportPlan KLReadout Potential EquilibriumSet CriticalLineReadout LieAlgebra
      GradeMinus GradeZero GradePlus EPlus EMinus BalanceReadout ZeroModeReadout :
      Type*}
    (M : PrimonFreeEnergyRelativeTraceManifest
      BosonicTrace FermionicTrace RelativeTrace PrimeOrbitReadout ExplicitFormulaReadout
      SpectralParameter MajoranaPartition DualPartition FreeEnergyReadout BranchData
      SingularityReadout ScaleCoordinate LogCoordinate ParityOperator
      FunctionalEquationReadout SourceDistribution TargetDistribution TransportPlan
      KLReadout Potential EquilibriumSet CriticalLineReadout LieAlgebra GradeMinus
      GradeZero GradePlus EPlus EMinus BalanceReadout ZeroModeReadout) :
    M.klEquilibrium.equilibrium_criticalLine_law :=
  M.klEquilibrium.equilibrium_criticalLine_certificate

end PrimonFreeEnergyRelativeTraceManifest

end InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace

import InfoGeometry.TraceFormula.FiniteISColimitInverseLimitSearch
import InfoGeometry.Clifford.InductiveColimitCrystal
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit
import InfoGeometry.Canonical.NoncommutativeModularSignum
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.MadelungMetriplecticColimitBridge

/-!
# Operatorial Itakura--Saito colimit framework

This is a composition surface for already verified owners.  It keeps three
levels distinct:

* the finite real log-determinant/trace readout;
* the genuine Fréchet/transport Hessian and its symmetric Onsager sector;
* the contravariant Kubo--Mori transport on the dual inverse system.

No theorem identifying the finite `-log det` potential with the BKM Hessian is
introduced here: that is a separate mathematical statement and is not present
in the current library.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.OperatorialISColimitFramework

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.TraceFormula.FiniteISColimitInverseLimitSearch
open InfoGeometry.Clifford.InductiveColimitCrystal
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit
open InfoGeometry.Canonical.MadelungMetriplecticColimitBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Krein
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.RelationalInformationCore
open SouriauOnsagerBKM

/-! ## Tomita--Takesaki relative modular operator -/

section RelativeModular

variable {R B : Type*}
variable [CommSemiring R] [Semiring B] [Algebra R B]

/--
The finite algebraic realization of the relative modular operator
`Δ_{a|b} = L_a R_{b⁻¹}`.  This is the repository's bounded left/right
Tomita--Takesaki lane; it is not an arbitrary gradient variable.
-/
def tomitaRelativeDelta
    (a b : InfoGeometry.OperatorAlgebra.IndividuatedCasimir.InvertibleTransport B) :
    B →ₗ[R] B :=
  InfoGeometry.Canonical.NoncommutativeModularSignum.lrRelativeModular a b

@[simp]
theorem tomitaRelativeDelta_apply
    (a b : InfoGeometry.OperatorAlgebra.IndividuatedCasimir.InvertibleTransport B)
    (x : B) :
    tomitaRelativeDelta (R := R) a b x = a.val * x * b.inv := by
  exact InfoGeometry.Canonical.NoncommutativeModularSignum.lrRelativeModular_apply
    (R := R) a b x

/-- Product law for the finite left/right modular operators.  The right-hand
    factor reverses order, as required by the noncommutative relative modular
    construction. -/
theorem tomitaRelativeDelta_mul
    (a b c d : InfoGeometry.OperatorAlgebra.IndividuatedCasimir.InvertibleTransport B) :
    tomitaRelativeDelta (R := R) a b * tomitaRelativeDelta (R := R) c d =
      InfoGeometry.Canonical.NoncommutativeModularSignum.leftMul
          (R := R) (a.val * c.val) *
        InfoGeometry.Canonical.NoncommutativeModularSignum.rightMul
          (R := R) (d.inv * b.inv) := by
  exact InfoGeometry.Canonical.NoncommutativeModularSignum.lrRelativeModular_mul
    (R := R) a b c d

/-- The honest three-point cocycle product.  It is intentionally stated with
    the reversed right factor rather than imposing a false commutative law. -/
theorem tomitaRelativeDelta_naive_cocycle_product
    (a b c : InfoGeometry.OperatorAlgebra.IndividuatedCasimir.InvertibleTransport B) :
    tomitaRelativeDelta (R := R) a b * tomitaRelativeDelta (R := R) b c =
      InfoGeometry.Canonical.NoncommutativeModularSignum.leftMul
          (R := R) (a.val * b.val) *
        InfoGeometry.Canonical.NoncommutativeModularSignum.rightMul
          (R := R) (c.inv * b.inv) := by
  exact InfoGeometry.Canonical.NoncommutativeModularSignum.lrRelativeModular_naive_cocycle_product
    (R := R) a b c

end RelativeModular

/-! ## Real UHF stage transport of the bounded modular action -/

section PrimonStageModular

open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.OperatorAlgebra.IndividuatedCasimir

/-- Transport a finite-stage unit through the canonical ring-hom injection. -/
def primonStageUnit (n : ℕ) (u : (MatrixStage n)ˣ) : PrimonUHFAlgebraˣ :=
  Units.map (toColimit n).toMonoidHom u

@[simp] theorem primonStageUnit_val (n : ℕ) (u : (MatrixStage n)ˣ) :
    (primonStageUnit n u).val = toColimit n u.val :=
  rfl

@[simp] theorem primonStageUnit_inv (n : ℕ) (u : (MatrixStage n)ˣ) :
    (primonStageUnit n u).inv = toColimit n u.inv :=
  rfl

/-- The bounded Tomita left/right action commutes with finite-stage injection.

This is the concrete real-carrier link for
`Δ_{a|b}(x) = a * x * b⁻¹`; no logarithm or completion is involved. -/
theorem tomitaRelativeDelta_stage
    (n : ℕ) (a b : (MatrixStage n)ˣ) (x : MatrixStage n) :
    toColimit n (tomitaRelativeDelta (R := ℝ) a b x) =
      toColimit n (a.val * x * b.inv) := by
  rw [tomitaRelativeDelta_apply]

/-- The normalized colimit trace reads the finite relative modular ratio on
the identity carrier. -/
theorem tauInfinity_tomitaRelativeDelta_stage_identity
    (n : ℕ) (a b : (MatrixStage n)ˣ) :
    tauInfinity
        (toColimit n (tomitaRelativeDelta (R := ℝ) a b
          (1 : MatrixStage n))) =
      normalizedTrace n (a.val * b.inv) := by
  rw [tauInfinity_stage]
  simp [tomitaRelativeDelta_apply]

/-! The identity subtraction is the centered relative ratio, now stated on
the genuine finite Tomita relative modular operator. -/
theorem tomitaRelativeDelta_stage_identity_sub_one_eq_centeredRelativeRatio
    (n : ℕ) (a b : (MatrixStage n)ˣ) :
    tomitaRelativeDelta (R := ℝ) a b (1 : MatrixStage n) - 1 =
      InfoGeometry.TraceFormula.ItakuraSaito.centeredRelativeRatio
        a.val b.val := by
  simp [tomitaRelativeDelta_apply,
    InfoGeometry.TraceFormula.ItakuraSaito.centeredRelativeRatio, mul_assoc]

/- The centered relative modular deviation has the native normalized-stage
trace readout in the colimit. -/
theorem tauInfinity_tomitaRelativeDelta_stage_centered_readout
    (n : ℕ) (a b : (MatrixStage n)ˣ) :
    tauInfinity
        (toColimit n
          (tomitaRelativeDelta (R := ℝ) a b (1 : MatrixStage n) - 1)) =
      normalizedTrace n (a.val * b.inv - 1) := by
  rw [tauInfinity_stage]
  simp [tomitaRelativeDelta_apply, mul_assoc]

theorem tauInfinity_tomitaRelativeDelta_stage_conjugation_invariant
    (n : ℕ) (u : (MatrixStage n)ˣ) (x : MatrixStage n) :
    tauInfinity
        (toColimit n
          (tomitaRelativeDelta (R := ℝ) u u x)) =
      tauInfinity (toColimit n x) := by
  rw [tauInfinity_stage, tauInfinity_stage]
  unfold normalizedTrace rawTrace
  rw [tomitaRelativeDelta_apply]
  rw [show u.val * x * u.inv = (u.val * x) * u.inv by simp [mul_assoc]]
  rw [Matrix.trace_mul_comm]
  rw [← mul_assoc]
  have hu : (u.inv : MatrixStage n) * u.val = 1 := Units.inv_mul u
  rw [hu, one_mul]

theorem tauInfinity_commonCarrier_tomitaRelativeDelta_stage_identity
    (n : ℕ) (a b : (MatrixStage n)ˣ) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
            ((clStageEquiv n).symm
              (tomitaRelativeDelta (R := ℝ) a b (1 : MatrixStage n))))) =
      normalizedTrace n (a.val * b.inv) := by
  rw [cliffordBitWordColimitEquiv_ofStage_symm]
  rw [tauInfinity_stage]
  simp [tomitaRelativeDelta_apply]

end PrimonStageModular

/-! ## Complex operator readout of the real Tomita carrier -/

open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

/-- The native complex finite-operator representative of a real BitWord matrix.
This is the coordinate complexification needed to compare the real UHF trace
with the complex BKM functional; it is not a second stage algebra. -/
def realMatrixOperator (n : ℕ) (A : MatrixStage n) :
    SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n) :=
  CblinfunMatrix.matrixOp
    (fun i j =>
      (InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordStageEquivFin n A i j : ℂ))

theorem finiteOperatorTrace_realMatrixOperator
    (n : ℕ) (A : MatrixStage n) :
    SouriauOnsagerBKM.finiteOperatorTrace (realMatrixOperator n A) =
      Complex.ofReal
        (Matrix.trace
          (InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordStageEquivFin n A)) := by
  unfold realMatrixOperator SouriauOnsagerBKM.finiteOperatorTrace
  rw [CblinfunMatrix.matrixOfOp_matrixOp]
  change (∑ i : Fin (2 ^ n),
      (InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordStageEquivFin n A i i : ℂ)) = _
  simp only [Matrix.trace, Matrix.diag_apply]
  push_cast
  rfl

theorem bkm_realMatrixOperator_readout
    (n : ℕ) (s : ℝ) (A : MatrixStage n) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n)) s
        (realMatrixOperator n A) =
      Complex.ofReal (normalizedTrace n A) := by
  rw [maximallyMixed_bkm_kernel_eq_normalized_trace,
    finiteOperatorTrace_realMatrixOperator]
  have htrace :=
    InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordStageEquivFin_trace n A
  unfold normalizedTrace rawTrace
  rw [← htrace]
  push_cast
  ring

/- The real matrix realization preserves the noncommutative product, with
   operator composition on the bounded-operator carrier. -/
theorem realMatrixOperator_mul_comp
    (n : ℕ) (A B : MatrixStage n) :
    (realMatrixOperator n A).comp (realMatrixOperator n B) =
      realMatrixOperator n (A * B) := by
  apply CblinfunMatrix.matrixOfOp_injective
  simp only [realMatrixOperator, CblinfunMatrix.matrixOfOp_comp,
    CblinfunMatrix.matrixOfOp_matrixOp]
  ext i j
  have hmul := congrArg
    (fun M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ => M i j)
    ((InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordStageEquivFin n).map_mul A B)
  have hmulC := congrArg Complex.ofReal hmul
  simpa [Matrix.mul_apply] using hmulC

/- The BKM functional therefore reads a finite Onsager product as the
   normalized real UHF trace of the corresponding matrix product. -/
theorem bkm_realMatrixOperator_product_readout
    (n : ℕ) (s : ℝ) (A B : MatrixStage n) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n)) s
        ((realMatrixOperator n A).comp (realMatrixOperator n B)) =
      Complex.ofReal (normalizedTrace n (A * B)) := by
  rw [realMatrixOperator_mul_comp, bkm_realMatrixOperator_readout]

/- The BKM product readout is the existing finite Onsager trace pairing after
   the canonical BitWord carrier identification. -/
theorem bkm_realMatrixOperator_tracePairingNative_readout
    (n : ℕ) (s : ℝ) (X Y : InfoGeometry.Physics.TraceOperatorSpace (BitWord n)) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n)) s
        ((realMatrixOperator n
            (traceOperatorSpaceMatrixStageEquiv n X)).comp
          (realMatrixOperator n
            (traceOperatorSpaceMatrixStageEquiv n Y))) =
      Complex.ofReal
        ((1 / (2 ^ n : ℝ)) * InfoGeometry.Physics.tracePairingNative X Y) := by
  rw [bkm_realMatrixOperator_product_readout]
  unfold normalizedTrace rawTrace
  have htrace :
      Matrix.trace
          (traceOperatorSpaceMatrixStageEquiv n X *
            traceOperatorSpaceMatrixStageEquiv n Y) =
        InfoGeometry.Physics.tracePairingNative X Y := by
    simpa [rawTrace] using tracePairing_native_eq_rawTrace n X Y
  rw [htrace]

/- The maximally mixed BKM readout is invariant under the same finite Tomita
   conjugation.  This identifies modular invariance on the operator carrier
   with invariance of the normalized real UHF trace. -/
theorem bkm_realMatrixOperator_tomita_conjugation_invariant
    (n : ℕ) (u : (MatrixStage n)ˣ) (s : ℝ) (x : MatrixStage n) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n)) s
        (realMatrixOperator n
          (tomitaRelativeDelta (R := ℝ) u u x)) =
      (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n)) s
        (realMatrixOperator n x) := by
  rw [bkm_realMatrixOperator_readout, bkm_realMatrixOperator_readout]
  have htrace := tauInfinity_tomitaRelativeDelta_stage_conjugation_invariant n u x
  rw [tauInfinity_stage, tauInfinity_stage] at htrace
  exact congrArg Complex.ofReal htrace

/- The existing operator-coordinate filtered colimit reads the real BitWord
    stage through the same BKM functional as the UHF trace.  This is the
    concrete comparison theorem between the operator colimit and the real
    matrix colimit; it uses the repository-owned operator cocone rather than
    introducing a second descent construction. -/
theorem concreteOperator_colimit_realMatrixOperator_readout
    (n : ℕ) (s : ℝ) (A : MatrixStage n) :
    traceColimitFunctional concreteStep concrete_trace_compatible
        (traceColimitInclusion concreteStep n
          (operatorToMatrixLinearMap n (realMatrixOperator n A))) =
      Complex.ofReal (normalizedTrace n A) := by
  change traceColimitFunctional concreteStep concrete_trace_compatible
      (traceColimitInclusion concreteStep n
        (CblinfunMatrix.matrixOfOp (realMatrixOperator n A))) = _
  rw [traceColimitFunctional_inclusion_bkm]
  exact bkm_realMatrixOperator_readout n s A

/- The same filtered-colimit readout for the native noncommutative trace
   pairing.  The product is formed on the bounded-operator carrier first and
   only then transported through `operatorToMatrixLinearMap`; this preserves
   the order-sensitive finite algebra rather than replacing it by a scalar
   diagonal model. -/
theorem concreteOperator_colimit_tracePairingNative_readout
    (n : ℕ) (s : ℝ)
    (X Y : InfoGeometry.Physics.TraceOperatorSpace (BitWord n)) :
    traceColimitFunctional concreteStep concrete_trace_compatible
        (traceColimitInclusion concreteStep n
          (operatorToMatrixLinearMap n
            ((realMatrixOperator n
                (traceOperatorSpaceMatrixStageEquiv n X)).comp
              (realMatrixOperator n
                (traceOperatorSpaceMatrixStageEquiv n Y))))) =
      Complex.ofReal
        ((1 / (2 ^ n : ℝ)) * InfoGeometry.Physics.tracePairingNative X Y) := by
  change traceColimitFunctional concreteStep concrete_trace_compatible
      (traceColimitInclusion concreteStep n
        (CblinfunMatrix.matrixOfOp
          ((realMatrixOperator n
              (traceOperatorSpaceMatrixStageEquiv n X)).comp
            (realMatrixOperator n
              (traceOperatorSpaceMatrixStageEquiv n Y))))) = _
  rw [traceColimitFunctional_inclusion_bkm]
  exact bkm_realMatrixOperator_tracePairingNative_readout n s X Y

theorem tomitaRelativeDelta_bkm_readout_identity
    (n : ℕ) (a b : (MatrixStage n)ˣ) (s : ℝ) :
    Complex.ofReal
        (tauInfinity
          (toColimit n
            (tomitaRelativeDelta (R := ℝ) a b (1 : MatrixStage n)))) =
      (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n)) s
        (realMatrixOperator n (a.val * b.inv)) := by
  rw [tauInfinity_tomitaRelativeDelta_stage_identity,
    bkm_realMatrixOperator_readout]

/-! ## Finite scalar readout and direct-colimit transport -/

abbrev finiteIS := finiteISHamiltonian

abbrev directCarrier := CrystalCarrier

theorem finiteIS_stage_scale_invariant
    (n : ℕ)
    (P Q : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n)
    (c : ℝ) (hc : 0 < c)
    (hQ : IsUnit Q.det) :
    finiteIS n (c • P) (c • Q) = finiteIS n P Q := by
  exact finiteISHamiltonian_scale_invariant n P Q c hc hQ

/-- The finite IS value decomposes into its native colimit-trace ratio
readout, finite normalized log-determinant, and unit normalization. -/
theorem normalized_finiteIS_colimit_readout
    (n : ℕ)
    (P Q : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n) :
    (1 / (2 ^ n : ℝ)) * finiteIS n P Q =
      tauInfinity
          (toColimit n (P * Q⁻¹)) +
        (1 / (2 ^ n : ℝ)) *
          InfoGeometry.TraceFormula.ItakuraSaito.mongeAmperePotential n
            (P * Q⁻¹) - 1 := by
  change (1 / (2 ^ n : ℝ)) *
      InfoGeometry.TraceFormula.ItakuraSaito.itakuraSaitoDivergence n P Q = _
  rw [ItakuraSaito.normalized_itakuraSaitoDivergence_eq]
  rw [tauInfinity_stage]

/-- The same IS decomposition with its ratio term read as the transported
Tomita action on the identity carrier. -/
theorem normalized_finiteIS_modular_readout
    (n : ℕ) (a b : (MatrixStage n)ˣ) :
    (1 / (2 ^ n : ℝ)) * finiteIS n a.val b.val =
      tauInfinity
          (toColimit n
            (tomitaRelativeDelta (R := ℝ) a b (1 : MatrixStage n))) +
        (1 / (2 ^ n : ℝ)) *
          InfoGeometry.TraceFormula.ItakuraSaito.mongeAmperePotential n
            (a.val * b.inv) - 1 := by
  change (1 / (2 ^ n : ℝ)) *
      InfoGeometry.TraceFormula.ItakuraSaito.itakuraSaitoDivergence n
        a.val b.val = _
  rw [ItakuraSaito.normalized_itakuraSaitoDivergence_eq]
  rw [tauInfinity_stage]
  simp [tomitaRelativeDelta_apply, mul_assoc]

theorem normalized_finiteIS_bkm_modular_readout
    (n : ℕ) (a b : (MatrixStage n)ˣ) (s : ℝ) :
    (1 / (2 ^ n : ℝ)) * finiteIS n a.val b.val =
      ((maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
          (1 : SouriauOnsagerBKM.FiniteOperatorAlgebra (2 ^ n)) s
          (realMatrixOperator n (a.val * b.inv))).re +
        (1 / (2 ^ n : ℝ)) *
          InfoGeometry.TraceFormula.ItakuraSaito.mongeAmperePotential n
            (a.val * b.inv) - 1 := by
  have hreadout := congrArg Complex.re
    (tomitaRelativeDelta_bkm_readout_identity n a b s)
  simp only [Complex.ofReal_re] at hreadout
  rw [normalized_finiteIS_modular_readout, hreadout]

theorem direct_logDet_readout_stable
    (m k : ℕ) (A : AtomStage m) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet
        (m + k) (bindAtoms m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A := by
  exact bindAtoms_normalizedLogAbsDet_stable m k A

theorem direct_trace_readout_stable
    (m k : ℕ) (A : AtomStage m) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace
        (m + k) (bindAtoms m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace m A := by
  exact bindAtoms_normalizedTrace_stable m k A

/-! ## Genuine Fréchet/transport Hessian -/

theorem scalar_transport_second_variation
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (ω : (InfoGeometry.Krein.DoubledSpace E →L[ℝ]
      InfoGeometry.Krein.DoubledSpace E) →L[ℝ] ℝ)
    (X A : InfoGeometry.Krein.DoubledSpace E →L[ℝ]
      InfoGeometry.Krein.DoubledSpace E) :
    deriv
        (fun t : ℝ =>
          deriv (fun s : ℝ => scalarTransportReadout ω X A s) t)
        0 =
      ω (operatorInformationHessian X A) := by
  exact deriv2_scalarTransportReadout_zero ω X A

theorem onsager_metric_diagonal
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (P : PotentialDatum (E := E))
    (A : InfoGeometry.Krein.DoubledSpace E →L[ℝ]
      InfoGeometry.Krein.DoubledSpace E)
    (X : InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel E) :
    operatorMetricHessianForm P A X X =
      P.probe (operatorInformationHessian X A) := by
  exact operatorMetricHessianForm_diag P A X

/-! ## Dual inverse transport of the BKM kernel -/

theorem bkm_dual_inverse_composition
    {I : Type*} [Preorder I]
    {dim : I → ℕ}
    (sys : FilteredColimit.DirectInductiveSystem ℂ I
      (InfoGeometry.Canonical.SouriauOnsagerBKMFilteredColimit.OperatorStage dim))
    (D : ∀ i, SouriauOnsagerBKM.FaithfulDensityOperator (dim i))
    (A : ∀ i, SouriauOnsagerBKM.FiniteOperatorAlgebra (dim i))
    (s : ℝ) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    FilteredColimit.InductiveCocone.dualInverseTransition sys hij
        (FilteredColimit.InductiveCocone.dualInverseTransition sys hjk
    (stageKernel dim D A s k)) =
      FilteredColimit.InductiveCocone.dualInverseTransition sys
        (le_trans hij hjk) (stageKernel dim D A s k) := by
  exact stageKernel_dual_inverse_comp dim sys D A s hij hjk

/-! ## Inverse-boundary carrier -/

variable {A : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]

abbrev inverseBoundary :=
  InfoGeometry.Topology.symbolicBoundaryPrefixLimitCompHaus (A := A)

def inverseBoundaryIso :
    InfoGeometry.Topology.symbolicBoundaryCompHaus (A := A) ≅
      inverseBoundary (A := A) :=
  inverseLimitSearchIso (A := A)

theorem inverseBoundaryIso_hom_inv :
    (inverseBoundaryIso (A := A)).hom ≫
        (inverseBoundaryIso (A := A)).inv = 𝟙 _ := by
  exact (inverseBoundaryIso (A := A)).hom_inv_id

theorem inverseBoundaryIso_inv_hom :
    (inverseBoundaryIso (A := A)).inv ≫
        (inverseBoundaryIso (A := A)).hom = 𝟙 _ := by
  exact (inverseBoundaryIso (A := A)).inv_hom_id

end InfoGeometry.TraceFormula.OperatorialISColimitFramework

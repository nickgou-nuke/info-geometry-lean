/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.SupportedProjectors
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityDoubleDerivation
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.GeneratorDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.UnitSquareAction
import InfoGeometry.OperatorAlgebra.PeirceSpine.KleinAction
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityProducts
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityCoboundary
import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential
import InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerCohomology
import InfoGeometry.OperatorAlgebra.PeirceSpine.ComplementSymmetry
import InfoGeometry.OperatorAlgebra.PeirceSpine.LeftRightActions
import InfoGeometry.OperatorAlgebra.PeirceSpine.MixedDifferentials
import InfoGeometry.OperatorAlgebra.PeirceSpine.GeneratorDifferentials
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import InfoGeometry.OperatorAlgebra.PeirceSpine.BoundaryDependence
import InfoGeometry.OperatorAlgebra.PeirceSpine.PrimalDual
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectLevelSet
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferMoments
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralDifferentials
import InfoGeometry.OperatorAlgebra.PeirceSpine.LaplacianHomogenization
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingPerturbation
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectParity
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingTransfer
import InfoGeometry.OperatorAlgebra.PeirceSpine.ModeCoordinates
import InfoGeometry.OperatorAlgebra.PeirceSpine.RingHomTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixColimitTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerPullback

import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityExactness
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.PullbackTriple
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich

import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismCharge

import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeSectors

import InfoGeometry.OperatorAlgebra.PeirceSpine.CornerChargeSectors

import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismBlocks

import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockCharges
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeExtraction
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargePowerMatrix
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeExtractionBalances
import InfoGeometry.OperatorAlgebra.PeirceSpine.CrossChargeBrackets
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockTriangularIntervention
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectLevelExclusions
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.HomogenizedKernels
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdealChartPairing
import InfoGeometry.OperatorAlgebra.PeirceSpine.LogarithmicPullback
import InfoGeometry.OperatorAlgebra.PeirceSpine.PhaseConjugateSteinberg
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichBrackets
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.WilsonPlaquette
import InfoGeometry.OperatorAlgebra.PeirceSpine.DirectedFlowMagneticResolvent
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.MasterCausalPosetD1ToD15
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParpicOperatorSpine

/-!
# Peirce operator spine

This is the verified, modular rewrite of `PureNonCommutativeOperatorSpine`. The
setting is an arbitrary ring `B` with an idempotent `P`. The corners are
`N₊ = P A (1 - P)` and `N₋ = (1 - P) C P`. There are no scalar, diagonal or
commuting models.

Causal poset of the modules:

```
Basic (vocabulary, corner relations, normal form)
 ├─ Tetraktys    A₁–A₁₁  multiplication table, inner-derivation spectra
 │   ├─ ParityDoubleDerivation A₇₃ core: all-X parity intertwining of the Φ/J double commutators
 │   └─ CurvatureDoubleCommutator A₇₄ core: a quadratic relation on Φ and J
 │   └─ Homogenized A₁₃, A₁₅, A₁₇  V-homogenized channels and sandwich character table
 ├─ Unipotent    A₁₂, A₁₄, A₁₆–A₁₉, A₂₁, A₂₂  unipotent groups, braid, ℙ¹(B)
 │   └─ Bergman  A₂₃–A₂₅  Bergman operator, commutator form, Jordan triple
 └─ Supercharge  A₂₆–A₂₈  Q_± derivations, parities, graded derivations
     ├─ ParityProducts: additive orbit sum and exact fixed-product obstruction
     ├─ CentralizerDifferential: square-zero additive endomorphism of the V-centralizer
     │   └─ CentralizerCohomology: kernel modulo image
     ├─ ComplementSymmetry: exchange of corners under P ↦ 1-P
     ├─ DefectTower A₃₉  δ-iteration and orthogonal Peirce-sheet splitting
     ├─ TransferDefect A₃₇  P+Φ quadratic relation, powers, and corrected chiral product
     │   ├─ DefectLevelSet: explicit inverse unit when δ(V)=1 and finite power recurrence
     │   └─ TransferMoments: complementary powers and all-index second-order recurrence
     ├─ ChiralEulerFactors A₄₃–A₄₄  ordered chiral and supercharge factorizations
     └─ CyclotomicBridge  Cayley–Weyl and transfer-element polynomial evaluations
     └─ Orientation A₃₃–A₃₄  ⋆ = L_S, half-twists, d̄ = -⋆d⋆
         └─ LeftRightActions: left and parity-twisted right multiplication
         └─ MixedDifferentials: corrected mixed A₃₀ compositions and squares
         └─ ChiralDifferentials (also ChiralEulerFactors): A₄₃ closure and exact residual
             └─ GeneratorDifferentials: A₃₁ evaluations on S, Φ, J, V, Σ
         └─ LaplacianHomogenization (also Homogenized): corrected A₃₂ scaled generation
InnerPullback A₅₁: two-cone pullbacks and exact residual for the proposed ordinary Maurer–Cartan equation
 └─ PullbackTriple: associative Jordan triple identity and ordered pullback formulas
SandwichCharge A₅₂: five actual charge sectors in End(B), corner charge table, fifth-order annihilator
 └─ ChargeExtraction A₅₃: scaled integer extraction of all five corner operators
     ├─ ChargeExtractionBalances: corrected ±1 factors (3 for sum/difference; 6 after combining)
     └─ CrossChargeBrackets A₅₄: cross-grade bracket table with crossed extremal supports
DefectParity (from TransferDefect and ParityProducts): even/odd defect decomposition
GradingPerturbation (from ChiralEulerFactors): shifted grading and exact defect grades
TripotentDefect A₅₆–A₅₇: tripotent defect calculus and orthogonal three-corner idempotent identities
 ├─ GradingTransfer (also TransferDefect): discriminants and double-commutator identities
 │   └─ ModeCoordinates: invertible coordinate change when 1+V is a unit
 └─ RingHomTransport (also Homogenized): polynomial naturality
     └─ MatrixColimitTransport (also Cl11TensorTowerLimit): actual matrix-limit coherence
Bridge: identification with Core.PeirceDecomposition, Core.IdempotentCartan,
        SquareZeroPairSpectral (Orientation, InnerDerivationSpectra)
```

The intake had false conjuncts in A₁₄, A₁₆, A₂₁, A₂₃, A₂₈ and A₃₄. Each module
docstring lists the corrected forms. Intake A₂₀ (`x = x`) has no content and was
dropped. Later transcript versions include A₂₉–A₃₂ statements. Their definitions
`superDerivPhiBar`, `superDerivJBar`, and `hodgeLaplacianPhi` are given in
`Orientation`; corrected A₃₂ scaled generation is in `LaplacianHomogenization`.

The later A₅₁–A₅₄ intake is also normalized against the owner files above:
the pullback is not asserted to satisfy a Maurer–Cartan flatness equation, the
charge sectors are submodules of `Module.End ℤ B` (not a direct-sum claim), and
the A₅₃ extraction factors are kept scaled over arbitrary rings. In A₅₄ the
extremal bracket has crossed `Q₊`/`Q₋` supports; the same-support formula has a
separately proved residual in `CrossChargeBrackets`.

`TripotentDefect` records polynomial consequences in an arbitrary ring and
their orthogonal three-corner specialization. It does not infer an `su(3)`
action or a color symmetry group from tripotency.
-/

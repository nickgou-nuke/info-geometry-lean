import InfoGeometry.OperatorAlgebra.PeirceSpine.SupportedProjectors
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
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

import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityExactness
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.PullbackTriple

import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismCharge

import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeSectors

import InfoGeometry.OperatorAlgebra.PeirceSpine.CornerChargeSectors

import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismBlocks

import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockCharges
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeExtractionBalances
import InfoGeometry.OperatorAlgebra.PeirceSpine.CrossChargeBrackets

import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeExtractionBalances
import InfoGeometry.OperatorAlgebra.PeirceSpine.CrossChargeBrackets

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
 │   └─ Homogenized A₁₃, A₁₅  V-homogenized projectors
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
DefectParity (from TransferDefect and ParityProducts): even/odd defect decomposition
GradingPerturbation (from ChiralEulerFactors): shifted grading and exact defect grades
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
-/

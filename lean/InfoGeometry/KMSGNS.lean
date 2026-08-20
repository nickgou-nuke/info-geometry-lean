import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

import InfoGeometry.Modular.ExactSequence
import InfoGeometry.Modular.Noncommutative
import InfoGeometry.Modular.TrifoldRadonNikodymBridge
import InfoGeometry.Modular.ConcreteOperatorModularBridge
import InfoGeometry.NCG.NoncommutativeKMSModularState
import InfoGeometry.NCG.CuntzColimitShiftKMSGNSBridge
import InfoGeometry.NCG.CategoricalInductiveColimitKMSBridge
import InfoGeometry.NCG.CategoricalColimitStateDescent
import InfoGeometry.TraceFormula.ColimitTrace

/-!
# KMS-GNS Core: Single Source of Truth

This module is the **canonical consolidation point** for all noncommutative
KMS (Kubo-Martin-Schwinger) and GNS (Gel'fand-Naimark-Segal) theories in the
repository.

## Canonical Owner Files

| Concept | Owner File | Key Theorems |
|:---|:---|:---|
| Modular derivation algebra | `InfoGeometry.Modular.ExactSequence` | `adK`, `dual_flow_commutator`, `modularDerivation` |
| Noncommutative dlog | `InfoGeometry.Modular.Noncommutative` | `dlogL`, `dlogR`, `dlogL_mul_noncommutative` |
| Trifold synthesis | `InfoGeometry.Modular.TrifoldRadonNikodymBridge` | `trifold_reconstruction`, `trace_K_zero`, `superTrace_K_zero` |
| Concrete modular bridge | `InfoGeometry.Modular.ConcreteOperatorModularBridge` | `concrete_modular_deriv_eq_adK` |
| KMS modular state | `InfoGeometry.NCG.NoncommutativeKMSModularState` | `connes_cyclic_1_cocycle_identity`, `noncommutativeSLDFisher_symm` |
| Cuntz KMS/GNS | `InfoGeometry.NCG.CuntzColimitShiftKMSGNSBridge` | Cuntz relations, shift Φ, KMS invariance |
| Colimit KMS descent | `InfoGeometry.NCG.CategoricalInductiveColimitKMSBridge` | Modular automorphism intertwining |
| GNS tower | `InfoGeometry.NCG.CategoricalColimitStateDescent` | GNS isometric embedding |
| Colimit trace | `InfoGeometry.TraceFormula.ColimitTrace` | `colimitTrace`, `normalizedTraceLin` |

## Usage

Import this module to get the complete kernel-checked KMS-GNS framework:

```lean
import InfoGeometry.KMSGNS
```

All downstream bridge files should re-export from here rather than
re-implementing core definitions.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.KMSGNS

-- ============================================================================
-- SECTION 1: Modular Derivation Algebra (native Derivation A)
-- ============================================================================

open InfoGeometry.Modular.ExactSequence

-- Core definitions exported from ExactSequence:
--   adK : A → A → A
--   modularDerivation : A → Derivation A
--   derivationCommutator : Derivation A → Derivation A → Derivation A
--   dual_flow_commutator : master [D, ad_K] = ad_{D(K)}
--   adiabatic_commutator_zero : D(K)=0 ⟹ [D, ad_K]=0
--   central_commutator_zero : K central ⟹ [D, ad_K]=0

-- ============================================================================
-- SECTION 2: Noncommutative Logarithmic Derivations
-- ============================================================================

open InfoGeometry.Modular.Noncommutative

-- Core noncommutative definitions:
--   adK : A → A → A (ℤ-linear)
--   adK_is_derivation : Leibniz rule
--   adK_one : adK K 1 = 0
--   IsNCDerivation : Prop
--   dlogL : (A →ₗ[ℤ] A) → Aˣ → A
--   dlogR : (A →ₗ[ℤ] A) → Aˣ → A
--   dlogL_mul_noncommutative : Maurer-Cartan rule
--   dlogL_inv_eq_neg_dlogR : inversion duality
--   rnUnit : Aˣ → Aˣ → Aˣ
--   dlogL_rnUnit : relative RN logarithmic derivative

-- ============================================================================
-- SECTION 3: Bundled Noncommutative Derivations
-- ============================================================================

-- NOTE: InfoGeometry.Modular.NoncommutativeRadonNikodymDLog defines
-- overlapping symbols (NoncommutativeDerivation, dlogL, etc.).
-- Use qualified access to avoid collisions:
--   NoncommutativeRadonNikodymDLog.NoncommutativeDerivation
--   NoncommutativeRadonNikodymDLog.dlogL
--   NoncommutativeRadonNikodymDLog.rnUnit

-- ============================================================================
-- SECTION 4: Trifold Synthesis
-- ============================================================================

-- The TrifoldRadonNikodymBridge theorems live in InfoGeometry.Modular
-- namespace. Reference them with full paths:
--   InfoGeometry.Modular.alphaCommon
--   InfoGeometry.Modular.betaChiral
--   InfoGeometry.Modular.K_zero
--   InfoGeometry.Modular.trace_K_zero
--   InfoGeometry.Modular.superTrace_K_zero
--   InfoGeometry.Modular.trifold_reconstruction

-- ============================================================================
-- SECTION 5: Concrete Operator Modular Bridge
-- ============================================================================

open InfoGeometry.Modular.ConcreteBridge

--   concrete_modular_deriv_eq_adK
--   concrete_modular_deriv_leibniz
--   derivation_concrete_modular_deriv_comm

-- ============================================================================
-- SECTION 6: Noncommutative KMS Modular State
-- ============================================================================

open InfoGeometry.NCG.KMS

--   TracialFunctional, AlgebraDerivation
--   innerAlgebraDerivation
--   connesCyclic1Cocycle
--   connes_cyclic_1_cocycle_identity
--   noncommutativeSLDFisher

-- ============================================================================
-- SECTION 7: Cuntz Algebras, Shift, KMS, GNS
-- ============================================================================

open InfoGeometry.NCG.CuntzColimit

--   Cuntz algebra relations, shift Φ, KMS invariance, GNS

-- ============================================================================
-- SECTION 8: Categorical Colimit KMS Descent
-- ============================================================================

open InfoGeometry.NCG.ColimitKMS

--   Filtered inductive systems, modular automorphism intertwining

-- ============================================================================
-- SECTION 9: GNS Tower
-- ============================================================================

open InfoGeometry.NCG

--   GNS tower isometries, state cocones

-- ============================================================================
-- SECTION 10: Colimit Trace
-- ============================================================================

open InfoGeometry.TraceFormula.ColimitTrace

--   normalizedTraceLin, colimitTrace, tauInfinity

end InfoGeometry.KMSGNS

end noncomputable section

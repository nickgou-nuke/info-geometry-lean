import InfoGeometry.Canonical.RealBdGDIIIAtom
import InfoGeometry.Canonical.KleinBottleTopology
import InfoGeometry.KK.Product
import InfoGeometry.KK.RealSplitKKTBridge
import InfoGeometry.OperatorAlgebra.AndreevBoundary
import InfoGeometry.Physics.FermionicAndreevReflection
import InfoGeometry.Projective.AndreevHorizonUnitarity
import InfoGeometry.Projective.FiveGradedTopologicalBridge

/-!
# Kasparov/Krein DIII Bridge

#### BUCKET 1: CLOSED FINITE THEOREMS

- `finite_andreev_diii_signature_packet`
- `canonical_diii_proxy_sign_readback`
- `canonical_diii_proxy_root_readback`
- `krein_kasparov_grade_split_from_witness`
- `krein_kasparov_mixed_commutator_gZero`
- `klein_bottle_trace_absorption`

#### BUCKET 2: CONDITIONAL INTERFACES

- `kasparov_product_cycle_readback` reads the output cycle from an explicitly
  supplied `KasparovProductData`.

#### BUCKET 3: OPEN CLOSURE DEBT

- Construct a genuine Kasparov product theorem for the real split-Krein cycles.
- Prove a geometric theorem identifying an event horizon with an Andreev
  boundary.
- Replace the `KleinBottleTopology` trace interface by a full KO-theoretic
  anomaly theorem.
- Relate any Betti/rank certificate to protected Majorana modes only after the
  external de Rham computation is genuinely certified.

This module deliberately avoids asserting a physical DIII theorem for spacetime.
It records the finite algebraic
compatibilities currently available in the repo:

1. finite Andreev particle-hole rotation;
2. canonical DIII symmetry laws on the doubled real BdG carrier;
3. split-Krein KKT decomposition for a supplied Kasparov cycle witness;
4. matrix-level Klein-bottle trace absorption under explicit orthogonality and
   trace-zero hypotheses.
-/

open scoped InnerProductSpace

namespace KasparovKreinDIIIBridge

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.RealBdGDIIIAtom
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKKTBridge
open InfoGeometry.OperatorAlgebra.AndreevBoundary
open InfoGeometry.Physics.FermionicAndreevReflection
open InfoGeometry.Projective.AndreevHorizonUnitarity
open InfoGeometry.Projective.Topology

-- 1. Finite Andreev/DIII horizon readout.

/--
Finite DIII/Andreev signature packet at the projective horizon readout.

This combines:
* the finite Andreev rotation square `A² = -1`;
* preservation of the finite electron/hole squared amplitude;
* the finite Andreev rotation fourth power `A⁴ = 1`;
* the electron/hole channel flip square `C² = 1`;
* the concrete `2×2` horizon isometry plus trace-zero/GW readback.
-/
theorem finite_andreev_diii_signature_packet
    (state : InfallingParticle)
    (ψ : AndreevAmplitude) :
    AndreevTwin (AndreevTwin state) = -state ∧
      InfoGeometry.Physics.FermionicAndreevReflection.amplitudeNormSq
          (AndreevTwin state) =
        InfoGeometry.Physics.FermionicAndreevReflection.amplitudeNormSq
          state ∧
      AndreevTwin (AndreevTwin (AndreevTwin (AndreevTwin state))) = state ∧
      andreevFlipLinear (andreevFlipLinear ψ) = ψ ∧
      ((concreteAndreevHorizonSMatrix.closure.moebiusParity.transpose *
          concreteAndreevHorizonSMatrix.closure.moebiusParity =
            concreteAndreevHorizonSMatrix.closure.I) ∧
        concreteAndreevHorizonSMatrix.closure.gromovWittenIndex = 0) := by
  exact ⟨
    andreevTwin_sq state,
    andreevTwin_normSq state,
    andreevTwin_fourth state,
    andreevFlipLinear_sq ψ,
    concreteAndreevHorizon_information_preservation⟩

-- 2. Canonical DIII symmetry laws on the doubled real BdG carrier.

section CanonicalDIII

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/-- Read back the canonical DIII proxy signs from the canonical owner. -/
theorem canonical_diii_proxy_sign_readback :
    let P := canonicalDIIIProxy (E := E)
    P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
      ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
      ∧ P.T.comp P.C = P.S
      ∧ P.C.comp P.T = -P.S := by
  exact ⟨(canonicalDIIIProxy (E := E)).T_sq,
    (canonicalDIIIProxy (E := E)).C_sq,
    (canonicalDIIIProxy (E := E)).TC_eq_S,
    (canonicalDIIIProxy (E := E)).CT_eq_neg_S⟩

/-- Root-name readback for the canonical DIII proxy. -/
theorem canonical_diii_proxy_root_readback :
    let P := canonicalDIIIProxy (E := E)
    P.T = InfoGeometry.Krein.complex_i (E := E)
      ∧ P.C = InfoGeometry.Krein.modular_j (E := E)
      ∧ P.S = -(InfoGeometry.Krein.spectral_epsilon (E := E))
      ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
      ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
      ∧ P.T.comp P.C = -(InfoGeometry.Krein.spectral_epsilon (E := E))
      ∧ P.C.comp P.T = InfoGeometry.Krein.spectral_epsilon (E := E) := by
  refine ⟨canonicalDIIIProxy_T_eq_complex_i (E := E),
    canonicalDIIIProxy_C_eq_modular_j (E := E),
    canonicalDIIIProxy_S_eq_neg_spectral_epsilon (E := E), ?_, ?_, ?_, ?_⟩
  · exact (canonicalDIIIProxy (E := E)).T_sq
  · exact (canonicalDIIIProxy (E := E)).C_sq
  · simpa [canonicalDIIIProxy_S_eq_neg_spectral_epsilon (E := E)] using
      (canonicalDIIIProxy (E := E)).TC_eq_S
  · simpa [canonicalDIIIProxy_S_eq_neg_spectral_epsilon (E := E)] using
      (canonicalDIIIProxy (E := E)).CT_eq_neg_S

end CanonicalDIII

-- 3. Split-Krein Kasparov/KKT readouts.

section KreinKasparov

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [InfoGeometry.Krein.KreinSpace H]
variable [InfoGeometry.Krein.KreinGradedModule H]

/--
Given the explicit `gradeCLM = eps` witness, the odd phase of the real
split-Krein Kasparov cycle splits into `g₁ ⊕ g₋₁`.
-/
theorem krein_kasparov_grade_split_from_witness
    (X : RealSplitKreinKasparovCycle A B H)
    (w : GradeEpsWitness X) :
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F :=
  F_eq_gOnePart_add_gNegOnePart_of_witness (X := X) w

/--
The mixed `g₁/g₋₁` commutator of the odd phase closes in grade zero.
-/
theorem krein_kasparov_mixed_commutator_gZero
    (X : RealSplitKreinKasparovCycle A B H) :
    IsGZero X.cl11
      (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) :=
  commutator_gOne_gNegOne_isGZero (X := X.cl11) X.F X.F

end KreinKasparov

-- 4. Explicit Kasparov-product interface.

section KasparovProduct

variable {A B C H₁ H₂ P : Type*}
variable [NormedRing A] [NormedRing B] [NormedRing C]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAlgebra ℝ C]
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [InfoGeometry.Krein.KreinSpace H₁]
variable [InfoGeometry.Krein.KreinGradedModule H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable [InfoGeometry.Krein.KreinSpace H₂]
variable [InfoGeometry.Krein.KreinGradedModule H₂]
variable [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
variable [InfoGeometry.Krein.KreinSpace P]
variable [InfoGeometry.Krein.KreinGradedModule P]
variable (X : KasparovCycle A B H₁)
variable (Y : KasparovCycle B C H₂)

/--
Read back the product cycle from an explicitly supplied Kasparov product datum.

This is an interface theorem, not a construction of the interior tensor product.
-/
theorem kasparov_product_cycle_readback
    (D : KasparovProductData A B C H₁ H₂ P X Y) :
    ∃ Z : KasparovCycle A C P, Z = D.out :=
  ⟨D.out, rfl⟩

end KasparovProduct

-- 5. Klein-bottle trace absorption interface.

/--
Matrix-level Klein-bottle trace absorption under explicit orthogonality and
trace-zero hypotheses.
-/
theorem klein_bottle_trace_absorption
    (M : Matrix (Fin 32) (Fin 32) ℝ)
    (Pparity : Matrix (Fin 32) (Fin 32) ℝ)
    (hOrth : Pparity.transpose * Pparity = 1)
    (hTrace : Matrix.trace M = 0) :
    Matrix.trace
      (InfoGeometry.Canonical.KleinBottleTopology.klein_gluing M Pparity) = 0 :=
  InfoGeometry.Canonical.KleinBottleTopology.klein_topology_trace_closure
    M Pparity hOrth hTrace

/-- Concrete `2×2` topological socket readback of finite Andreev/DIII isometry and
trace-zero data. -/
theorem concreteTopologicalSocket2_packet :
    (concreteTopologicalSocket2.inv.closure.moebiusParity.transpose *
        concreteTopologicalSocket2.inv.closure.moebiusParity =
      concreteTopologicalSocket2.inv.closure.I) ∧
    concreteTopologicalSocket2.inv.closure.gromovWittenIndex = 0 := by
  simpa [concreteTopologicalSocket2] using
    concreteAndreevHorizon_information_preservation

end KasparovKreinDIIIBridge

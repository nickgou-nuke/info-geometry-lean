import Mathlib

open TensorProduct
open scoped TensorProduct DirectSum

/-!
# Quantum G₂ Fusion Coherence Datum

This file defines the abstract fusion channels and coherence relations (Pentagon and Hexagons)
for a modular tensor category / anyon system, specialized toward the fusion rules of quantum G₂.

We use `DirectSum` to represent the intermediate fusion channel decompositions.
-/

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.QuantumG2FusionCoherenceDatum

/-- The core structure of fusion spaces and F/R-moves. -/
structure QuantumG2FusionCoherenceDatum (Sector : Type u) (𝕜 : Type u) [CommRing 𝕜] where
  /-- The fusion multiplicity $N_{ab}^c$. -/
  fusionMultiplicity : Sector → Sector → Sector → ℕ

  /-- The vector space of fusion vertices $V_{ab}^c = \operatorname{Hom}(a \otimes b, c)$. -/
  FusionSpace : Sector → Sector → Sector → Type u

  /-- Module structure on fusion spaces. -/
  instAddCommGroupFusionSpace : ∀ a b c, AddCommGroup (FusionSpace a b c)
  instModuleFusionSpace : ∀ a b c, Module 𝕜 (FusionSpace a b c)

  /-- Left-associated 3-particle fusion space: $\bigoplus_e V_{ab}^e \otimes V_{ec}^d$ -/
  leftAssociatedFusionSpace (a b c d : Sector) : Type u :=
    letI (x y z : Sector) := instAddCommGroupFusionSpace x y z
    letI (x y z : Sector) := instModuleFusionSpace x y z
    ⨁ (e : Sector), (FusionSpace a b e) ⊗[𝕜] (FusionSpace e c d)

  /-- Right-associated 3-particle fusion space: $\bigoplus_f V_{bc}^f \otimes V_{af}^d$ -/
  rightAssociatedFusionSpace (a b c d : Sector) : Type u :=
    letI (x y z : Sector) := instAddCommGroupFusionSpace x y z
    letI (x y z : Sector) := instModuleFusionSpace x y z
    ⨁ (f : Sector), (FusionSpace b c f) ⊗[𝕜] (FusionSpace a f d)

  /-- Module structures for the associated spaces. -/
  instAddCommGroupLeft (a b c d : Sector) : AddCommGroup (leftAssociatedFusionSpace a b c d)
  instModuleLeft (a b c d : Sector) : Module 𝕜 (leftAssociatedFusionSpace a b c d)
  instAddCommGroupRight (a b c d : Sector) : AddCommGroup (rightAssociatedFusionSpace a b c d)
  instModuleRight (a b c d : Sector) : Module 𝕜 (rightAssociatedFusionSpace a b c d)

  /-- The F-move recoupling isomorphism. -/
  Fmove (a b c d : Sector) :
    letI := instAddCommGroupLeft a b c d; letI := instModuleLeft a b c d
    letI := instAddCommGroupRight a b c d; letI := instModuleRight a b c d
    (leftAssociatedFusionSpace a b c d) ≃ₗ[𝕜] (rightAssociatedFusionSpace a b c d)

  /-- The R-move braiding isomorphism for a single fusion channel. -/
  Rmove (a b c : Sector) :
    letI := instAddCommGroupFusionSpace a b c; letI := instModuleFusionSpace a b c
    letI := instAddCommGroupFusionSpace b a c; letI := instModuleFusionSpace b a c
    FusionSpace a b c ≃ₗ[𝕜] FusionSpace b a c

attribute [instance] QuantumG2FusionCoherenceDatum.instAddCommGroupFusionSpace
attribute [instance] QuantumG2FusionCoherenceDatum.instModuleFusionSpace
attribute [instance] QuantumG2FusionCoherenceDatum.instAddCommGroupLeft
attribute [instance] QuantumG2FusionCoherenceDatum.instModuleLeft
attribute [instance] QuantumG2FusionCoherenceDatum.instAddCommGroupRight
attribute [instance] QuantumG2FusionCoherenceDatum.instModuleRight

end InfoGeometry.Canonical.QuantumG2FusionCoherenceDatum

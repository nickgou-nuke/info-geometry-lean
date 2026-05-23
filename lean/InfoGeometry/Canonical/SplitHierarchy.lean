import InfoGeometry.Algebraic.SplitSuperGeometry
import InfoGeometry.Canonical.Cl44ConformalNormalization

/-!
# Split hierarchy readout

This file records a conservative diagnostic layer for the split hierarchy:

* split-complex / split-quaternion / split-octonion labels are treated as
  readout tiers, not as a theorem that split octonions or an `E₈` manifold have
  been constructed here;
* the local doubled-real split Clifford seed is exposed through the canonical
  `SplitSuperGeometry` carrier;
* the `so(4,4)` triality placement and the corrected `Cl(4,4)` conformal
  normalization are re-exported from the existing owner surfaces.

The file is intentionally small.  It provides an interface packet that keeps
the null-cone / projective / conformal layers distinct from the current-algebra
and boundary-gap files.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitHierarchy

open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Algebraic.SplitSuperGeometry
open InfoGeometry.Canonical.Cl44ConformalNormalization

/--
Tier labels for the split hierarchy.

The labels are diagnostic readouts only:
* `splitComplex` corresponds to the local `Cl(1,1)` seed;
* `splitQuaternion` corresponds to the next hyperbolic tier;
* `splitOctonion` is the `Cl(4,4)` triality readout tier;
* `projectiveBoundary` is the null / boundary closure label.
-/
inductive SplitHierarchyTier where
  | splitComplex
  | splitQuaternion
  | splitOctonion
  | projectiveBoundary
  deriving DecidableEq, Repr

/-- Signature readout associated with each hierarchy tier. -/
def tierSignature : SplitHierarchyTier → Nat × Nat
  | .splitComplex => (1, 1)
  | .splitQuaternion => (2, 2)
  | .splitOctonion => (4, 4)
  | .projectiveBoundary => (0, 0)

@[simp] theorem tierSignature_splitComplex :
    tierSignature .splitComplex = (1, 1) :=
  rfl

@[simp] theorem tierSignature_splitQuaternion :
    tierSignature .splitQuaternion = (2, 2) :=
  rfl

@[simp] theorem tierSignature_splitOctonion :
    tierSignature .splitOctonion = (4, 4) :=
  rfl

@[simp] theorem tierSignature_projectiveBoundary :
    tierSignature .projectiveBoundary = (0, 0) :=
  rfl

/--
A split hierarchy packet records a split Clifford carrier together with its
diagnostic hierarchy tier and signature readout.

No claim is made here that the `splitOctonion` tier is an actual split
octonion algebra; it is only the `Cl(4,4)` triality readout level used by the
repo's conformal corridor.
-/
structure SplitHierarchyPacket (n : ℕ) where
  tier : SplitHierarchyTier
  geometry : SplitSuperGeometry n
  parity : ParityInvolution (Cl_nn n)
  parity_eq : parity = geometry.parity
  signature : Nat × Nat
  signature_eq : signature = tierSignature tier

namespace SplitHierarchyPacket

variable {n : ℕ}

/-- The parity involution attached to the packet is the underlying carrier parity. -/
@[simp] theorem parity_eq_geometry_parity
    (P : SplitHierarchyPacket n) :
    P.parity = P.geometry.parity :=
  P.parity_eq

/-- The packet signature is exactly the tier readout. -/
@[simp] theorem signature_eq_tierSignature
    (P : SplitHierarchyPacket n) :
    P.signature = tierSignature P.tier :=
  P.signature_eq

end SplitHierarchyPacket

/-- Canonical local doubled-real split seed at tier `splitComplex`. -/
def canonicalSplitComplexPacket : SplitHierarchyPacket 1 where
  tier := .splitComplex
  geometry := SplitSuperGeometry.canonical 1
  parity := splitCliffordParityInvolution 1
  parity_eq := rfl
  signature := tierSignature .splitComplex
  signature_eq := rfl

/-- Canonical hyperbolic intermediate tier at `Cl(2,2)`. -/
def canonicalSplitQuaternionPacket : SplitHierarchyPacket 2 where
  tier := .splitQuaternion
  geometry := SplitSuperGeometry.canonical 2
  parity := splitCliffordParityInvolution 2
  parity_eq := rfl
  signature := tierSignature .splitQuaternion
  signature_eq := rfl

/-- Canonical triality readout tier at `Cl(4,4)`. -/
def canonicalSplitOctonionPacket : SplitHierarchyPacket 4 where
  tier := .splitOctonion
  geometry := SplitSuperGeometry.canonical 4
  parity := splitCliffordParityInvolution 4
  parity_eq := rfl
  signature := tierSignature .splitOctonion
  signature_eq := rfl

/-- The local split-complex seed is inhabited by the canonical packet. -/
theorem localSeed_inhabited :
    Nonempty (SplitHierarchyPacket 1) :=
  ⟨canonicalSplitComplexPacket⟩

/-- The split-quaternion tier is inhabited by the canonical packet. -/
theorem quaternionTier_inhabited :
    Nonempty (SplitHierarchyPacket 2) :=
  ⟨canonicalSplitQuaternionPacket⟩

/-- The split-octonion readout tier is inhabited by the canonical packet. -/
theorem octonionTier_inhabited :
    Nonempty (SplitHierarchyPacket 4) :=
  ⟨canonicalSplitOctonionPacket⟩

/--
Diagnostic split-hierarchy corridor.

This packages the existing local seed, the `Cl(4,4)` triality placement, and
the corrected conformal normalization as a single readout.  It does not claim
an `E₈` theorem or a signature-selection theorem.
-/
structure SplitHierarchyDiagnostic where
  localSeed : Nonempty (SplitHierarchyPacket 1)
  quaternionTier : Nonempty (SplitHierarchyPacket 2)
  octonionTier : Nonempty (SplitHierarchyPacket 4)
  trialityPlacement : Nonempty TrialityLeviPlacement
  conformalNormalization : Cl44ConformalNormalizationOwnerTarget

/-- Canonical diagnostic readout for the split hierarchy corridor. -/
def canonicalDiagnostic : SplitHierarchyDiagnostic where
  localSeed := localSeed_inhabited
  quaternionTier := quaternionTier_inhabited
  octonionTier := octonionTier_inhabited
  trialityPlacement := ⟨TrialityLeviPlacement.canonical⟩
  conformalNormalization := cl44ConformalNormalizationOwnerTarget

/-- The canonical diagnostic has the canonical local seed. -/
theorem canonicalDiagnostic_localSeed :
    canonicalDiagnostic.localSeed = localSeed_inhabited :=
  rfl

/-- The canonical diagnostic has the canonical triality placement. -/
theorem canonicalDiagnostic_trialityPlacement :
    canonicalDiagnostic.trialityPlacement = ⟨TrialityLeviPlacement.canonical⟩ :=
  rfl

end InfoGeometry.Canonical.SplitHierarchy

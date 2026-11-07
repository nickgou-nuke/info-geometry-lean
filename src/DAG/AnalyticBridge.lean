import DAG.CocycleBridgeActivation
import InfoGeometry.Clifford.CliffordBott
import InfoGeometry.Canonical.SplitCliffordDirectLimit

/-!
# DAG.AnalyticBridge

Checked readout of the DAG cocycle bridge into the repo-owned split Clifford
direct-limit tower.  The direct-limit construction and Bott-step maps are owned
by `InfoGeometry.Canonical.SplitCliffordDirectLimit`; this file only exposes the
names needed by the DAG layer.
-/

noncomputable section

namespace DAG.AnalyticBridge

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.CliffordBott

/-- DAG-facing alias for the repo-owned split Clifford direct limit. -/
abbrev UHFAlgebra : Type :=
  SplitCliffordInfinity

/-- DAG-facing alias for the owner stage map into the direct limit. -/
def uhfOf (n : ℕ) : SplitClNNAlg n →+* UHFAlgebra :=
  ofStage n

@[simp]
theorem uhfOf_map (m n : ℕ) (h : m ≤ n) (x : SplitClNNAlg m) :
    uhfOf n (splitCliffordMap m n h x) = uhfOf m x :=
  ofStage_map m n h x

/-- Harmonic-vacuum finite flow: the stationary direct-limit readout is identity. -/
def finiteFlow (n : ℕ) (_t : ℝ) (x : SplitClNNAlg n) : SplitClNNAlg n :=
  x

@[simp]
theorem finiteFlow_apply (n : ℕ) (t : ℝ) (x : SplitClNNAlg n) :
    finiteFlow n t x = x :=
  rfl

@[simp]
theorem flow_commutes_with_splitCliffordMap
    (m n : ℕ) (h : m ≤ n) (t : ℝ) (x : SplitClNNAlg m) :
    finiteFlow n t (splitCliffordMap m n h x)
      = splitCliffordMap m n h (finiteFlow m t x) :=
  rfl

/-- The induced harmonic-vacuum modular flow on the direct-limit algebra. -/
def uhfModularFlow (_t : ℝ) : UHFAlgebra → UHFAlgebra :=
  id

@[simp]
theorem uhfModularFlow_apply (t : ℝ) (z : UHFAlgebra) :
    uhfModularFlow t z = z :=
  rfl

@[simp]
theorem uhfModularFlow_stage (n : ℕ) (t : ℝ) (x : SplitClNNAlg n) :
    uhfModularFlow t (uhfOf n x) = uhfOf n (finiteFlow n t x) :=
  rfl

@[simp]
theorem uhfModularFlow_add (s t : ℝ) :
    uhfModularFlow (s + t) = uhfModularFlow s ∘ uhfModularFlow t :=
  rfl

/-- The owner direct-limit nilpotent shield is available through the DAG bridge. -/
theorem analytic_completion_has_nilpotent_lift :
    ∃ ε : UHFAlgebra, ε * ε = 0 :=
  cl_infty_has_nilpotent_lift

/--
The harmonic-vacuum Connes cocycle equation in the stationary direct-limit
readout.  Here the implemented flow is identity; nontrivial analytic cocycles
remain owned by the volume/operator-algebra lane.
-/
theorem connes_cocycle_at_limit (s t : ℝ) :
    uhfModularFlow (s + t) = uhfModularFlow s ∘ uhfModularFlow t :=
  uhfModularFlow_add s t

/-- Build the existing three-layer cocycle bridge from a finite two-complex. -/
def fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) :
    DAG.CocycleBridgeActivation.CocycleBridge α :=
  DAG.CocycleBridgeActivation.fromTwoComplex tc

end DAG.AnalyticBridge

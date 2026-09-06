import Mathlib
import InfoGeometry.Topology.ChiralOperatorSageLatentChart
import InfoGeometry.Topology.ChiralOperatorTopologicalBraidAction

/-!
# Tensor-factor braid action on the Sage latent feature space

The feature space has the exact operator-valued coordinates
`(u+, s+0, s+1, s+2, u-, s-0, s-1, s-2)`.  This owner places the external
tensor-factor permutations on products of that feature space and proves
their chart transport from the operator carrier.  It does not add a product
to the observational quotient and does not alter Zorn multiplication.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

abbrev OperatorSageFeatureTensor2 A :=
  OperatorSageFeatureSpace A × OperatorSageFeatureSpace A

abbrev OperatorSageFeatureTensor3 A :=
  OperatorSageFeatureSpace A ×
    OperatorSageFeatureSpace A ×
      OperatorSageFeatureSpace A

def operatorSageFeatureTensorSwap
    (p : OperatorSageFeatureTensor2 A) :
    OperatorSageFeatureTensor2 A :=
  (p.2, p.1)

def operatorSageFeatureTensorR12
    (p : OperatorSageFeatureTensor3 A) :
    OperatorSageFeatureTensor3 A :=
  (p.2.1, p.1, p.2.2)

def operatorSageFeatureTensorR23
    (p : OperatorSageFeatureTensor3 A) :
    OperatorSageFeatureTensor3 A :=
  (p.1, p.2.2, p.2.1)

@[simp] theorem operatorSageFeatureTensorSwap_involutive
    (p : OperatorSageFeatureTensor2 A) :
    operatorSageFeatureTensorSwap
      (operatorSageFeatureTensorSwap p) = p := rfl

theorem continuous_operatorSageFeatureTensorSwap :
    Continuous (operatorSageFeatureTensorSwap (A := A)) := by
  change Continuous (fun p : OperatorSageFeatureTensor2 A => (p.2, p.1))
  exact continuous_snd.prodMk continuous_fst

theorem continuous_operatorSageFeatureTensorR12 :
    Continuous (operatorSageFeatureTensorR12 (A := A)) := by
  change Continuous
    (fun p : OperatorSageFeatureTensor3 A => (p.2.1, p.1, p.2.2))
  exact (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

theorem continuous_operatorSageFeatureTensorR23 :
    Continuous (operatorSageFeatureTensorR23 (A := A)) := by
  change Continuous
    (fun p : OperatorSageFeatureTensor3 A => (p.1, p.2.2, p.2.1))
  exact continuous_fst.prodMk
    ((continuous_snd.comp continuous_snd).prodMk
      (continuous_fst.comp continuous_snd))

theorem operatorSageFeatureTensorR12_yang_baxter
    (p : OperatorSageFeatureTensor3 A) :
    operatorSageFeatureTensorR12
      (operatorSageFeatureTensorR23
        (operatorSageFeatureTensorR12 p)) =
      operatorSageFeatureTensorR23
        (operatorSageFeatureTensorR12
          (operatorSageFeatureTensorR23 p)) := rfl

@[simp] theorem operatorSageFeatureTensorR12_quadratic
    (p : OperatorSageFeatureTensor3 A) :
    operatorSageFeatureTensorR12
      (operatorSageFeatureTensorR12 p) = p := rfl

@[simp] theorem operatorSageFeatureTensorR23_quadratic
    (p : OperatorSageFeatureTensor3 A) :
    operatorSageFeatureTensorR23
      (operatorSageFeatureTensorR23 p) = p := rfl

def operatorSageFeaturePairMap :
    ChiralOperatorTensor2 A → OperatorSageFeatureTensor2 A :=
  fun p =>
    (operatorSageObservationMap p.1,
      operatorSageObservationMap p.2)

def operatorSageFeatureTripleMap :
    ChiralOperatorTensor3 A → OperatorSageFeatureTensor3 A :=
  fun p =>
    (operatorSageObservationMap p.1,
      operatorSageObservationMap p.2.1,
      operatorSageObservationMap p.2.2)

theorem operatorSageFeaturePair_swap_intertwines
    (p : ChiralOperatorTensor2 A) :
    operatorSageFeaturePairMap
        (chiralOperatorTensorSwap p) =
      operatorSageFeatureTensorSwap
        (operatorSageFeaturePairMap p) := rfl

theorem operatorSageFeatureTriple_R12_intertwines
    (p : ChiralOperatorTensor3 A) :
    operatorSageFeatureTripleMap
        (chiralOperatorTensorR12 p) =
      operatorSageFeatureTensorR12
        (operatorSageFeatureTripleMap p) := rfl

theorem operatorSageFeatureTriple_R23_intertwines
    (p : ChiralOperatorTensor3 A) :
    operatorSageFeatureTripleMap
        (chiralOperatorTensorR23 p) =
      operatorSageFeatureTensorR23
        (operatorSageFeatureTripleMap p) := rfl

theorem operatorSageFeatureTriple_R12_yang_baxter_transport
    (p : ChiralOperatorTensor3 A) :
    operatorSageFeatureTripleMap
        (chiralOperatorTensorR12
          (chiralOperatorTensorR23
            (chiralOperatorTensorR12 p))) =
      operatorSageFeatureTripleMap
        (chiralOperatorTensorR23
          (chiralOperatorTensorR12
            (chiralOperatorTensorR23 p))) := by
  rw [chiralOperatorTensorR12_yang_baxter]

end
end InfoGeometry.Topology

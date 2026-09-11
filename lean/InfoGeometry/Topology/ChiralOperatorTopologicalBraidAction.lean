import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ChiralOperatorSageLatentChart

/-!
# External topological braid action on the chiral operator carrier

This owner formalizes the associative operator layer only.  The braid
generator is the flip on tensor factors; it is not the nonassociative Zorn
multiplication and it carries no anyonic or cyclotomic interpretation.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

abbrev ChiralOperatorTensor2 (A : Type) :=
  OperatorSageTopologicalCarrier A × OperatorSageTopologicalCarrier A

abbrev ChiralOperatorTensor3 (A : Type) :=
  OperatorSageTopologicalCarrier A ×
    OperatorSageTopologicalCarrier A ×
      OperatorSageTopologicalCarrier A

def chiralOperatorTensorSwap
    (p : ChiralOperatorTensor2 A) : ChiralOperatorTensor2 A :=
  (p.2, p.1)

def chiralOperatorTensorR12
    (p : ChiralOperatorTensor3 A) : ChiralOperatorTensor3 A :=
  (p.2.1, p.1, p.2.2)

def chiralOperatorTensorR23
    (p : ChiralOperatorTensor3 A) : ChiralOperatorTensor3 A :=
  (p.1, p.2.2, p.2.1)

theorem chiralOperatorTensorSwap_involutive
    (p : ChiralOperatorTensor2 A) :
    chiralOperatorTensorSwap (chiralOperatorTensorSwap p) = p := by
  rfl

theorem continuous_chiralOperatorTensorSwap :
    Continuous (chiralOperatorTensorSwap (A := A)) := by
  change Continuous (fun p : ChiralOperatorTensor2 A => (p.2, p.1))
  exact continuous_snd.prodMk continuous_fst

theorem continuous_chiralOperatorTensorR12 :
    Continuous (chiralOperatorTensorR12 (A := A)) := by
  change Continuous
    (fun p : ChiralOperatorTensor3 A => (p.2.1, p.1, p.2.2))
  have h₁ : Continuous (fun p : ChiralOperatorTensor3 A => p.2.1) :=
    continuous_fst.comp continuous_snd
  have h₂ : Continuous (fun p : ChiralOperatorTensor3 A => p.1) :=
    continuous_fst
  have h₃ : Continuous (fun p : ChiralOperatorTensor3 A => p.2.2) :=
    continuous_snd.comp continuous_snd
  exact h₁.prodMk (h₂.prodMk h₃)

theorem continuous_chiralOperatorTensorR23 :
    Continuous (chiralOperatorTensorR23 (A := A)) := by
  change Continuous
    (fun p : ChiralOperatorTensor3 A => (p.1, p.2.2, p.2.1))
  have h₁ : Continuous (fun p : ChiralOperatorTensor3 A => p.1) :=
    continuous_fst
  have h₂ : Continuous (fun p : ChiralOperatorTensor3 A => p.2.2) :=
    continuous_snd.comp continuous_snd
  have h₃ : Continuous (fun p : ChiralOperatorTensor3 A => p.2.1) :=
    continuous_fst.comp continuous_snd
  exact h₁.prodMk (h₂.prodMk h₃)

theorem chiralOperatorTensorR12_yang_baxter
    (p : ChiralOperatorTensor3 A) :
    chiralOperatorTensorR12
        (chiralOperatorTensorR23
          (chiralOperatorTensorR12 p)) =
      chiralOperatorTensorR23
        (chiralOperatorTensorR12
          (chiralOperatorTensorR23 p)) := by
  rfl

theorem chiralOperatorTensorR12_quadratic
    (p : ChiralOperatorTensor3 A) :
    chiralOperatorTensorR12
        (chiralOperatorTensorR12 p) = p := by
  rfl

theorem chiralOperatorTensorR23_quadratic
    (p : ChiralOperatorTensor3 A) :
    chiralOperatorTensorR23
        (chiralOperatorTensorR23 p) = p := by
  rfl

end
end InfoGeometry.Topology

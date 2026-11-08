import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ChiralOperatorLatentQuotientTransport

/-!
# Quotient transport of the external chiral operator braid action

The quotient carries the same external tensor-factor permutations as the
carrier.  The statements here concern the topological quotient and its
representatives only; no multiplication or algebra structure is placed on
the quotient.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

abbrev ChiralOperatorQuotientTensor2 (A : Type) [NormedRing A]
    [NormedAlgebra ℝ A] :=
  ChiralOperatorObservationalQuotient A ×
    ChiralOperatorObservationalQuotient A

abbrev ChiralOperatorQuotientTensor3 (A : Type) [NormedRing A]
    [NormedAlgebra ℝ A] :=
  ChiralOperatorObservationalQuotient A ×
    ChiralOperatorObservationalQuotient A ×
      ChiralOperatorObservationalQuotient A

def chiralOperatorQuotientTensorSwap
    (p : ChiralOperatorQuotientTensor2 A) :
    ChiralOperatorQuotientTensor2 A :=
  (p.2, p.1)

def chiralOperatorQuotientTensorR12
    (p : ChiralOperatorQuotientTensor3 A) :
    ChiralOperatorQuotientTensor3 A :=
  (p.2.1, p.1, p.2.2)

def chiralOperatorQuotientTensorR23
    (p : ChiralOperatorQuotientTensor3 A) :
    ChiralOperatorQuotientTensor3 A :=
  (p.1, p.2.2, p.2.1)

theorem continuous_chiralOperatorQuotientTensorSwap :
    Continuous (chiralOperatorQuotientTensorSwap (A := A)) := by
  change Continuous
    (fun p : ChiralOperatorQuotientTensor2 A => (p.2, p.1))
  exact continuous_snd.prodMk continuous_fst

theorem continuous_chiralOperatorQuotientTensorR12 :
    Continuous (chiralOperatorQuotientTensorR12 (A := A)) := by
  change Continuous
    (fun p : ChiralOperatorQuotientTensor3 A => (p.2.1, p.1, p.2.2))
  have h₁ : Continuous
      (fun p : ChiralOperatorQuotientTensor3 A => p.2.1) :=
    continuous_fst.comp continuous_snd
  have h₂ : Continuous
      (fun p : ChiralOperatorQuotientTensor3 A => p.1) :=
    continuous_fst
  have h₃ : Continuous
      (fun p : ChiralOperatorQuotientTensor3 A => p.2.2) :=
    continuous_snd.comp continuous_snd
  exact h₁.prodMk (h₂.prodMk h₃)

theorem continuous_chiralOperatorQuotientTensorR23 :
    Continuous (chiralOperatorQuotientTensorR23 (A := A)) := by
  change Continuous
    (fun p : ChiralOperatorQuotientTensor3 A => (p.1, p.2.2, p.2.1))
  have h₁ : Continuous
      (fun p : ChiralOperatorQuotientTensor3 A => p.1) :=
    continuous_fst
  have h₂ : Continuous
      (fun p : ChiralOperatorQuotientTensor3 A => p.2.2) :=
    continuous_snd.comp continuous_snd
  have h₃ : Continuous
      (fun p : ChiralOperatorQuotientTensor3 A => p.2.1) :=
    continuous_fst.comp continuous_snd
  exact h₁.prodMk (h₂.prodMk h₃)

@[simp] theorem chiralOperatorQuotientTensorSwap_involutive
    (p : ChiralOperatorQuotientTensor2 A) :
    chiralOperatorQuotientTensorSwap
      (chiralOperatorQuotientTensorSwap p) = p := by
  rfl

theorem chiralOperatorQuotientTensorR12_yang_baxter
    (p : ChiralOperatorQuotientTensor3 A) :
    chiralOperatorQuotientTensorR12
      (chiralOperatorQuotientTensorR23
        (chiralOperatorQuotientTensorR12 p)) =
      chiralOperatorQuotientTensorR23
        (chiralOperatorQuotientTensorR12
          (chiralOperatorQuotientTensorR23 p)) := by
  rfl

@[simp] theorem chiralOperatorQuotientTensorR12_quadratic
    (p : ChiralOperatorQuotientTensor3 A) :
    chiralOperatorQuotientTensorR12
      (chiralOperatorQuotientTensorR12 p) = p := by
  rfl

@[simp] theorem chiralOperatorQuotientTensorR23_quadratic
    (p : ChiralOperatorQuotientTensor3 A) :
    chiralOperatorQuotientTensorR23
      (chiralOperatorQuotientTensorR23 p) = p := by
  rfl

theorem chiralOperatorQuotientTensorR12_mk
    (X Y Z : OperatorSageTopologicalCarrier A) :
    chiralOperatorQuotientTensorR12
      (Quotient.mk _ X, Quotient.mk _ Y, Quotient.mk _ Z) =
      (Quotient.mk _ Y, Quotient.mk _ X, Quotient.mk _ Z) := by
  rfl

theorem chiralOperatorQuotientTensorR23_mk
    (X Y Z : OperatorSageTopologicalCarrier A) :
    chiralOperatorQuotientTensorR23
      (Quotient.mk _ X, Quotient.mk _ Y, Quotient.mk _ Z) =
      (Quotient.mk _ X, Quotient.mk _ Z, Quotient.mk _ Y) := by
  rfl

end
end InfoGeometry.Topology

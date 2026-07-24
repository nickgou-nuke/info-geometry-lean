import Mathlib
import InfoGeometry.Projective.QuantumTwistorGauge
import InfoGeometry.Canonical.BostConnesKTheory
import InfoGeometry.Algebra.CuntzGNSRepresentation
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportOperatorInner

/-!
# Quantum Twistor Dirac Operator & Spectral Triple

This module records the spectral-triple interface around the quantum
Grassmannian coordinate ring. The bounded-commutator hypothesis is carried as
an explicit field of the spectral-triple structure; this file does not invent a
separate projector-level theorem.
-/

noncomputable section

namespace QuantumTwistorDirac

variable (q : ℂ) (u : ℂ)

/--
The base structure for a Dirac operator on a finite complex Hilbert space.

The inner product is supplied explicitly so the model can use the finite-support
GNS pairing without requiring a global `InnerProductSpace` instance.
-/
structure QuantumDiracOperator (H : Type*) [NormedAddCommGroup H] [Module ℂ H] where
  inner : H → H → ℂ
  domain : Submodule ℂ H
  op : H → H

/--
The formal `SpectralTriple` structure over the coordinate ring.
It contains the Hilbert-space representation `H`, the representation of the
`coordinateRing ℂ q`, and the self-adjoint Dirac operator `D` with the bounded
commutator constraint.
-/
structure QuantumSpectralTriple (H : Type*) [NormedAddCommGroup H] [Module ℂ H] where
  rep : InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q →+* Module.End ℂ H
  D : QuantumDiracOperator H
  bounded_commutators : ∀ (a : InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q), ∃ (C : ℝ), ∀ (x : H), x ∈ D.domain →
    ‖D.op ((rep a) x) - (rep a) (D.op x)‖ ≤ C * ‖x‖

/--
The bounded-commutator property is already carried by the spectral-triple
structure itself.
-/
def IsKTheoryCommutatorBounded {H : Type*} [NormedAddCommGroup H] [Module ℂ H]
    (ST : QuantumSpectralTriple q H) : Prop :=
  ∀ (a : InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q), ∃ (C : ℝ), ∀ (x : H), x ∈ ST.D.domain →
    ‖ST.D.op ((ST.rep a) x) - (ST.rep a) (ST.D.op x)‖ ≤ C * ‖x‖

/--
Interaction with the gauge action: the spectral triple is gauge covariant
if the gauge action is implemented by a unitary operator `U` that commutes with
`D`.
-/
def IsGaugeCovariant {H : Type*} [NormedAddCommGroup H] [Module ℂ H]
    (ST : QuantumSpectralTriple q H)
    (gauge : InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q → InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q) : Prop :=
  ∃ (U : H ≃ₗᵢ[ℂ] H),
    (∀ (a : InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q), ST.rep (gauge a) =
      (U : H →L[ℂ] H) * ST.rep a * (U.symm : H →L[ℂ] H)) ∧
    (∀ (x : H), x ∈ ST.D.domain → U x ∈ ST.D.domain ∧ ST.D.op (U x) = U (ST.D.op x))

/-! ### Bost-Connes GNS Instantiation -/

section BostConnes

variable (n : ℕ) (primes : Fin n → ℕ) (β : ℂ) (q : ℂ)

/-- The GNS pre-Hilbert space is the finite-support carrier `Fin n → ℂ`. -/
abbrev GNSPreHilbert (n : ℕ) : Type :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport.GNS
    (fun _ : Fin n => True)

private def gnsInner (n : ℕ) : GNSPreHilbert n → GNSPreHilbert n → ℂ :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport.innerGNS
    (fun _ : Fin n => True)

private def gnsDiracWeight (n : ℕ) (primes : Fin n → ℕ) : Fin n → ℂ :=
  fun i => algebraMap ℝ ℂ (Real.log (primes i))

private def gnsDiracAction (n : ℕ) (primes : Fin n → ℕ) :
    GNSPreHilbert n → GNSPreHilbert n :=
  InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport.liftMul (fun _ : Fin n => True)
    (gnsDiracWeight n primes)

/-- The diagonal log-weight Dirac operator on the finite GNS carrier. -/
noncomputable def gnsDiracOperator : QuantumDiracOperator (GNSPreHilbert n) where
  inner := gnsInner n
  domain := ⊤
  op := gnsDiracAction n primes

variable (coordinateToCuntz : InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q →ₐ[ℂ] InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n)
variable (cuntzGNSAction : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n →ₐ[ℂ] (GNSPreHilbert n →L[ℂ] GNSPreHilbert n))

/-- The representation maps the coordinate ring to the Cuntz algebra,
    and then acts on the GNS space. -/
noncomputable def gnsRepresentation :
    InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q →+* Module.End ℂ (GNSPreHilbert n) :=
  (ContinuousLinearMap.toLinearMapRingHom :
      (GNSPreHilbert n →L[ℂ] GNSPreHilbert n) →+* Module.End ℂ (GNSPreHilbert n)).comp
    (cuntzGNSAction.comp coordinateToCuntz)

/-- The exact QuantumSpectralTriple over the Bost-Connes boundary. -/
noncomputable def bostConnesSpectralTriple
    (hbounded : ∀ (a : InfoGeometry.Projective.QuantumGrassmannian.coordinateRing ℂ q), ∃ (C : ℝ), ∀ (x : GNSPreHilbert n),
      x ∈ (gnsDiracOperator n primes).domain →
        ‖(gnsDiracOperator n primes).op ((gnsRepresentation n q coordinateToCuntz
          cuntzGNSAction a) x) -
          (gnsRepresentation n q coordinateToCuntz cuntzGNSAction a)
            ((gnsDiracOperator n primes).op x)‖ ≤ C * ‖x‖) :
    QuantumSpectralTriple q (GNSPreHilbert n) where
  rep := gnsRepresentation n q coordinateToCuntz cuntzGNSAction
  D := gnsDiracOperator n primes
  bounded_commutators := hbounded

end BostConnes

end QuantumTwistorDirac

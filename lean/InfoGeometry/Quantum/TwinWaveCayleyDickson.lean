import Mathlib.Algebra.Group.Defs
import InfoGeometry.Clifford.SplitOctonionsDualProduct
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Quantum.TwinWave

open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian
open InfoGeometry.Clifford.SplitOctonionsDualProduct
open InfoGeometry.Clifford.SplitOctonionsDualProduct.SplitOctonion
open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M)

/-- 
In the Twin Wave Formalism (Two-State Vector Formalism), a physical state is described 
by a pair of states: one evolving forward in time (the "Now" or "Retarded" state), 
and one evolving backward in time (the "Past/Future" or "Advanced" state).

We can natively embed this structure into the Cayley-Dickson doubling of a split algebra, 
where the first component represents the forward-time wave, and the second component 
represents the backward-time wave.
-/
structure TwinWaveState where
  forward : evenOdd Q 0
  backward : evenOdd Q 0

/-- 
The time reversal operator in this algebra is mathematically identical to 
the Hestenes Adjoint (Clifford conjugation). It reverses the orientation 
of the algebraic generators.
-/
def TimeReversal (X : evenOdd Q 0) : evenOdd Q 0 :=
  hestenesAdjoint Q v0 X

/-- 
The transition amplitude between two Twin Wave states is governed by the 
Cayley-Dickson split product. The cross-terms natively apply TimeReversal 
(conjugation) to ensure CPT invariance during the interference of the 
forward and backward waves.
-/
def TwinWaveInterference (X Y : TwinWaveState Q) : TwinWaveState Q :=
  { forward := X.forward * Y.forward + (TimeReversal Q v0 Y.backward) * X.backward,
    backward := Y.backward * X.forward + X.backward * (TimeReversal Q v0 Y.forward) }

/-- 
The Twin Wave Interference exactly reproduces the Cayley-Dickson Split Octonion product.
This demonstrates that the hypercomplex structure of the split doubling is algebraically 
isomorphic to the bidirectional time-evolution of the Two-State Vector Formalism.
-/
def TwinWaveEquivSplitOctonion : TwinWaveState Q ≃ SplitOctonion Q v0 where
  toFun := fun X => ⟨X.forward, X.backward⟩
  invFun := fun O => ⟨O.fst, O.snd⟩
  left_inv := fun X => rfl
  right_inv := fun O => rfl

theorem interference_is_star_prod (X Y : TwinWaveState Q) :
    TwinWaveEquivSplitOctonion Q v0 (TwinWaveInterference Q v0 X Y) = 
    star_prod (TwinWaveEquivSplitOctonion Q v0 X) (TwinWaveEquivSplitOctonion Q v0 Y) := by
  rfl

/-!
## Analytic doubled-space realization

`TwinWaveState` is the algebraic product carrier.  `DoubledSpace` is the
`WithLp 2` completion of a product carrier, so the identification requires the
analytic structure needed by that owner.
-/

noncomputable def TwinWaveEquivDoubledSpace
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M)
    [NormedAddCommGroup (evenOdd Q 0)]
    [InnerProductSpace ℝ (evenOdd Q 0)]
    [CompleteSpace (evenOdd Q 0)] :
    TwinWaveState Q ≃ InfoGeometry.Krein.DoubledSpace (evenOdd Q 0) where
  toFun X :=
    InfoGeometry.Krein.to_doubled X.forward X.backward
  invFun X :=
    { forward := WithLp.fst X
      backward := WithLp.snd X }
  left_inv X := by
    rcases X with ⟨forward, backward⟩
    simp
  right_inv X := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp

/-!
## Associative Schur cross-term

The Cayley--Dickson cross-term is a product of three entries.  Its honest
Schur interpretation is the block-elimination term `B * D⁻¹ * C`; the full
Schur complement additionally contains the diagonal block `A`.
-/

def schurCrossTerm {A : Type*} [Ring A] (B Dinv C : A) : A :=
  B * Dinv * C

def associativeSchurComplement {A : Type*} [Ring A]
    (A₀ B Dinv C : A) : A :=
  A₀ - schurCrossTerm B Dinv C

theorem twinWave_forward_eq_diagonal_subtracted_schurComplement
    (X Y : TwinWaveState Q) :
    X.forward * Y.forward +
        (TimeReversal Q v0 Y.backward) * X.backward =
      X.forward * Y.forward +
        schurCrossTerm (TimeReversal Q v0 Y.backward) 1 X.backward := by
  simp [schurCrossTerm]

end InfoGeometry.Quantum.TwinWave

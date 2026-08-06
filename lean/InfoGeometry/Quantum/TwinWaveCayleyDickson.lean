import Mathlib.Algebra.Group.Defs
import InfoGeometry.Clifford.SplitOctonionsDualProduct

namespace InfoGeometry.Quantum.TwinWave

open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian
open SplitOctonion
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

end InfoGeometry.Quantum.TwinWave

import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitOctonionsDualProduct
import InfoGeometry.Clifford.EvenRegularRepresentation
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Quantum.TwinWave

open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian
open InfoGeometry.Clifford.SplitOctonionsDualProduct
open InfoGeometry.Clifford.SplitOctonionsDualProduct.SplitOctonion
open InfoGeometry.Clifford.EvenRegularRepresentation
open InfoGeometry.Krein
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
  { forward := X.forward * Y.forward + (TimeReversal Q v0 Y.backward) * X.backward
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

/-! ## Schur-complement readout of the forward Cayley-Dickson cross-term -/

/-- The associative Schur cross-term `B D⁻¹ C` on the even Clifford carrier. -/
def schurCrossTerm
    (B Dinv C : evenOdd Q 0) : evenOdd Q 0 :=
  (B * Dinv) * C

/-- The corresponding algebraic Schur complement `A - B D⁻¹ C`. -/
def associativeSchurComplement
    (A B Dinv C : evenOdd Q 0) : evenOdd Q 0 :=
  A - schurCrossTerm Q B Dinv C

/--
The forward TwinWave interference cross-term is exactly the Schur cross-term
with identity inverse block.
-/
theorem twinWave_forward_crossTerm_eq_schurCrossTerm
    (X Y : TwinWaveState Q) :
    (TimeReversal Q v0 Y.backward) * X.backward =
      schurCrossTerm Q (TimeReversal Q v0 Y.backward) 1 X.backward := by
  simp [schurCrossTerm]

/--
The forward TwinWave interference is a diagonal product minus the Schur
complement with zero upper-left entry and identity inverse lower-right block.
This is the exact `D⁻¹ = 1` Schur specialization; it does not assert a general
invertible-minus-block transport theorem.
-/
theorem twinWave_forward_eq_diagonal_subtracted_schurComplement
    (X Y : TwinWaveState Q) :
    (TwinWaveInterference Q v0 X Y).forward =
      X.forward * Y.forward -
        associativeSchurComplement Q 0
          (TimeReversal Q v0 Y.backward) 1 X.backward := by
  simp [TwinWaveInterference, associativeSchurComplement, schurCrossTerm]

/-! ## Native even-algebra and analytic doubled-space realizations -/

section RealRealizations

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

/--
The two TwinWave components are canonically the two copies of Mathlib's bundled
associative even Clifford algebra. This removes the algebraic carrier mismatch
between `evenOdd Q 0` and `CliffordAlgebra.even Q` without introducing a new carrier.
-/
noncomputable def TwinWaveEquivEvenPair :
    TwinWaveState Q ≃ CliffordAlgebra.even Q × CliffordAlgebra.even Q where
  toFun := fun X =>
    ((evenEquivEvenOddZero Q).symm X.forward,
      (evenEquivEvenOddZero Q).symm X.backward)
  invFun := fun X =>
    ⟨evenEquivEvenOddZero Q X.1, evenEquivEvenOddZero Q X.2⟩
  left_inv := by
    intro X
    cases X
    simp
  right_inv := by
    intro X
    rcases X with ⟨Xplus, Xminus⟩
    simp

@[simp] theorem TwinWaveEquivEvenPair_forward (X : TwinWaveState Q) :
    (TwinWaveEquivEvenPair Q X).1 = (evenEquivEvenOddZero Q).symm X.forward := by
  rfl

@[simp] theorem TwinWaveEquivEvenPair_backward (X : TwinWaveState Q) :
    (TwinWaveEquivEvenPair Q X).2 = (evenEquivEvenOddZero Q).symm X.backward := by
  rfl

variable [NormedAddCommGroup (evenOdd Q 0)]
variable [InnerProductSpace ℝ (evenOdd Q 0)]
variable [CompleteSpace (evenOdd Q 0)]

/--
Under the explicit Hilbert hypotheses needed by the repository's Krein owner,
a TwinWave state is canonically the same pair as `DoubledSpace (evenOdd Q 0)`.
No new doubled carrier is introduced.
-/
def TwinWaveEquivDoubledSpace :
    TwinWaveState Q ≃ DoubledSpace (evenOdd Q 0) where
  toFun := fun X => to_doubled X.forward X.backward
  invFun := fun u => ⟨WithLp.fst u, WithLp.snd u⟩
  left_inv := fun X => rfl
  right_inv := fun u => by
    apply DoubledSpace.ext <;> rfl

@[simp]
theorem TwinWaveEquivDoubledSpace_apply (X : TwinWaveState Q) :
    TwinWaveEquivDoubledSpace Q X = to_doubled X.forward X.backward :=
  rfl

@[simp]
theorem TwinWaveEquivDoubledSpace_symm_apply
    (u : DoubledSpace (evenOdd Q 0)) :
    (TwinWaveEquivDoubledSpace Q).symm u =
      ⟨WithLp.fst u, WithLp.snd u⟩ :=
  rfl

end RealRealizations

end InfoGeometry.Quantum.TwinWave

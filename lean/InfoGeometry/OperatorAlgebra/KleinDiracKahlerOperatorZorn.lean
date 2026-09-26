import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Exact square calculus for the associative two-sheet block.  The name is
historical; the statements below are ordinary ring identities and make no
topological or physical claim about a Klein bottle or a Dirac operator. -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn

open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

variable {A : Type*} [Ring A] [StarRing A]

abbrev ZornBlock (A : Type*) [Ring A] [StarRing A] :=
  InfoGeometry.Physics.OperatorZornMatrix A

def twinBoundaryDiracBlock
    (wp wm dp dm : A) : ZornBlock A := ⟨wp, wm, dp, dm⟩

def pureDiracBlock (dp dm : A) : ZornBlock A :=
  twinBoundaryDiracBlock 0 0 dp dm

theorem twinBoundaryDiracBlock_sq
    (wp wm dp dm : A) :
    twinBoundaryDiracBlock wp wm dp dm *
        twinBoundaryDiracBlock wp wm dp dm =
      ⟨wp * wp + dp * dm,
        dm * dp + wm * wm,
        wp * dp + dp * wm,
        dm * wp + wm * dm⟩ := by
  apply zornBlock_ext <;>
    simp [twinBoundaryDiracBlock]

theorem pureDiracBlock_sq
    (dp dm : A) :
    pureDiracBlock dp dm * pureDiracBlock dp dm =
      ⟨dp * dm, dm * dp, 0, 0⟩ := by
  simpa [pureDiracBlock] using twinBoundaryDiracBlock_sq 0 0 dp dm

/-- An odd two-channel block is odd for the sheet Cartan involution. -/
theorem pureDiracBlock_isOdd (dp dm : A) :
    IsOdd (pureDiracBlock dp dm) := by
  unfold IsOdd
  rw [cartanInvolution_coordinates]
  apply zornBlock_ext <;> simp [pureDiracBlock, twinBoundaryDiracBlock]

/-- The square of an odd two-channel block is even. -/
theorem pureDiracBlock_sq_isEven (dp dm : A) :
    IsEven (pureDiracBlock dp dm * pureDiracBlock dp dm) := by
  unfold IsEven
  rw [pureDiracBlock_sq, cartanInvolution_coordinates]
  rfl

/-- If both off-diagonal coupling defects vanish, the square of a
twin-boundary block is diagonal. -/
theorem twinBoundaryDiracBlock_sq_diagonal
    (wp wm dp dm : A)
    (hPlus : wp * dp + dp * wm = 0)
    (hMinus : dm * wp + wm * dm = 0) :
    twinBoundaryDiracBlock wp wm dp dm * twinBoundaryDiracBlock wp wm dp dm =
      (⟨wp * wp + dp * dm, dm * dp + wm * wm, 0, 0⟩ : ZornBlock A) := by
  rw [twinBoundaryDiracBlock_sq, hPlus, hMinus]

/-! ## Ring-level Dirac--Kähler square

The result below is an identity in an associative ring.  Its hypotheses are
nilpotency laws for two elements; it does not construct a differential
operator or make an analytic claim.
-/

/-- Algebraic data for the square calculation `D = d - δ`. -/
structure RingDiracKahler (A : Type*) [Ring A] where
  d : A
  delta : A
  d_sq_zero : d * d = 0
  delta_sq_zero : delta * delta = 0

namespace RingDiracKahler

variable (K : RingDiracKahler A)

/-- The difference operator with the convention `D = d - δ`. -/
def dirac : A := K.d - K.delta

/-- The anticommutator `dδ + δd`. -/
def laplacian : A := K.d * K.delta + K.delta * K.d

/-- In any associative ring, nilpotence of `d` and `δ` gives
`(d - δ)² = -(dδ + δd)`. -/
theorem dirac_sq_eq_neg_laplacian :
    K.dirac * K.dirac = -K.laplacian := by
  unfold dirac laplacian
  noncomm_ring [K.d_sq_zero, K.delta_sq_zero]

/-- Place the same algebraic operator in both off-diagonal channels. -/
def zornBlock : ZornBlock A :=
  pureDiracBlock K.dirac K.dirac

/-- Its square has the anticommutator Laplacian in each diagonal channel. -/
theorem zornBlock_sq :
    K.zornBlock * K.zornBlock =
      (⟨-K.laplacian, -K.laplacian, 0, 0⟩ : ZornBlock A) := by
  calc
    K.zornBlock * K.zornBlock =
        (⟨K.dirac * K.dirac, K.dirac * K.dirac, 0, 0⟩ : ZornBlock A) := by
          exact pureDiracBlock_sq K.dirac K.dirac
    _ = (⟨-K.laplacian, -K.laplacian, 0, 0⟩ : ZornBlock A) := by
      rw [K.dirac_sq_eq_neg_laplacian]

end RingDiracKahler

end InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn

end

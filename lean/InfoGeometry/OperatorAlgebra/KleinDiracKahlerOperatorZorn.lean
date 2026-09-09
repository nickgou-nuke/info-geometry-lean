import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

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

end InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn

end

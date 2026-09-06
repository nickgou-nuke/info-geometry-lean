import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Topology.KleinDeckNormalForm
import InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge

/-!
# Klein and Dirac--Kahler calculus in the associative operator-Zorn shell

The diagonal entries are two independent boundary operators.  The upper and
lower off-diagonal entries are the two chiral maps.  The exact square of the
block records both the diagonal Laplacians and the off-diagonal coupling
defects.

The Klein generator is represented by sheet exchange.  A diagonal unit pair
`diag(u,u^{-1})` is conjugated to its inverse, giving the literal relation
`b a b^{-1} = a^{-1}`.  This finite representation theorem is distinct from a
topological quotient or a claim that the Dirac--Kahler operator itself creates
a Klein bottle.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

variable {A : Type*} [Ring A] [StarRing A]

/-- General two-boundary, two-chiral-channel block. -/
def twinBoundaryDiracBlock
    (WPlus WMinus DPlus DMinus : A) : ZornBlock A :=
  ⟨WPlus, WMinus, DPlus, DMinus⟩

/-- Pure odd Dirac block. -/
def pureDiracBlock (DPlus DMinus : A) : ZornBlock A :=
  twinBoundaryDiracBlock 0 0 DPlus DMinus

/-- Exact square of the fully noncommutative twin-boundary block. -/
theorem twinBoundaryDiracBlock_sq
    (WPlus WMinus DPlus DMinus : A) :
    twinBoundaryDiracBlock WPlus WMinus DPlus DMinus *
        twinBoundaryDiracBlock WPlus WMinus DPlus DMinus =
      (⟨WPlus * WPlus + DPlus * DMinus,
        DMinus * DPlus + WMinus * WMinus,
        WPlus * DPlus + DPlus * WMinus,
        DMinus * WPlus + WMinus * DMinus⟩ : ZornBlock A) := by
  apply zornBlock_ext <;>
    simp [twinBoundaryDiracBlock]

/-- An odd block squares into the two diagonal chiral Laplacians. -/
theorem pureDiracBlock_sq (DPlus DMinus : A) :
    pureDiracBlock DPlus DMinus * pureDiracBlock DPlus DMinus =
      (⟨DPlus * DMinus, DMinus * DPlus, 0, 0⟩ : ZornBlock A) := by
  simpa [pureDiracBlock] using
    twinBoundaryDiracBlock_sq
      (0 : A) 0 DPlus DMinus

/-- The pure Dirac block is odd for the sheet Cartan involution. -/
theorem pureDiracBlock_isOdd (DPlus DMinus : A) :
    IsOdd (pureDiracBlock DPlus DMinus) := by
  unfold IsOdd
  rw [cartanInvolution_coordinates]
  apply zornBlock_ext <;> simp [pureDiracBlock, twinBoundaryDiracBlock]

/-- Its square is even. -/
theorem pureDiracBlock_sq_isEven (DPlus DMinus : A) :
    IsEven (pureDiracBlock DPlus DMinus *
      pureDiracBlock DPlus DMinus) := by
  unfold IsEven
  rw [pureDiracBlock_sq, cartanInvolution_coordinates]
  rfl

/-- Direct equality form of the evenness theorem. -/
theorem pureDiracBlock_sq_commutes_grading (DPlus DMinus : A) :
    cartanInvolution
        (pureDiracBlock DPlus DMinus * pureDiracBlock DPlus DMinus) =
      pureDiracBlock DPlus DMinus * pureDiracBlock DPlus DMinus := by
  exact pureDiracBlock_sq_isEven DPlus DMinus

/-- Exact decoupling criterion: the two off-diagonal defects must vanish. -/
theorem twinBoundaryDiracBlock_sq_diagonal
    (WPlus WMinus DPlus DMinus : A)
    (hPlus : WPlus * DPlus + DPlus * WMinus = 0)
    (hMinus : DMinus * WPlus + WMinus * DMinus = 0) :
    twinBoundaryDiracBlock WPlus WMinus DPlus DMinus *
        twinBoundaryDiracBlock WPlus WMinus DPlus DMinus =
      (⟨WPlus * WPlus + DPlus * DMinus,
        DMinus * DPlus + WMinus * WMinus,
        0, 0⟩ : ZornBlock A) := by
  rw [twinBoundaryDiracBlock_sq, hPlus, hMinus]

/-- Ring-level Dirac--Kahler datum.  The two nilpotency laws are the exact
input used to square `d-delta`. -/
structure RingDiracKahler (A : Type*) [Ring A] where
  d : A
  delta : A
  d_sq_zero : d * d = 0
  delta_sq_zero : delta * delta = 0

namespace RingDiracKahler

variable (K : RingDiracKahler A)

/-- Dirac--Kahler operator with the sign convention `D=d-delta`. -/
def dirac : A :=
  K.d - K.delta

/-- Hodge--de Rham Laplacian in the associative coefficient ring. -/
def laplacian : A :=
  K.d * K.delta + K.delta * K.d

/-- Exact ring identity `D^2 = -Delta`. -/
theorem dirac_sq_eq_neg_laplacian :
    K.dirac * K.dirac = -K.laplacian := by
  unfold dirac laplacian
  noncomm_ring [K.d_sq_zero, K.delta_sq_zero]

/-- Dirac--Kahler operator placed in both chiral directions. -/
def zornBlock : ZornBlock A :=
  pureDiracBlock K.dirac K.dirac

/-- The Zorn block square is the diagonal doubled Laplacian. -/
theorem zornBlock_sq :
    K.zornBlock * K.zornBlock =
      (⟨-K.laplacian, -K.laplacian, 0, 0⟩ : ZornBlock A) := by
  calc
    K.zornBlock * K.zornBlock =
        (⟨K.dirac * K.dirac, K.dirac * K.dirac, 0, 0⟩ :
          ZornBlock A) := by
            exact pureDiracBlock_sq K.dirac K.dirac
    _ = (⟨-K.laplacian, -K.laplacian, 0, 0⟩ : ZornBlock A) := by
      rw [K.dirac_sq_eq_neg_laplacian]

/-- Add two independent boundary waves to the Dirac--Kahler channels. -/
def withBoundaryWaves (WPlus WMinus : A) : ZornBlock A :=
  twinBoundaryDiracBlock WPlus WMinus K.dirac K.dirac

/-- Boundary-wave square with the exact noncommutative coupling defects shown
explicitly. -/
theorem withBoundaryWaves_sq (WPlus WMinus : A) :
    K.withBoundaryWaves WPlus WMinus *
        K.withBoundaryWaves WPlus WMinus =
      (⟨WPlus * WPlus - K.laplacian,
        -K.laplacian + WMinus * WMinus,
        WPlus * K.dirac + K.dirac * WMinus,
        K.dirac * WPlus + WMinus * K.dirac⟩ : ZornBlock A) := by
  calc
    K.withBoundaryWaves WPlus WMinus *
        K.withBoundaryWaves WPlus WMinus =
      (⟨WPlus * WPlus + K.dirac * K.dirac,
        K.dirac * K.dirac + WMinus * WMinus,
        WPlus * K.dirac + K.dirac * WMinus,
        K.dirac * WPlus + WMinus * K.dirac⟩ : ZornBlock A) := by
          exact twinBoundaryDiracBlock_sq WPlus WMinus K.dirac K.dirac
    _ = (⟨WPlus * WPlus - K.laplacian,
        -K.laplacian + WMinus * WMinus,
        WPlus * K.dirac + K.dirac * WMinus,
        K.dirac * WPlus + WMinus * K.dirac⟩ : ZornBlock A) := by
      rw [K.dirac_sq_eq_neg_laplacian]
      simp [sub_eq_add_neg]

end RingDiracKahler

/-- Diagonal unit representation of the orientable translation generator. -/
def phaseTranslation (u : Units A) : ZornBlock A :=
  ⟨(u : A), ((u⁻¹ : Units A) : A), 0, 0⟩

/-- The sheet exchange represents the orientation-reversing generator. -/
def kleinGlide : ZornBlock A :=
  sheetExchange

@[simp] theorem kleinGlide_sq :
    kleinGlide (A := A) * kleinGlide = 1 := by
  exact sheetExchange_sq

/-- Exact matrix representation of the Klein relation:
`G T(u) G^{-1} = T(u^{-1})`. -/
theorem kleinGlide_conjugates_phaseTranslation
    (u : Units A) :
    kleinGlide * phaseTranslation u * kleinGlide =
      phaseTranslation u⁻¹ := by
  rw [kleinGlide, sheetExchange_conjugates]
  apply zornBlock_ext <;> simp [phaseTranslation]

/-- Sheet exchange swaps the two diagonal waves and the two chiral maps. -/
theorem kleinGlide_conjugates_twinBoundaryDiracBlock
    (WPlus WMinus DPlus DMinus : A) :
    kleinGlide * twinBoundaryDiracBlock WPlus WMinus DPlus DMinus *
        kleinGlide =
      twinBoundaryDiracBlock WMinus WPlus DMinus DPlus := by
  rw [kleinGlide, sheetExchange_conjugates]
  rfl

/-- The algebraic Klein generator used here agrees with the abstract deck
presentation at the level of the defining conjugation relation. -/
theorem klein_relation_shape :
    InfoGeometry.Topology.KleinDeckNormalForm.b *
        InfoGeometry.Topology.KleinDeckNormalForm.a *
        InfoGeometry.Topology.KleinDeckNormalForm.b⁻¹ =
      InfoGeometry.Topology.KleinDeckNormalForm.a⁻¹ :=
  InfoGeometry.Topology.KleinDeckNormalForm.klein_conjugation_relation

end InfoGeometry.OperatorAlgebra.KleinDiracKahlerOperatorZorn

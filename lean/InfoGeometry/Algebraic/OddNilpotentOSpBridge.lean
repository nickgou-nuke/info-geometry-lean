import Mathlib

/-!
# Odd nilpotent and `osp(1|2)` gate socket

witness-gated (Native Closure Mandated: Closure Debt) super Jacobson--Morozov eligibility surface:

`odd nilpotent -> super Jordan normal form -> osp(1|2) embedding gate`.

This file is a structural bridge/socket. It does not claim a full constructive
formalization of Lie-superalgebra normal-form machinery, a CAR inductive-limit
construction, a Cantor homeomorphism, or an AQFT representation theorem.
-/

noncomputable section

namespace InfoGeometry.Algebraic.OddNilpotentOSpBridge

/-! ## 1. Finite parity vocabulary -/

/-- Two parity sectors of a finite superspace. -/
inductive SuperParity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace SuperParity

/-- Flip even and odd parity. -/
def flip : SuperParity → SuperParity
  | even => odd
  | odd => even

@[simp]
theorem flip_even : flip even = odd := rfl

@[simp]
theorem flip_odd : flip odd = even := rfl

@[simp]
theorem flip_flip (p : SuperParity) : flip (flip p) = p := by
  cases p <;> rfl

end SuperParity

/-- Abstract vector superspace dimensions. -/
structure SuperDimension where
  /-- Even dimension. -/
  evenDim : ℕ
  /-- Odd dimension. -/
  oddDim : ℕ

/-- Super Jordan block descriptor. -/
structure SuperJordanBlock where
  /-- Length of the alternating-parity Jordan chain. -/
  size : ℕ
  /-- Positivity witness. -/
  size_pos : 0 < size

/-- A super Jordan block is admissible for `osp(1|2)` iff its size is odd. -/
def SuperJordanBlock.AdmissibleOdd (B : SuperJordanBlock) : Prop :=
  B.size % 2 = 1

namespace SuperJordanBlock

/--
Parity at a position in an alternating super Jordan block.

This is only the finite parity bookkeeping.  It does not construct a Jordan
normal form or a matrix representation.
-/
def parityAt (B : SuperJordanBlock) (start : SuperParity) (k : Fin B.size) :
    SuperParity :=
  if k.1 % 2 = 0 then start else start.flip

@[simp]
theorem parityAt_zero
    (B : SuperJordanBlock)
    (start : SuperParity)
    (hB : 0 < B.size) :
    B.parityAt start ⟨0, hB⟩ = start := by
  simp [parityAt]

@[simp]
theorem parityAt_zero_even
    (B : SuperJordanBlock)
    (hB : 0 < B.size) :
    B.parityAt SuperParity.even ⟨0, hB⟩ = SuperParity.even := by
  simp

/--
Admissibility is exactly the stored odd-size condition.

This readback keeps the paper's odd-block criterion as a finite arithmetic
predicate, without deriving an `osp(1|2)` embedding by itself.
-/
theorem admissibleOdd_iff
    (B : SuperJordanBlock) :
    B.AdmissibleOdd ↔ B.size % 2 = 1 :=
  Iff.rfl

end SuperJordanBlock

/-! ## 2. Odd nilpotent square packets -/

/--
An odd nilpotent-style square packet.

For an odd element `e`, papers on `gl(m|n)` often track its square `e * e`,
which is even and may itself be nilpotent.  The parity and nilpotence laws are
kept as explicit supplied laws here.
-/
structure OddNilpotentSquarePacket
    (Op : Type*) [Mul Op] where
  /-- Odd operator/element. -/
  e : Op
  /-- Its even square readout. -/
  square : Op
  /-- Definitional square law. -/
  square_eq : e * e = square
  /-- Supplied oddness law for `e`. -/
  oddLaw : Prop
  /-- Certificate of oddness. -/
  oddCertificate : oddLaw
  /-- Supplied evenness law for `e * e`. -/
  squareEvenLaw : Prop
  /-- Certificate of evenness for the square. -/
  squareEvenCertificate : squareEvenLaw
  /-- Supplied nilpotence law. -/
  nilpotentLaw : Prop
  /-- Certificate of nilpotence. -/
  nilpotentCertificate : nilpotentLaw

namespace OddNilpotentSquarePacket

variable {Op : Type*} [Mul Op]

/-- The square readout of the odd element. -/
theorem square_readout
    (P : OddNilpotentSquarePacket Op) :
    P.e * P.e = P.square :=
  P.square_eq

/-- Re-export of the supplied oddness law. -/
theorem odd_valid
    (P : OddNilpotentSquarePacket Op) :
    P.oddLaw :=
  P.oddCertificate

/-- Re-export of the supplied evenness law for the square. -/
theorem square_even_valid
    (P : OddNilpotentSquarePacket Op) :
    P.squareEvenLaw :=
  P.squareEvenCertificate

/-- Re-export of the supplied nilpotence law. -/
theorem nilpotent_valid
    (P : OddNilpotentSquarePacket Op) :
    P.nilpotentLaw :=
  P.nilpotentCertificate

end OddNilpotentSquarePacket

/-! ## 3. Super Jordan normal-form gate -/

/--
Super Jordan normal-form package for an odd nilpotent element.

`lies_in_even_orbit_of_blocks` abstracts the statement that `e` lies in the
even-group orbit of a super Jordan matrix with these blocks.
-/
structure SuperJordanNormalForm (Element : Type*) where
  e : Element
  blocks : List SuperJordanBlock
  lies_in_even_orbit_of_blocks : Prop

/-- Ko admissibility criterion: all super Jordan blocks have odd size. -/
def SuperJordanNormalForm.OSpAdmissible
    {Element : Type*}
    (N : SuperJordanNormalForm Element) : Prop :=
  ∀ B ∈ N.blocks, B.AdmissibleOdd

/-- Witness that an `osp(1|2)` subalgebra contains the odd nilpotent element. -/
structure OSpOneTwoEmbeddingWitness
    (Element OSpSubalgebra : Type*) where
  e : Element
  subalgebra : OSpSubalgebra
  contains_e : Prop

/--
Super Jacobson--Morozov gate socket.

This packages the bidirectional eligibility statement as witness data.
-/
structure OddNilpotentOSpGate
    (Element OSpSubalgebra : Type*) where
  normalForm : SuperJordanNormalForm Element
  /-- Forward: embedding implies odd-block normal form. -/
  embedding_implies_odd_blocks :
    OSpOneTwoEmbeddingWitness Element OSpSubalgebra →
      normalForm.OSpAdmissible
  /-- Reverse: odd-block normal form implies embedding. -/
  odd_blocks_implies_embedding :
    normalForm.OSpAdmissible →
      OSpOneTwoEmbeddingWitness Element OSpSubalgebra

/-- Re-export: `osp(1|2)` embedding implies odd super Jordan blocks. -/
theorem osp_embedding_implies_odd_super_jordan_blocks
    {Element OSpSubalgebra : Type*}
    (G : OddNilpotentOSpGate Element OSpSubalgebra)
    (W : OSpOneTwoEmbeddingWitness Element OSpSubalgebra) :
    G.normalForm.OSpAdmissible :=
  G.embedding_implies_odd_blocks W

/-- Re-export: odd super Jordan blocks imply an `osp(1|2)` embedding witness. -/
def odd_super_jordan_blocks_imply_osp_embedding
    {Element OSpSubalgebra : Type*}
    (G : OddNilpotentOSpGate Element OSpSubalgebra)
    (h : G.normalForm.OSpAdmissible) :
    OSpOneTwoEmbeddingWitness Element OSpSubalgebra :=
  G.odd_blocks_implies_embedding h

/-! ## 4. Cantor/CAR interpretation gate -/

/--
Witness-gated bridge from finite super Jordan data to an external
Cantor/CAR/AQFT interpretation.

The finite normal-form data alone do not construct an infinite tensor product,
CAR algebra, Cantor homeomorphism, or AQFT representation.  Those claims must
be supplied by a separate owner.
-/
structure SuperJordanCantorCARInterpretation
    (Element : Type*) where
  /-- Finite super Jordan normal-form data. -/
  normalForm : SuperJordanNormalForm Element
  /-- External carrier for a symbolic boundary, if supplied. -/
  BoundaryCarrier : Type*
  /-- External carrier for a CAR or operator-algebra realization, if supplied. -/
  CARCarrier : Type*
  /-- Supplied finite-to-boundary interpretation law. -/
  finiteBoundaryLaw : Prop
  /-- Certificate for the finite-to-boundary interpretation law. -/
  finiteBoundaryCertificate : finiteBoundaryLaw
  /-- Supplied finite-to-CAR interpretation law. -/
  finiteCARLaw : Prop
  /-- Certificate for the finite-to-CAR interpretation law. -/
  finiteCARCertificate : finiteCARLaw
  /-- Guardrail: no infinite tensor-product theorem is proved here. -/
  noInfiniteTensorProductClaim : Type*
  /-- Guardrail: no Cantor homeomorphism theorem is proved here. -/
  noCantorHomeomorphismClaim : Type*
  /-- Guardrail: no AQFT representation theorem is proved here. -/
  noAQFTRepresentationClaim : Type*

namespace SuperJordanCantorCARInterpretation

variable {Element : Type*}

/-- Re-export of the supplied finite-to-boundary law. -/
theorem finiteBoundary_valid
    (I : SuperJordanCantorCARInterpretation Element) :
    I.finiteBoundaryLaw :=
  I.finiteBoundaryCertificate

/-- Re-export of the supplied finite-to-CAR law. -/
theorem finiteCAR_valid
    (I : SuperJordanCantorCARInterpretation Element) :
    I.finiteCARLaw :=
  I.finiteCARCertificate

end SuperJordanCantorCARInterpretation

end InfoGeometry.Algebraic.OddNilpotentOSpBridge

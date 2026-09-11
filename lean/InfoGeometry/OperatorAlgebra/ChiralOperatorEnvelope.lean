import Mathlib.Algebra.FreeAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.OperatorAlgebra

/-!
# Associative envelope for the chiral operator channels

The eight-dimensional Zorn/Sage carrier is a readout layer. This owner keeps
operator products in an associative free algebra, so same-chirality and
mixed-chirality words remain distinct expressions until a later representation
or projection supplies relations.
-/

inductive ChiralGenerator
  | pPlus
  | pMinus
  | sPlus (i : Fin 3)
  | sMinus (i : Fin 3)
deriving DecidableEq, Fintype

abbrev ChiralOperatorEnvelope (R : Type*) [CommRing R] :=
  FreeAlgebra R ChiralGenerator

namespace ChiralOperatorEnvelope

variable {R : Type*} [CommRing R]

/-- The universal associative operator represented by a generator. -/
def ofGenerator (g : ChiralGenerator) : ChiralOperatorEnvelope R :=
  FreeAlgebra.ι R g

/-- The two Peirce projector symbols. -/
def PPlus : ChiralOperatorEnvelope R := ofGenerator .pPlus

def PMinus : ChiralOperatorEnvelope R := ofGenerator .pMinus

/-- The three positive and negative chiral operator components. -/
def SPlus (i : Fin 3) : ChiralOperatorEnvelope R := ofGenerator (.sPlus i)

def SMinus (i : Fin 3) : ChiralOperatorEnvelope R := ofGenerator (.sMinus i)

/-- Associative commutator and anticommutator in the operator envelope. -/
def commutator (X Y : ChiralOperatorEnvelope R) : ChiralOperatorEnvelope R :=
  X * Y - Y * X

def anticommutator (X Y : ChiralOperatorEnvelope R) : ChiralOperatorEnvelope R :=
  X * Y + Y * X

theorem product_associative (X Y Z : ChiralOperatorEnvelope R) :
    (X * Y) * Z = X * (Y * Z) :=
  mul_assoc X Y Z

theorem commutator_antisymmetric (X Y : ChiralOperatorEnvelope R) :
    commutator X Y = -commutator Y X := by
  unfold commutator
  abel

theorem same_chirality_plus_is_operator_product (i j : Fin 3) :
    SPlus (R := R) i * SPlus (R := R) j =
      ofGenerator (R := R) (.sPlus i) * ofGenerator (R := R) (.sPlus j) :=
  rfl

theorem same_chirality_minus_is_operator_product (i j : Fin 3) :
    SMinus (R := R) i * SMinus (R := R) j =
      ofGenerator (R := R) (.sMinus i) * ofGenerator (R := R) (.sMinus j) :=
  rfl

theorem mixed_chirality_plus_minus_is_operator_product (i j : Fin 3) :
    SPlus (R := R) i * SMinus (R := R) j =
      ofGenerator (R := R) (.sPlus i) * ofGenerator (R := R) (.sMinus j) :=
  rfl

theorem mixed_chirality_minus_plus_is_operator_product (i j : Fin 3) :
    SMinus (R := R) i * SPlus (R := R) j =
      ofGenerator (R := R) (.sMinus i) * ofGenerator (R := R) (.sPlus j) :=
  rfl

/-- A Peirce-support predicate for a concrete associative representation.

This is a proposition, not a wrapper carrying a second copy of the operators.
It can be instantiated by a representation of the universal envelope. -/
def PeirceSupported
    {A : Type*} [Ring A]
    (Pp Pm : A) (Sp Sm : Fin 3 -> A) : Prop :=
  Pp * Pp = Pp /\
    Pm * Pm = Pm /\
    Pp * Pm = 0 /\
    Pm * Pp = 0 /\
    Pp + Pm = 1 /\
    (forall i, Pp * Sp i = Sp i /\ Sp i * Pm = Sp i) /\
    (forall i, Pm * Sm i = Sm i /\ Sm i * Pp = Sm i)

theorem PeirceSupported.projector_plus_idempotent
    {A : Type*} [Ring A]
    {Pp Pm : A} {Sp Sm : Fin 3 -> A}
    (h : PeirceSupported Pp Pm Sp Sm) :
    Pp * Pp = Pp :=
  h.1

theorem PeirceSupported.projector_minus_idempotent
    {A : Type*} [Ring A]
    {Pp Pm : A} {Sp Sm : Fin 3 -> A}
    (h : PeirceSupported Pp Pm Sp Sm) :
    Pm * Pm = Pm :=
  h.2.1

theorem PeirceSupported.plus_support
    {A : Type*} [Ring A]
    {Pp Pm : A} {Sp Sm : Fin 3 -> A}
    (h : PeirceSupported Pp Pm Sp Sm) (i : Fin 3) :
    Pp * Sp i = Sp i /\ Sp i * Pm = Sp i :=
  h.2.2.2.2.2.1 i

theorem PeirceSupported.minus_support
    {A : Type*} [Ring A]
    {Pp Pm : A} {Sp Sm : Fin 3 -> A}
    (h : PeirceSupported Pp Pm Sp Sm) (i : Fin 3) :
    Pm * Sm i = Sm i /\ Sm i * Pp = Sm i :=
  h.2.2.2.2.2.2 i

/-- Formal integer degree of the four generator channels. -/
def generatorDegree : ChiralGenerator -> Int
  | .pPlus => 0
  | .pMinus => 0
  | .sPlus _ => 1
  | .sMinus _ => -1

def wordDegree : List ChiralGenerator -> Int
  | [] => 0
  | g :: w => generatorDegree g + wordDegree w

theorem wordDegree_append (u v : List ChiralGenerator) :
    wordDegree (u ++ v) = wordDegree u + wordDegree v := by
  induction u with
  | nil => simp [wordDegree]
  | cons g u ih =>
      simp [wordDegree, ih, add_assoc]

/-- The associative operator word represented by a finite generator word. -/
def word : List ChiralGenerator -> ChiralOperatorEnvelope R
  | [] => 1
  | g :: w => ofGenerator g * word w

theorem word_append (u v : List ChiralGenerator) :
    word (R := R) (u ++ v) = word (R := R) u * word (R := R) v := by
  induction u with
  | nil => simp [word]
  | cons g u ih =>
      simp [word, ih, mul_assoc]

end ChiralOperatorEnvelope

end InfoGeometry.OperatorAlgebra

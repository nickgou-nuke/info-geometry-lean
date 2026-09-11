import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hestenes B₂ Quaternion Comparison Bridge

This file provides a thin comparison bridge connecting the local algebraic atoms of the 
Hestenes carrier with the exceptional Weyl/lattice quaternionic atoms.

We establish the structural correspondence between the specific generators from the 
Weyl-lattice literature and our existing split-Clifford/Hestenes data:
1. Literature atom (Dual Quaternions): $I^2 = -1, J^2 = +1, IJ = -JI$
2. Hestenes atom (Split-Clifford): $I^2 = -1, H^2 = +1, IH = -HI$

This algebraic seed provides the $W(B_2) \cong W(C_2)$ symmetry generator and acts
as the starting point for exceptional $F_4/E_8$-type Weyl globalization, fully decoupled 
from the quantum braiding layer.
-/

namespace InfoGeometry.Canonical.HestenesB2QuaternionComparisonBridge

/-- 
The abstract specification of the dual-quaternionic atom 
used to generate the exceptional Weyl reflection geometry.
-/
class AbstractSplitQuaternionAtom (A : Type*) [Ring A] where
  I : A
  J : A
  I_sq : I * I = -1
  J_sq : J * J = 1
  anti_comm : I * J = -(J * I)

/--
The abstract specification of the Hestenes carrier local atom.
-/
class AbstractHestenesAtom (A : Type*) [Ring A] where
  I : A
  H : A
  I_sq : I * I = -1
  H_sq : H * H = 1
  anti_comm : I * H = -(H * I)

/-- 
The canonical identification: the local Weyl-lattice quaternionic atom 
is structurally identical to the Hestenes local atom.
-/
def hestenesAtom_of_splitQuaternionAtom (A : Type*) [Ring A] 
    [atom : AbstractSplitQuaternionAtom A] : AbstractHestenesAtom A where
  I := atom.I
  H := atom.J
  I_sq := atom.I_sq
  H_sq := atom.J_sq
  anti_comm := atom.anti_comm

/-- 
The canonical identification: the Hestenes local atom is structurally identical 
to the local Weyl-lattice quaternionic atom.
-/
def splitQuaternionAtom_of_hestenesAtom (A : Type*) [Ring A] 
    [atom : AbstractHestenesAtom A] : AbstractSplitQuaternionAtom A where
  I := atom.I
  J := atom.H
  I_sq := atom.I_sq
  J_sq := atom.H_sq
  anti_comm := atom.anti_comm

end InfoGeometry.Canonical.HestenesB2QuaternionComparisonBridge

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.GrandUnification.ArchetypeDictionary
import InfoGeometry.GrandUnification.PfaffianSquareRootCharacter
import InfoGeometry.GrandUnification.SupertraceBerezinianBridge
import InfoGeometry.GrandUnification.SymplecticCartanInvolutionBridge
import InfoGeometry.Canonical.DeterminantTrifactor
import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.Volume.Pfaffian
import InfoGeometry.Canonical.ParaComplexNeutralForm
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Index of Finite Algebraic Owners

This file imports finite theorem owners that formalize several related but
mathematically distinct constructions. It is an import index, not a theorem
identifying the subjects as one geometric structure or proving bridges that
the owner files do not state.

The imported results have finite algebraic scopes: determinant and matrix
exponential identities; two-dimensional skew-matrix Pfaffian identities;
block-diagonal Berezinian and supertrace identities; linear para-complex
eigenspace results; and split-involution projector decompositions. They do not
by themselves establish manifold-level spin structures, anomalies, a general
supermanifold Berezinian theorem, or metaplectic representations.
-/

namespace InfoGeometry.GrandUnification.MasterArchetypeDictionary

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

theorem master_archetype_dictionary_operator_identities
    {P : B} (hP : P * P = P) (A C X : B) :
    invS P * invS P = (1 : B) ∧
    evenGrade P X + oddGrade P X = X ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end InfoGeometry.GrandUnification.MasterArchetypeDictionary

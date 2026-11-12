/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.CSSKoszulExtension
import InfoGeometry.Quantum.LatticeTranslationRing
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Matrix CSS presentations of the coupled Koszul complex

The stabilizer presentation matrices are the matrices of the already defined
native linear maps, in standard product bases. Their block formulas reproduce
equation (161) of arXiv:2608.09913v2. Over the actual lattice translation ring,
spatial inversion and transpose give both CSS isotropy identities.

These are identities of rectangular operator matrices over the translation
ring. This module does not construct a Hilbert-space Pauli representation or
a finite-depth Clifford circuit.
-/

namespace InfoGeometry.Quantum.CSSKoszulPauli

open CategoryTheory Matrix Module
open CSSKoszulExtension LatticeTranslationRing

noncomputable section

universe u

variable (R : Type u) [CommRing R]

def sourceBasis : Basis (Fin 3 ⊕ Unit) R (Vec3 R × R) :=
  (Pi.basisFun R (Fin 3)).prod (Basis.singleton Unit R)

def middleBasis : Basis (Fin 3 ⊕ Fin 3) R (Vec3 R × Vec3 R) :=
  (Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))

def targetBasis : Basis (Unit ⊕ Fin 3) R (R × Vec3 R) :=
  (Basis.singleton Unit R).prod (Pi.basisFun R (Fin 3))

variable {R}

/-- The incoming stabilizer matrix, constructed from the native complex map. -/
def zMatrix (f a : Vec3 R) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Unit) R :=
  LinearMap.toMatrix (sourceBasis R) (middleBasis R) (incoming f a)

/-- The outgoing matrix, whose lattice dagger is the other CSS presentation. -/
def boundaryMatrix (f a : Vec3 R) : Matrix (Unit ⊕ Fin 3) (Fin 3 ⊕ Fin 3) R :=
  LinearMap.toMatrix (middleBasis R) (targetBasis R) (outgoing f a)

@[simp] theorem zMatrix_toLin (f a : Vec3 R) :
    Matrix.toLin (sourceBasis R) (middleBasis R) (zMatrix f a) = incoming f a :=
  Matrix.toLin_toMatrix _ _ _

@[simp] theorem boundaryMatrix_toLin (f a : Vec3 R) :
    Matrix.toLin (middleBasis R) (targetBasis R) (boundaryMatrix f a) = outgoing f a :=
  Matrix.toLin_toMatrix _ _ _

/-- The `6 × 4` incoming matrix retains the off-diagonal coupling column. -/
theorem zMatrix_eq_fromBlocks (f a : Vec3 R) :
    zMatrix f a = Matrix.fromBlocks (koszulMatrix f) (fun i (_ : Unit) => a i)
      (0 : Matrix (Fin 3) (Fin 3) R) (fun i (_ : Unit) => f i) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [zMatrix, LinearMap.toMatrix_apply, sourceBasis, middleBasis,
      incoming_apply, boundary2, Matrix.fromBlocks]

/-- The `4 × 6` outgoing matrix has the compensating negative coupling row. -/
theorem boundaryMatrix_eq_fromBlocks (f a : Vec3 R) :
    boundaryMatrix f a = Matrix.fromBlocks (fun (_ : Unit) i => f i)
      (fun (_ : Unit) i => -a i) (0 : Matrix (Fin 3) (Fin 3) R) (koszulMatrix f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [boundaryMatrix, LinearMap.toMatrix_apply, middleBasis, targetBasis,
      outgoing_apply, boundary1, boundary2, Matrix.fromBlocks]

/-- Matrix composition vanishes because the linked native maps form a complex. -/
theorem boundaryMatrix_mul_zMatrix (f a : Vec3 R) :
    boundaryMatrix f a * zMatrix f a = 0 := by
  rw [boundaryMatrix, zMatrix, ← LinearMap.toMatrix_comp]
  rw [outgoing_comp_incoming]
  simp

variable (k : Type u) [CommRing k] (D : ℕ)

/-- The `X`-sector presentation uses translation inversion and transpose. -/
def xMatrix (f a : Vec3 (Coefficients k D)) :
    Matrix (Fin 3 ⊕ Fin 3) (Unit ⊕ Fin 3) (Coefficients k D) :=
  dagger k D (boundaryMatrix f a)

/-- One CSS isotropy identity, inherited from the native coupled complex. -/
theorem dagger_xMatrix_mul_zMatrix (f a : Vec3 (Coefficients k D)) :
    dagger k D (xMatrix k D f a) * zMatrix f a = 0 := by
  rw [xMatrix, dagger_dagger, boundaryMatrix_mul_zMatrix]

/-- The second CSS isotropy identity follows by the order-reversing dagger. -/
theorem dagger_zMatrix_mul_xMatrix (f a : Vec3 (Coefficients k D)) :
    dagger k D (zMatrix f a) * xMatrix k D f a = 0 := by
  rw [xMatrix, ← dagger_mul, boundaryMatrix_mul_zMatrix, dagger_zero]

end

end InfoGeometry.Quantum.CSSKoszulPauli

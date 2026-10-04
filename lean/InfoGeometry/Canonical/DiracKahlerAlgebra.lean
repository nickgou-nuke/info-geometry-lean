import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic

/-!
# Foundational Quotient Algebra for the Dirac-Kähler Structure

Instead of constructing the algebra post-hoc or via lightweight structural macros,
we build the Dirac-Kähler algebra as a true Mathlib native `RingQuot` of a
`FreeAlgebra`, fully embodying its algebraic constraints. Then, we map this
abstract algebra structurally to its 2x2 matrix representations.
-/

namespace InfoGeometry.Canonical

/-- Generators of the abstract Dirac-Kähler algebra. -/
inductive DKVars
| J -- Chiral/Polarization Generator
| D -- Dirac Operator Generator
deriving DecidableEq, Repr

open DKVars

/-- The native quotient relations defining the Dirac-Kähler algebra over a commutative ring R.
    1. J^2 = 1
    2. J D + D J = 0 (Chirality / Anticommutation)
-/
inductive DKRel (R : Type*) [CommRing R] : FreeAlgebra R DKVars → FreeAlgebra R DKVars → Prop
| j_sq : DKRel R (FreeAlgebra.ι R J * FreeAlgebra.ι R J) 1
| chiral : DKRel R (FreeAlgebra.ι R D * FreeAlgebra.ι R J + FreeAlgebra.ι R J * FreeAlgebra.ι R D) 0

/-- The Dirac-Kähler Algebra as a foundational `RingQuot`. -/
noncomputable def DiracKahlerAlgebra (R : Type*) [CommRing R] := RingQuot (DKRel R)

instance (R : Type*) [CommRing R] : Ring (DiracKahlerAlgebra R) :=
  RingQuot.instRing (DKRel R)

instance (R : Type*) [CommRing R] : Algebra R (DiracKahlerAlgebra R) :=
  RingQuot.instAlgebra (DKRel R)

/-- The canonical injection of the generators into the quotient algebra. -/
noncomputable def dkGen (R : Type*) [CommRing R] (v : DKVars) : DiracKahlerAlgebra R :=
  RingQuot.mkAlgHom R (DKRel R) (FreeAlgebra.ι R v)

/-- Verification that the algebra intrinsically satisfies J^2 = 1. -/
theorem dkGen_J_sq (R : Type*) [CommRing R] : dkGen R J * dkGen R J = 1 := by
  have H : dkGen R J * dkGen R J = RingQuot.mkAlgHom R (DKRel R) (FreeAlgebra.ι R J * FreeAlgebra.ι R J) := by
    exact (map_mul (RingQuot.mkAlgHom R (DKRel R)) _ _).symm
  rw [H]
  have H1 : (1 : DiracKahlerAlgebra R) = RingQuot.mkAlgHom R (DKRel R) 1 := (map_one (RingQuot.mkAlgHom R (DKRel R))).symm
  rw [H1]
  exact RingQuot.mkAlgHom_rel R (DKRel.j_sq)

/-- Verification that the algebra intrinsically satisfies {D, J} = 0. -/
theorem dkGen_chiral (R : Type*) [CommRing R] : dkGen R D * dkGen R J + dkGen R J * dkGen R D = 0 := by
  have H1 : dkGen R D * dkGen R J = RingQuot.mkAlgHom R (DKRel R) (FreeAlgebra.ι R D * FreeAlgebra.ι R J) :=
    (map_mul (RingQuot.mkAlgHom R (DKRel R)) _ _).symm
  have H2 : dkGen R J * dkGen R D = RingQuot.mkAlgHom R (DKRel R) (FreeAlgebra.ι R J * FreeAlgebra.ι R D) :=
    (map_mul (RingQuot.mkAlgHom R (DKRel R)) _ _).symm
  rw [H1, H2]
  have H3 : RingQuot.mkAlgHom R (DKRel R) (FreeAlgebra.ι R D * FreeAlgebra.ι R J) + RingQuot.mkAlgHom R (DKRel R) (FreeAlgebra.ι R J * FreeAlgebra.ι R D) = RingQuot.mkAlgHom R (DKRel R) (FreeAlgebra.ι R D * FreeAlgebra.ι R J + FreeAlgebra.ι R J * FreeAlgebra.ι R D) :=
    (map_add (RingQuot.mkAlgHom R (DKRel R)) _ _).symm
  rw [H3]
  have H0 : (0 : DiracKahlerAlgebra R) = RingQuot.mkAlgHom R (DKRel R) 0 := (map_zero (RingQuot.mkAlgHom R (DKRel R))).symm
  rw [H0]
  exact RingQuot.mkAlgHom_rel R (DKRel.chiral)

/-- Conjugation by the involutive generator reverses the anticommuting
operator. This is the algebraic parity action on the universal generator; it
does not assert that the operator squares to zero. -/
theorem dkGen_J_conjugates_D (R : Type*) [CommRing R] :
    dkGen R J * dkGen R D * dkGen R J = -dkGen R D := by
  have hJ := dkGen_J_sq R
  have hDJ := dkGen_chiral R
  have hJD : dkGen R J * dkGen R D = -(dkGen R D * dkGen R J) := by
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hDJ)
  calc
    dkGen R J * dkGen R D * dkGen R J =
        -(dkGen R D * dkGen R J) * dkGen R J := by rw [hJD]
    _ = -dkGen R D := by rw [neg_mul, mul_assoc, hJ]; simp

/-- The chosen matrix for each free generator. -/
def dkMatrixGenerator {R : Type*} [CommRing R] (a b : R) :
    DKVars → Matrix (Fin 2) (Fin 2) R
  | J => !![(1 : R), 0; 0, -1]
  | D => !![(0 : R), a; b, 0]

/-- The free-algebra representation before imposing the two relations. -/
noncomputable def dkMatrixFreeRep {R : Type*} [CommRing R] (a b : R) :
    FreeAlgebra R DKVars →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  FreeAlgebra.lift R (dkMatrixGenerator a b)

/-- The matrix assignment respects both generators of the quotient relation. -/
theorem dkMatrixFreeRep_respects {R : Type*} [CommRing R] (a b : R)
    {x y : FreeAlgebra R DKVars} : DKRel R x y →
    dkMatrixFreeRep a b x = dkMatrixFreeRep a b y := by
  intro h
  cases h with
  | j_sq =>
      simp only [dkMatrixFreeRep, map_mul, map_one, FreeAlgebra.lift_ι_apply,
        dkMatrixGenerator]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  | chiral =>
      simp only [dkMatrixFreeRep, map_add, map_mul, map_zero,
        FreeAlgebra.lift_ι_apply, dkMatrixGenerator]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.zero_apply]

/-- The matrix representation of the quotient algebra, obtained from the
Mathlib universal property of `RingQuot`. -/
noncomputable def dkMatrixRep {R : Type*} [CommRing R] (a b : R) :
  DiracKahlerAlgebra R →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  RingQuot.liftAlgHom R ⟨dkMatrixFreeRep a b,
    fun {_x _y} (h : DKRel R _x _y) => dkMatrixFreeRep_respects a b h⟩

/-- The quotient representation sends the polarization generator to its
diagonal involution matrix. -/
@[simp] theorem dkMatrixRep_apply_J {R : Type*} [CommRing R] (a b : R) :
    dkMatrixRep a b (dkGen R J) = !![(1 : R), 0; 0, -1] := by
  change RingQuot.liftAlgHom R
      ⟨dkMatrixFreeRep a b,
        fun {_x _y} (h : DKRel R _x _y) => dkMatrixFreeRep_respects a b h⟩
      ((RingQuot.mkAlgHom R (DKRel R)) (FreeAlgebra.ι R J)) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp [dkMatrixFreeRep, dkMatrixGenerator]

/-- The quotient representation sends the Dirac generator to its
off-diagonal matrix. -/
@[simp] theorem dkMatrixRep_apply_D {R : Type*} [CommRing R] (a b : R) :
    dkMatrixRep a b (dkGen R D) = !![(0 : R), a; b, 0] := by
  change RingQuot.liftAlgHom R
      ⟨dkMatrixFreeRep a b,
        fun {_x _y} (h : DKRel R _x _y) => dkMatrixFreeRep_respects a b h⟩
      ((RingQuot.mkAlgHom R (DKRel R)) (FreeAlgebra.ι R D)) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp [dkMatrixFreeRep, dkMatrixGenerator]

end InfoGeometry.Canonical

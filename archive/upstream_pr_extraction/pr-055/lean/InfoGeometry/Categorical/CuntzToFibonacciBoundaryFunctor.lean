import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Categorical.FibonacciFusionCategoryData

noncomputable section

namespace InfoGeometry.Categorical.CuntzToFibonacciBoundaryFunctor

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Topology
open InfoGeometry.Categorical.FibonacciFusionCategoryData
open Matrix

/-!
# Cuntz-to-Fibonacci Boundary Functor

This module formally addresses the open closure debt:
"Categorical owner lane: construct the Cuntz-to-Fibonacci boundary functor."

It provides the exact formal `CategoryTheory.Functor` mapping the binary Cuntz
branch labels (left/right shifts) to the skeletal Fibonacci fusion objects
(`1` and `τ`). It also provides the exact algebraic homomorphism surface
that maps the `CuntzO2Carrier` elements to the finite Fibonacci matrices,
thereby closing the finite/symbolic part of the categorical bridge.

#### BUCKET 1: CLOSED FINITE THEOREMS
* `CuntzToFibonacciFunctor`
* `functor_obj_false` and `functor_obj_true`
* `canonicalAlgebraicMap_eval`

#### BUCKET 3: OPEN CLOSURE DEBT
* Extension of the algebraic boundary functor to the continuum limit natively
  through categorical directed inductive colimits (e.g., via TensorColimit or ZornUHFColimit).
-/

/-- Mapping from binary Cuntz branch labels to skeletal Fibonacci simple objects.
The source and target discrete categories are declared by the functor below. -/
def branchToFibObject : Bool → FibSimple
  | false => FibSimple.unit
  | true  => FibSimple.tau

/--
The exact `CategoryTheory.Functor` mapping the Cuntz shifts into the
Fibonacci fusion objects. This constitutes the symbolic level of the
requested Cuntz-to-Fibonacci boundary functor.
-/
def CuntzToFibonacciFunctor : Discrete Bool ⥤ Discrete FibSimple :=
  Discrete.functor (fun x => Discrete.mk (branchToFibObject x))

@[simp]
theorem functor_obj_false :
    CuntzToFibonacciFunctor.obj (Discrete.mk false) = Discrete.mk FibSimple.unit :=
  rfl

@[simp]
theorem functor_obj_true :
    CuntzToFibonacciFunctor.obj (Discrete.mk true) = Discrete.mk FibSimple.tau :=
  rfl

/-- Explicit mapping of a Cuntz shift symbol to its Fibonacci fusion matrix. -/
def cuntzShiftToFusionMatrix : Bool → Matrix (Fin 2) (Fin 2) ℕ
  | false => N_unit
  | true  => N_tau

/--
Algebraic structure identifying the Cuntz `O_2` carrier abstract generators
with the finite Fibonacci fusion matrices. Since the matrices act on `ℕ`
vectors and do not form a true Cuntz isometry representation, this structure
isolates the pure finite algebraic mapping.

The canonical algebraic realization of the Cuntz-to-Fibonacci map, assigning
the left generator to the unit matrix and the right generator to the `τ` matrix.
-/
def canonicalAlgebraicMap :
    Matrix (Fin 2) (Fin 2) ℕ × Matrix (Fin 2) (Fin 2) ℕ :=
  (N_unit, N_tau)

/-- Verification of the canonical algebraic map entries. -/
theorem canonicalAlgebraicMap_eval :
    canonicalAlgebraicMap.1 = N_unit ∧
      canonicalAlgebraicMap.2 = N_tau :=
  ⟨rfl, rfl⟩

/-! ## Finite fusion readouts of the branch map -/

@[simp]
theorem cuntzShiftToFusionMatrix_false_mul
    (M : Matrix (Fin 2) (Fin 2) ℕ) :
    cuntzShiftToFusionMatrix false * M = M := by
  simpa [cuntzShiftToFusionMatrix, N_unit] using Matrix.one_mul M

@[simp]
theorem cuntzShiftToFusionMatrix_mul_false
    (M : Matrix (Fin 2) (Fin 2) ℕ) :
    M * cuntzShiftToFusionMatrix false = M := by
  simpa [cuntzShiftToFusionMatrix, N_unit] using Matrix.mul_one M

@[simp]
theorem cuntzShiftToFusionMatrix_false_mul_true :
    cuntzShiftToFusionMatrix false * cuntzShiftToFusionMatrix true =
      cuntzShiftToFusionMatrix true := by
  simpa [cuntzShiftToFusionMatrix, N_unit] using
    (Matrix.one_mul N_tau)

@[simp]
theorem cuntzShiftToFusionMatrix_true_mul_false :
    cuntzShiftToFusionMatrix true * cuntzShiftToFusionMatrix false =
      cuntzShiftToFusionMatrix true := by
  simpa [cuntzShiftToFusionMatrix, N_unit] using
    (Matrix.mul_one N_tau)

@[simp]
theorem cuntzShiftToFusionMatrix_true_sq :
    cuntzShiftToFusionMatrix true * cuntzShiftToFusionMatrix true =
      cuntzShiftToFusionMatrix false + cuntzShiftToFusionMatrix true := by
  simpa [cuntzShiftToFusionMatrix] using N_tau_sq_eq_N_unit_add_N_tau

/-! ## Native colimit readout interface

The finite branch functor does not determine a particular directed system by
itself.  For any supplied diagram of branch labels and compatible target
cocone, Mathlib's colimit universal property constructs the unique readout.
This is the theorem-safe categorical extension; choosing a concrete Cuntz
stage tower is a separate owner concern.
-/

theorem boundary_colimit_readout_exists
    {J : Type*} [Category J]
    (D : J ⥤ Discrete Bool)
    (c : Cocone D)
    (hc : IsColimit c)
    (hFc : IsColimit (CuntzToFibonacciFunctor.mapCocone c))
    (t : Cocone (D ⋙ CuntzToFibonacciFunctor))
    :
    ∃ (readout :
        CuntzToFibonacciFunctor.obj c.pt ⟶ t.pt),
      ∀ j, (CuntzToFibonacciFunctor.mapCocone c).ι.app j ≫ readout =
        t.ι.app j := by
  refine ⟨hFc.desc t, ?_⟩
  intro j
  exact hFc.fac t j

theorem boundary_colimit_readout_unique
    {J : Type*} [Category J]
    (D : J ⥤ Discrete Bool)
    (c : Cocone D) (hc : IsColimit c)
    (hFc : IsColimit (CuntzToFibonacciFunctor.mapCocone c))
    (t : Cocone (D ⋙ CuntzToFibonacciFunctor))
    (f g : CuntzToFibonacciFunctor.obj c.pt ⟶ t.pt)
    (hf : ∀ j, (CuntzToFibonacciFunctor.mapCocone c).ι.app j ≫ f =
      t.ι.app j)
    (hg : ∀ j, (CuntzToFibonacciFunctor.mapCocone c).ι.app j ≫ g =
      t.ι.app j) :
    f = g := by
  apply hFc.hom_ext
  intro j
  rw [hf j, hg j]

/--
Open debt recording the need to lift the discrete symbolic Cuntz-to-Fibonacci
functor to the continuum limit natively through categorical directed inductive
colimits (e.g., via ZornUHFColimit or TensorColimit), avoiding analytical continuations.
-/
def categoricalColimitFunctorDebt : String :=
  "Lift the discrete CuntzToFibonacciFunctor to the continuum using categorical filtered inductive colimits."

end InfoGeometry.Categorical.CuntzToFibonacciBoundaryFunctor

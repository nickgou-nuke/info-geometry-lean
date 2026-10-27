import InfoGeometry.Topology.KleinDeckRepresentation
import InfoGeometry.Twistor.TwistorKinematicTensor
import Mathlib

/-!
# Explicit Clifford lifts of the Klein reflection

Both quadratic signatures are realized by native CliffordAlgebra homomorphisms.
The reflected tangent vector and the affine glide are separate. A lift's square
is additional data: +1 and -1 have the same reflected tangent action. This does
not claim a classification of Pin bundles or turn a nonorientable base into Spin.
-/
noncomputable section
namespace InfoGeometry.Topology.KleinCliffordPinLift
open KleinQuotientDeckInvariants KleinDeckRepresentation
open scoped KleinDeckRepresentation Matrix

abbrev Tangent := Fin 2 → ℝ
abbrev Spinor := Fin 2 → ℂ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def positiveForm : QuadraticForm ℝ Tangent :=
  QuadraticMap.sq.comp (LinearMap.proj 0) + QuadraticMap.sq.comp (LinearMap.proj 1)

def negativeForm : QuadraticForm ℝ Tangent := -positiveForm

@[simp] theorem positiveForm_apply (v : Tangent) : positiveForm v=v 0*v 0+v 1*v 1 := rfl
@[simp] theorem negativeForm_apply (v : Tangent) : negativeForm v=-(v 0*v 0+v 1*v 1) := rfl

def vectorPlus : Tangent →ₗ[ℝ] Mat where
  toFun v := !![(v 1:ℂ),(v 0:ℂ); (v 0:ℂ),-(v 1:ℂ)]
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' r v := by ext i j; fin_cases i <;> fin_cases j <;> simp [smul_eq_mul]

def vectorMinus : Tangent →ₗ[ℝ] Mat := Complex.I • vectorPlus

theorem vectorPlus_square (v : Tangent) :
    vectorPlus v * vectorPlus v=algebraMap ℝ Mat (positiveForm v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vectorPlus,Matrix.mul_apply,Fin.sum_univ_two,Matrix.algebraMap_apply] <;> ring

theorem vectorMinus_square (v : Tangent) :
    vectorMinus v * vectorMinus v=algebraMap ℝ Mat (negativeForm v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vectorMinus,vectorPlus,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.algebraMap_apply,smul_eq_mul,Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]

def positiveRepresentation : CliffordAlgebra positiveForm →ₐ[ℝ] Mat :=
  CliffordAlgebra.lift positiveForm ⟨vectorPlus,vectorPlus_square⟩

def negativeRepresentation : CliffordAlgebra negativeForm →ₐ[ℝ] Mat :=
  CliffordAlgebra.lift negativeForm ⟨vectorMinus,vectorMinus_square⟩

@[simp] theorem positiveRepresentation_vector (v : Tangent) :
    positiveRepresentation (CliffordAlgebra.ι positiveForm v)=vectorPlus v :=
  CliffordAlgebra.lift_ι_apply _ _ _

@[simp] theorem negativeRepresentation_vector (v : Tangent) :
    negativeRepresentation (CliffordAlgebra.ι negativeForm v)=vectorMinus v :=
  CliffordAlgebra.lift_ι_apply _ _ _

def reflectionPlus : Mat := !![0,1;1,0]
def reflectionMinus : Mat := Complex.I • reflectionPlus

theorem reflectionPlus_square : reflectionPlus*reflectionPlus=1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [reflectionPlus,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem reflectionMinus_square : reflectionMinus*reflectionMinus=-1 := by
  simp [reflectionMinus,smul_mul_assoc,mul_smul_comm,smul_smul,
    reflectionPlus_square,Complex.I_sq]

def plusUnit : Matˣ := ⟨reflectionPlus,reflectionPlus,reflectionPlus_square,reflectionPlus_square⟩
def minusUnit : Matˣ := ⟨reflectionMinus,-reflectionMinus,
  by rw [mul_neg,reflectionMinus_square,neg_neg],
  by rw [neg_mul,reflectionMinus_square,neg_neg]⟩

def reflected (v : Tangent) : Tangent := ![-v 0,v 1]

/-- Twisted adjoint, not ordinary conjugation, gives the vector reflection. -/
theorem plus_twisted_adjoint (v : Tangent) :
    -(plusUnit.val * vectorPlus v * plusUnit.inv)=vectorPlus (reflected v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusUnit,reflectionPlus,vectorPlus,reflected,Matrix.mul_apply,Fin.sum_univ_two]

/-- The negative Clifford lift has the same geometric reflection but different square. -/
theorem minus_twisted_adjoint (v : Tangent) :
    -(minusUnit.val * vectorMinus v * minusUnit.inv)=vectorMinus (reflected v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusUnit,reflectionMinus,reflectionPlus,vectorMinus,vectorPlus,reflected,
      Matrix.mul_apply,Fin.sum_univ_two,smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq]

/-- This is precisely the existing deck derivative, not an unrelated reflection. -/
theorem reflected_eq_deck_linear (v : Tangent) :
    reflected v=deckB_diff.mulVec v := by
  ext i
  fin_cases i <;> simp [reflected,deckB_diff,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

def signUnit (s : Bool) : Matˣ := if s then -1 else 1

theorem signUnit_square (s : Bool) : signUnit s * signUnit s=1 := by cases s <;> simp [signUnit]

theorem signUnit_commute (s : Bool) (U : Matˣ) : Commute (signUnit s) U := by
  cases s <;> simp [signUnit,Commute,SemiconjBy]

def plusMonodromy (s t : Bool) : KleinDeckGroup →* Matˣ :=
  flatRepresentation (signUnit s) (signUnit t*plusUnit)
    (signUnit_square s) (signUnit_commute _ _)

def minusMonodromy (s t : Bool) : KleinDeckGroup →* Matˣ :=
  flatRepresentation (signUnit s) (signUnit t*minusUnit)
    (signUnit_square s) (signUnit_commute _ _)

theorem plus_double_glide (s t : Bool) :
    ((plusMonodromy s t (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b)).val)=1 := by
  rw [plusMonodromy,flatRepresentation_double_glide]
  cases t <;> simp [signUnit,plusUnit,reflectionPlus_square]

theorem minus_double_glide (s t : Bool) :
    ((minusMonodromy s t (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b)).val)=-1 := by
  rw [minusMonodromy,flatRepresentation_double_glide]
  cases t <;> simp [signUnit,minusUnit,reflectionMinus_square]

/-- A spatial boundary condition yields a translation sign, not pointwise invariance. -/
theorem equivariant_double_glide (R : Mat) (ψ : PlanePoint → Spinor)
    (hψ : ∀ p, ψ (deckB p)=R.mulVec (ψ p)) (p : PlanePoint) :
    ψ (p.1,p.2+2)=(R*R).mulVec (ψ p) := by
  rw [← deckB_sq p,hψ,hψ,Matrix.mulVec_mulVec]

theorem minus_equivariant_antiperiodic (ψ : PlanePoint → Spinor)
    (hψ : ∀ p, ψ (deckB p)=reflectionMinus.mulVec (ψ p)) (p : PlanePoint) :
    ψ (p.1,p.2+2)=-ψ p := by
  rw [equivariant_double_glide _ ψ hψ,reflectionMinus_square]
  simp

/-- A negative lift cannot define an ordinary involution on a nonzero periodic field. -/
theorem negative_lift_periodic_obstruction (ψ : PlanePoint → Spinor)
    (hψ : ∀ p, ψ (deckB p)=reflectionMinus.mulVec (ψ p))
    (hper : ∀ p, ψ (p.1,p.2+2)=ψ p) : ψ=0 := by
  funext p
  have h := minus_equivariant_antiperiodic ψ hψ p
  rw [hper] at h
  ext i
  have hi := congrFun h i
  have : (2:ℂ)*(ψ p i)=0 := by linear_combination hi
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

end InfoGeometry.Topology.KleinCliffordPinLift

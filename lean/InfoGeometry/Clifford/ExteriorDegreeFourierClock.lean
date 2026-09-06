import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
import InfoGeometry.Algebra.FourthRootSpectralProjectors

/-!
# The actual degree-four clock on the native complex exterior algebra

Scaling each generator by `z` extends by the exterior universal property to
an algebra homomorphism. For `z = i` this is the degree clock. It fixes one,
acts by `i^k` on a wedge word of length k, and has fourth power identity.
Its Fourier projectors therefore extract degree residues on wedge words.

This clock is not left multiplication by the volume element, and it is not
a Clifford-algebra automorphism obtained by multiplying vectors by `i` in a
nonzero quadratic metric. The exterior product and Clifford product stay distinct.
-/

noncomputable section

namespace InfoGeometry.Clifford.ExteriorDegreeFourierClock

open InfoGeometry.Algebra.FourthRootSpectralProjectors

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A scalar change of generators extended by the native exterior universal property. -/
def phaseMap (z : ℂ) : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V :=
  ExteriorAlgebra.lift ℂ
    ⟨z • ExteriorAlgebra.ι ℂ, by
      intro v
      change (z • ExteriorAlgebra.ι ℂ v) * (z • ExteriorAlgebra.ι ℂ v) = 0
      rw [smul_mul_assoc, mul_smul_comm, ExteriorAlgebra.ι_sq_zero,
        smul_zero, smul_zero]⟩

@[simp] theorem phaseMap_iota (z : ℂ) (v : V) :
    phaseMap z (ExteriorAlgebra.ι ℂ v) = z • ExteriorAlgebra.ι ℂ v := by
  exact ExteriorAlgebra.lift_ι_apply ℂ _ _ v

/-- Composition is proved on generators, not postulated on a graded presentation. -/
theorem phaseMap_comp (z w : ℂ) :
    (phaseMap (V := V) z).comp (phaseMap w) = phaseMap (z * w) := by
  apply ExteriorAlgebra.hom_ext
  ext v
  change phaseMap z (phaseMap w (ExteriorAlgebra.ι ℂ v)) =
    phaseMap (z * w) (ExteriorAlgebra.ι ℂ v)
  simp only [phaseMap_iota, map_smul, smul_smul]
  rw [mul_comm]

@[simp] theorem phaseMap_one : phaseMap (V := V) 1 = AlgHom.id ℂ (ExteriorAlgebra ℂ V) := by
  apply ExteriorAlgebra.hom_ext
  ext v
  change phaseMap 1 (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ v
  simp

/-- Forget multiplication only to obtain the corresponding endomorphism. -/
def phaseEnd (z : ℂ) : Module.End ℂ (ExteriorAlgebra ℂ V) :=
  (phaseMap z).toLinearMap

theorem phaseEnd_mul (z w : ℂ) :
    phaseEnd (V := V) z * phaseEnd w = phaseEnd (z * w) := by
  ext x
  exact congrArg (fun f : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V => f x)
    (phaseMap_comp z w)

@[simp] theorem phaseEnd_one : phaseEnd (V := V) 1 = 1 := by
  ext x
  exact congrArg (fun f : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V => f x)
    (phaseMap_one (V := V))

theorem phaseEnd_pow (z : ℂ) (k : ℕ) :
    phaseEnd (V := V) z ^ k = phaseEnd (z ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, phaseEnd_mul, pow_succ]

/-- Degree clock on exterior forms, rather than a volume multiplication. -/
def degreeClock : Module.End ℂ (ExteriorAlgebra ℂ V) := phaseEnd Complex.I

theorem degreeClock_fourth : degreeClock (V := V) ^ 4 = 1 := by
  rw [degreeClock, phaseEnd_pow]
  norm_num [pow_succ]

/-- Use the already constructed Fourier polynomial without another projector family. -/
def degreeProjector (k : Fin 4) : Module.End ℂ (ExteriorAlgebra ℂ V) :=
  projector degreeClock k

/-- A concrete instance of the existing general Fourier readout. -/
def degreeReadout := fourthRootReadout (degreeClock (V := V)) degreeClock_fourth

/-- Ordered wedge word in the literal native exterior algebra. -/
def wedgeWord : List V → ExteriorAlgebra ℂ V
  | [] => 1
  | v :: vs => ExteriorAlgebra.ι ℂ v * wedgeWord vs

/-- The degree eigenvalue is derived for every word. Repeated vectors are
allowed; a zero wedge word simply satisfies the same equation. -/
theorem phaseMap_wedgeWord (z : ℂ) (vs : List V) :
    phaseMap z (wedgeWord vs) = z ^ vs.length • wedgeWord vs := by
  induction vs with
  | nil => simp [wedgeWord]
  | cons v vs ih =>
      simp only [wedgeWord, map_mul, phaseMap_iota, ih, List.length_cons,
        smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ']

/-- Residue labels belong to `Fin 4`, with the modulus bound proved. -/
def degreeResidue (k : ℕ) : Fin 4 := ⟨k % 4, Nat.mod_lt _ (by decide)⟩

theorem I_pow_degreeResidue (k : ℕ) : Complex.I ^ k = root4 (degreeResidue k) := by
  rw [root4_eq_pow]
  change Complex.I ^ k = Complex.I ^ (k % 4)
  calc
    Complex.I ^ k = Complex.I ^ (k % 4 + 4 * (k / 4)) := by rw [Nat.mod_add_div]
    _ = Complex.I ^ (k % 4) * (Complex.I ^ 4) ^ (k / 4) := by rw [pow_add, pow_mul]
    _ = Complex.I ^ (k % 4) := by norm_num [pow_succ]

theorem degreeClock_wedgeWord (vs : List V) :
    degreeClock (wedgeWord vs) = root4 (degreeResidue vs.length) • wedgeWord vs := by
  change phaseMap Complex.I (wedgeWord vs) = _
  rw [phaseMap_wedgeWord, I_pow_degreeResidue]

/-- The requested degree-mod-four selection is valid for this clock. -/
theorem degreeProjector_wedgeWord (k : Fin 4) (vs : List V) :
    degreeProjector k (wedgeWord vs) =
      if k = degreeResidue vs.length then wedgeWord vs else 0 := by
  exact projector_on_eigenvector degreeClock k (degreeResidue vs.length)
    (wedgeWord vs) (degreeClock_wedgeWord vs)

theorem degreeProjector_idempotent (k : Fin 4) :
    degreeProjector (V := V) k * degreeProjector k = degreeProjector k :=
  projector_idempotent degreeClock degreeClock_fourth k

theorem degreeProjector_orthogonal (k l : Fin 4) (hkl : k ≠ l) :
    degreeProjector (V := V) k * degreeProjector l = 0 :=
  projector_orthogonal degreeClock degreeClock_fourth k l hkl

theorem degreeProjector_complete : (∑ k, degreeProjector (V := V) k) = 1 :=
  projector_sum degreeClock

@[simp] theorem degreeClock_one : degreeClock (V := V) 1 = 1 := by
  change phaseMap Complex.I 1 = 1
  exact map_one _

/-- The phase at -1 is precisely the pre-existing exterior parity operator. -/
theorem phaseMap_neg_one : phaseMap (V := V) (-1) =
    InfoGeometry.Canonical.ExteriorSpinorChiralityBridge.gradeInvolution := by
  apply ExteriorAlgebra.hom_ext
  ext v
  change phaseMap (-1) (ExteriorAlgebra.ι ℂ v) =
    InfoGeometry.Canonical.ExteriorSpinorChiralityBridge.gradeInvolution
      (ExteriorAlgebra.ι ℂ v)
  simp only [phaseMap_iota, neg_one_smul,
    InfoGeometry.Canonical.ExteriorSpinorChiralityBridge.gradeInvolution_ι]

/-- Exact compatibility with the existing chirality, not a parallel definition. -/
theorem degreeClock_square_eq_existing_parity : degreeClock (V := V) ^ 2 =
    (InfoGeometry.Canonical.ExteriorSpinorChiralityBridge.gradeInvolution
      (R := ℂ) (V := V)).toLinearMap := by
  rw [degreeClock, phaseEnd_pow, Complex.I_sq]
  change (phaseMap (-1)).toLinearMap = _
  rw [phaseMap_neg_one]

/-- Unlike a square-minus-one volume action, the degree clock fixes scalars. -/
theorem degreeClock_square_ne_neg_one : degreeClock (V := V) ^ 2 ≠ -1 := by
  intro h
  have h1 := congrArg (fun T : Module.End ℂ (ExteriorAlgebra ℂ V) => T 1) h
  simp only [pow_two, Module.End.mul_apply, degreeClock_one,
    LinearMap.neg_apply, Module.End.one_apply] at h1
  have hc := congrArg
    (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℂ V →ₐ[ℂ] ℂ) h1
  norm_num at hc

/-- Exterior nilpotency is why the generator scaling above is multiplicative.
For a general Clifford vector, multiplication of two scaled vectors changes
its square by a minus sign. -/
theorem imaginary_scaling_square {A : Type*} [Ring A] [Algebra ℂ A] (v : A) :
    (Complex.I • v) * (Complex.I • v) = -(v * v) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num

end InfoGeometry.Clifford.ExteriorDegreeFourierClock

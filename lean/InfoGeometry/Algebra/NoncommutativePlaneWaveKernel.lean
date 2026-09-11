import Mathlib.Algebra.MonoidAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite noncommutative plane-wave kernel

The algebraic core of the noncommutative Fourier construction is the plane-wave
law `E_g ⋆ E_h = E_(g h)`.  The native monoid algebra realizes this law with
no analytic or Hilbert-space assumptions: `MonoidAlgebra.single g 1` is the
plane wave attached to `g`.

This owner formalizes only the finite algebraic kernel.  It does not claim a
Haar integral, an `L²` theory, or a Plancherel theorem.
-/

namespace InfoGeometry.Algebra.NoncommutativePlaneWaveKernel

variable {R G : Type*} [Semiring R] [Group G]

noncomputable section

def planeWave (g : G) : MonoidAlgebra R G :=
  MonoidAlgebra.single g 1

theorem planeWave_one : planeWave (R := R) (1 : G) = 1 := by
  rw [planeWave, MonoidAlgebra.one_def]

theorem planeWave_mul (g h : G) :
    planeWave (R := R) (g * h) =
      planeWave (R := R) g * planeWave (R := R) h := by
  rw [planeWave, planeWave, planeWave, MonoidAlgebra.single_mul_single]
  simp

def planeWaveRepresentation : G →* MonoidAlgebra R G where
  toFun := planeWave (R := R)
  map_one' := planeWave_one (R := R)
  map_mul' g h := planeWave_mul (R := R) g h

theorem planeWaveRepresentation_apply (g : G) :
    planeWaveRepresentation (R := R) g = planeWave (R := R) g :=
  rfl

theorem planeWave_injective [Nontrivial R] :
    Function.Injective (planeWave (R := R) : G → MonoidAlgebra R G) := by
  intro g h e
  apply Finsupp.single_left_injective (one_ne_zero : (1 : R) ≠ 0)
  simpa [planeWave] using e

theorem planeWaveRepresentation_injective [Nontrivial R] :
    Function.Injective (planeWaveRepresentation (R := R) (G := G)) := by
  intro g h e
  apply planeWave_injective (R := R)
  simpa only [planeWaveRepresentation_apply] using e

theorem planeWave_representation_law (g h : G) :
    planeWaveRepresentation (R := R) (g * h) =
      planeWaveRepresentation (R := R) g *
        planeWaveRepresentation (R := R) h := by
  exact (planeWaveRepresentation (R := R)).map_mul g h

theorem planeWave_representation_identity :
    planeWaveRepresentation (R := R) (1 : G) = 1 := by
  exact (planeWaveRepresentation (R := R)).map_one

/-! ### Finite coefficient transform -/

variable [Fintype G] [DecidableEq G]

def finitePlaneWaveTransform : (G → R) →ₗ[R] MonoidAlgebra R G where
  toFun f := ∑ g : G, f g • planeWave (R := R) g
  map_add' f h := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]
    congr 1

theorem finitePlaneWaveTransform_apply (f : G → R) :
    finitePlaneWaveTransform (R := R) f =
      ∑ g : G, f g • planeWave (R := R) g :=
  rfl

theorem finitePlaneWaveTransform_pointMass (g : G) (c : R) :
    finitePlaneWaveTransform (R := R) (Pi.single g c) =
      c • planeWave (R := R) g := by
  rw [finitePlaneWaveTransform_apply]
  rw [Fintype.sum_eq_single g]
  · simp [planeWave]
  · intro b hb
    simp [Pi.single_apply, hb]

theorem finitePlaneWaveTransform_coeff (f : G → R) (k : G) :
    finitePlaneWaveTransform (R := R) f k = f k := by
  classical
  rw [finitePlaneWaveTransform_apply]
  have hterm (g : G) :
      f g • planeWave (R := R) g = Finsupp.single g (f g) := by
    rw [planeWave, MonoidAlgebra.single, Finsupp.smul_single]
    simp
  calc
    (∑ g : G, f g • planeWave (R := R) g) k =
        (∑ g : G, Finsupp.single g (f g)) k := by
      exact congrArg (fun x : MonoidAlgebra R G => x k)
        (Finset.sum_congr rfl (fun g hg => hterm g))
    _ = f k := by
      have h := congrArg (fun x : MonoidAlgebra R G => x k)
        (Finsupp.equivFunOnFinite_symm_eq_sum f)
      simpa using h.symm

def finiteConvolution (f h : G → R) (k : G) : R :=
  ∑ g : G, f g * h (g⁻¹ * k)

theorem finitePlaneWaveTransform_mul_convolution (f h : G → R) :
    finitePlaneWaveTransform (R := R) (fun k => finiteConvolution f h k) =
      finitePlaneWaveTransform (R := R) f *
        finitePlaneWaveTransform (R := R) h := by
  ext k
  rw [MonoidAlgebra.mul_apply_left]
  rw [Finsupp.sum_fintype]
  · simp [finiteConvolution, finitePlaneWaveTransform_coeff]
  · intro g
    simp

/-! ### Finite Haar-sum invariance -/

def finiteHaarSum (f : G → R) : R :=
  ∑ g : G, f g

theorem finiteHaarSum_left_translate (a : G) (f : G → R) :
    finiteHaarSum (fun g => f (a * g)) = finiteHaarSum f := by
  unfold finiteHaarSum
  simpa using (Equiv.sum_comp (Equiv.mulLeft a) f)

theorem finiteHaarSum_right_translate (a : G) (f : G → R) :
    finiteHaarSum (fun g => f (g * a)) = finiteHaarSum f := by
  unfold finiteHaarSum
  simpa using (Equiv.sum_comp (Equiv.mulRight a) f)

end

end InfoGeometry.Algebra.NoncommutativePlaneWaveKernel

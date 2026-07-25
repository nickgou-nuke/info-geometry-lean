import Mathlib.Tactic
import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Quantum.Monodromy

/-!
# ModularMonodromyClock

A small, fully checkable bridge between:
1. topological de Rham winding around the forbidden light cone (implemented in
   `KleinQuadricMonodromy`), and
2. a square-zero generator matrix whose modular flow is parabolic/unipotent.

This file avoids placeholders. Any statement about a nilpotent generator is made
with an explicit algebraic hypothesis.
-/

noncomputable section

namespace InfoGeometry.Projective.ParabolicTimeMonodromy

open Complex Matrix
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

variable {A : Type*} [Ring A]

-- A concrete null-cone-like 2×2 generator used in the capstone examples.
def modularGenerator (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a * b, -a ^ 2; b ^ 2, -a * b]

theorem modularGenerator_nilpotent (a b : ℂ) :
    (modularGenerator a b) ^ 2 = 0 := by
  rw [pow_two]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    (simp [modularGenerator, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, mul_assoc,
      add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm]; try ring_nf)

-- Inner derivation by left-right commutator of `K`.
def modularDerivation (K : A) : A → A :=
  fun X => K * X - X * K

/--
The residue operator that carries the topological `de Rham` circle data to algebra.
-/
structure DeRhamResidue (A : Type*) [Ring A] where
  Res : A → A
  isParabolic : ∀ X : A, Res (Res X) = 0

/--
Dictionary field for the Rosetta correspondence in this repo:
`de Rham` residue is (postulated) to be identified with a modular commutator
generator, and that generator is required to be square-zero.
-/
structure MonodromyModularDictionary (A : Type*) [Ring A] where
  residue : DeRhamResidue A
  timeGenerator : A
  mapResidueToDerivation : DeRhamResidue A → A → A
  timeIsResidue :
    mapResidueToDerivation residue = modularDerivation timeGenerator
  modularGeneratorSquareZero : timeGenerator * timeGenerator = 0

/--
With explicit dictionary data, the modular generator is concretely square-zero.
-/
theorem parabolic_time_clock (dict : MonodromyModularDictionary A) :
    ∃ K : A, K * K = 0 := by
  refine ⟨dict.timeGenerator, dict.modularGeneratorSquareZero⟩

/--
Parabolic/unipotent flow on the concrete nilpotent cone model:
`U(t) = I + tK`, so `det = 1` and `trace = 2`.
-/
noncomputable def nullConeFlow (a b t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) + t • modularGenerator a b


theorem nullConeFlow_trace (a b t : ℂ) :
    (nullConeFlow a b t).trace = 2 := by
  simp [nullConeFlow, modularGenerator, Matrix.trace_fin_two]


theorem nullConeFlow_det (a b t : ℂ) :
    (nullConeFlow a b t).det = 1 := by
  simp [nullConeFlow, modularGenerator, Matrix.det_fin_two]
  ring

/--
`modularGenerator` is trace-zero and the flow is therefore parabolic.
-/
theorem nullConeFlow_parabolic (a b t : ℂ) :
    (nullConeFlow a b t).det = 1 ∧ (nullConeFlow a b t).trace = 2 := by
  constructor
  · exact nullConeFlow_det a b t
  · exact nullConeFlow_trace a b t

/--
Unipotent power law: the `n`-fold monodromy clock step is affine in `n` on a
square-zero generator.
-/
 theorem parabolic_winding_power_law (a b t : ℂ) (n : ℕ) :
    (nullConeFlow a b t) ^ n =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (n : ℕ) • (t • modularGenerator a b) := by
  have hNil : (t • modularGenerator a b) * (t • modularGenerator a b) = 0 := by
    have hK2 : (modularGenerator a b) * (modularGenerator a b) = (0 : _ ) :=
      by
        simpa [pow_two] using (modularGenerator_nilpotent (a := a) (b := b))
    -- `smul_mul_assoc` / `mul_smul` reduce this to `(t*t) • (K*K)`.
    calc
      (t • modularGenerator a b) * (t • modularGenerator a b)
          = t • ((modularGenerator a b) * (t • modularGenerator a b)) := by
              simpa using
                (Matrix.smul_mul (M := (modularGenerator a b)) (N := (modularGenerator a b)) (a := t))
      _ = t • (t • ((modularGenerator a b) * (modularGenerator a b))) := by
          simp [Matrix.mul_smul]
      _ = (t * t) • ((modularGenerator a b) * (modularGenerator a b)) := by
          simp [smul_smul]
      _ = (t * t) • (0 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [hK2]
      _ = 0 := by simp
  -- apply the existing monodromy power law with `lambda = 1` and square-zero `t•K`.
  simpa [nullConeFlow, one_mul] using
    (InfoGeometry.QuantumMonodromy.monodromy_winding_formula
      (lambda := (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (epsilon := (t • modularGenerator a b)) hNil (by simp) n)

/--
Purely topological monodromy residue around the forbidden cone produces a `2πi`
winding class. Composing with `Complex.exp` gives unit holonomy.
-/
theorem deRham_winding_phase (R : ℝ) (hR : 0 < R) (n : ℤ) :
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), (1 : ℂ) / z)) = (1 : ℂ) := by
  change Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)) = 1
  rw [circleIntegral_one_div R hR]
  simpa using (Complex.exp_int_mul_two_pi_mul_I n)

end InfoGeometry.Projective.ParabolicTimeMonodromy

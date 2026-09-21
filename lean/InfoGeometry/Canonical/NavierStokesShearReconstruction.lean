import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Spatial shear reconstruction for the incompressible Navier–Stokes equation

Coordinate derivatives below are actual native `deriv`s along coordinate
lines in R³. The shear reduction computes every term of the pointwise PDE;
no equation or reconstruction law is stored as a structure field.

This local coordinate interface does not include the global smoothness,
finite-energy, initial-data or forcing conditions of the Clay alternatives.
-/

noncomputable section

namespace InfoGeometry.Canonical.NavierStokesShearReconstruction

abbrev Space := Fin 3 → ℝ
abbrev Velocity := ℝ → Space → Space

/-- Native partial derivative, with other coordinates held fixed. -/
def coordDeriv (i : Fin 3) (f : Space → ℝ) (x : Space) : ℝ :=
  deriv (fun r => f (Function.update x i r)) (x i)

def divergence (v : Space → Space) (x : Space) : ℝ :=
  ∑ i, coordDeriv i (fun y => v y i) x

def curl (v : Space → Space) (x : Space) : Space :=
  ![coordDeriv 1 (fun y => v y 2) x - coordDeriv 2 (fun y => v y 1) x,
    coordDeriv 2 (fun y => v y 0) x - coordDeriv 0 (fun y => v y 2) x,
    coordDeriv 0 (fun y => v y 1) x - coordDeriv 1 (fun y => v y 0) x]

def laplacian (f : Space → ℝ) (x : Space) : ℝ :=
  ∑ j, coordDeriv j (coordDeriv j f) x

def advection (v : Space → Space) (x : Space) (i : Fin 3) : ℝ :=
  ∑ j, v x j * coordDeriv j (fun y => v y i) x

/-- The actual componentwise equation and incompressibility at `(t,x)`. -/
def SatisfiesAt (ν : ℝ) (u : Velocity) (p : ℝ → Space → ℝ)
    (f : Velocity) (t : ℝ) (x : Space) : Prop :=
  divergence (u t) x = 0 ∧ ∀ i,
    deriv (fun s => u s x i) t + advection (u t) x i =
      ν * laplacian (fun y => u t y i) x - coordDeriv i (p t) x + f t x i

def shear (a : ℝ → ℝ → ℝ) : Velocity := fun t x => ![0, a t (x 0), 0]

/-- Agreement with the native Fréchet derivative on the coordinate vector. -/
theorem coordDeriv_eq_fderiv {f : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    coordDeriv i f x = fderiv ℝ f x (Pi.single i 1) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa [coordDeriv] using h.deriv

@[simp] theorem partial_const (i : Fin 3) (c : ℝ) (x : Space) :
    coordDeriv i (fun _ => c) x = 0 := by simp [coordDeriv]

theorem partial_first (i : Fin 3) (a : ℝ → ℝ) (x : Space) :
    coordDeriv i (fun y => a (y 0)) x = if i = 0 then deriv a (x 0) else 0 := by
  fin_cases i <;> simp [coordDeriv]

theorem coordDeriv_const_fun (i : Fin 3) (c : ℝ) :
    coordDeriv i (fun _ => c) = (fun _ => 0) := funext (partial_const i c)

theorem coordDeriv_first_fun (i : Fin 3) (a : ℝ → ℝ) :
    coordDeriv i (fun y => a (y 0)) =
      (fun x => if i = 0 then deriv a (x 0) else 0) := funext (partial_first i a)

@[simp] theorem divergence_shear (a : ℝ → ℝ → ℝ) (t : ℝ) (x : Space) :
    divergence (shear a t) x = 0 := by
  simp [divergence, shear, Fin.sum_univ_succ, partial_first]

theorem curl_shear (a : ℝ → ℝ → ℝ) (t : ℝ) (x : Space) :
    curl (shear a t) x = ![0, 0, deriv (a t) (x 0)] := by
  simp [curl, shear, partial_first]

@[simp] theorem laplacian_const (c : ℝ) (x : Space) :
    laplacian (fun _ => c) x = 0 := by simp [laplacian, coordDeriv_const_fun]

theorem laplacian_first (a : ℝ → ℝ) (x : Space) :
    laplacian (fun y => a (y 0)) x = deriv (deriv a) (x 0) := by
  simp [laplacian, Fin.sum_univ_succ, coordDeriv_first_fun, partial_first]

@[simp] theorem advection_shear (a : ℝ → ℝ → ℝ) (t : ℝ) (x : Space)
    (i : Fin 3) : advection (shear a t) x i = 0 := by
  fin_cases i <;> simp [advection, shear, partial_first]

/-- All three PDE components reduce to the scalar forced heat equation. -/
theorem satisfiesAt_shear_iff (ν : ℝ) (a b : ℝ → ℝ → ℝ) (t : ℝ) (x : Space) :
    SatisfiesAt ν (shear a) (fun _ _ => 0) (shear b) t x ↔
      deriv (fun s => a s (x 0)) t = ν * deriv (deriv (a t)) (x 0) + b t (x 0) := by
  simp only [SatisfiesAt, divergence_shear, true_and, advection_shear, add_zero,
    partial_const, sub_zero]
  constructor
  · intro h
    simpa [shear, laplacian_first] using h 1
  · intro h i
    fin_cases i <;> simp [shear, laplacian_first, h]

/-- For any twice spatially differentiable profile this is the usual residual
forcing; the identity itself also respects Lean's totalized derivatives. -/
theorem shear_with_residual_forcing (ν : ℝ) (a : ℝ → ℝ → ℝ) (t : ℝ) (x : Space) :
    SatisfiesAt ν (shear a) (fun _ _ => 0)
      (shear (fun s r => deriv (fun q => a q r) s - ν * deriv (deriv (a s)) r)) t x := by
  rw [satisfiesAt_shear_iff]
  ring

end InfoGeometry.Canonical.NavierStokesShearReconstruction

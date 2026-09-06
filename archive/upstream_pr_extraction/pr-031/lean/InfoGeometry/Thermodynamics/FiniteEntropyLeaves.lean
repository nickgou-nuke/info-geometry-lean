import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

noncomputable section

namespace InfoGeometry.Thermodynamics.FiniteEntropyLeaves

def entropyLeaf {X R : Type*} (S : X → R) (c : R) : Set X :=
  {x | S x = c}

theorem mem_entropyLeaf_iff
    {X R : Type*} {S : X → R} {c : R} {x : X} :
    x ∈ entropyLeaf S c ↔ S x = c :=
  Iff.rfl

theorem entropy_preserving_maps_leaf
    {X R : Type*}
    (S : X → R) (f : X → X)
    (hf : ∀ x, S (f x) = S x)
    (c : R) :
    Set.MapsTo f (entropyLeaf S c) (entropyLeaf S c) := by
  intro x hx
  exact (hf x).trans hx

theorem entropy_preserving_comp
    {X R : Type*}
    (S : X → R) (f g : X → X)
    (hf : ∀ x, S (f x) = S x)
    (hg : ∀ x, S (g x) = S x) :
    ∀ x, S ((f ∘ g) x) = S x := by
  intro x
  rw [Function.comp_apply, hf, hg]

theorem entropy_preserving_iterate
    {X R : Type*}
    (S : X → R) (f : X → X)
    (hf : ∀ x, S (f x) = S x) :
    ∀ k x, S (f^[k] x) = S x := by
  intro k
  induction k with
  | zero =>
      intro x
      rfl
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply, ih, hf]

def conjugate
    {n R : Type*} [Fintype n] [Semiring R]
    (U V A : Matrix n n R) : Matrix n n R :=
  U * A * V

theorem trace_conjugate
    {n R : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R]
    (U V A : Matrix n n R)
    (hVU : V * U = 1) :
    Matrix.trace (conjugate U V A) = Matrix.trace A := by
  calc
    Matrix.trace (conjugate U V A) = Matrix.trace (V * (U * A)) := by
      simpa [conjugate] using Matrix.trace_mul_comm (U * A) V
    _ = Matrix.trace ((V * U) * A) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace A := by simp [hVU]

theorem conjugate_maps_trace_leaf
    {n R : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R]
    (U V : Matrix n n R)
    (hVU : V * U = 1)
    (c : R) :
    Set.MapsTo (conjugate U V)
      (entropyLeaf Matrix.trace c)
      (entropyLeaf Matrix.trace c) := by
  intro A hA
  exact (trace_conjugate U V A hVU).trans hA

def uniformRelativeWeight (W : ℝ) : ℝ :=
  W⁻¹

def uniformSurprisal (W : ℝ) : ℝ :=
  -Real.log (uniformRelativeWeight W)

theorem uniformSurprisal_eq_log (W : ℝ) :
    uniformSurprisal W = Real.log W := by
  rw [uniformSurprisal, uniformRelativeWeight, Real.log_inv, neg_neg]

def boltzmannEntropy (kB W : ℝ) : ℝ :=
  kB * Real.log W

theorem boltzmannEntropy_eq_scaled_uniformSurprisal (kB W : ℝ) :
    boltzmannEntropy kB W = kB * uniformSurprisal W := by
  rw [boltzmannEntropy, uniformSurprisal_eq_log]

def boltzmannSurprisalOperator
    {n : Type*} [Fintype n] [DecidableEq n]
    (kB W : ℝ) : Matrix n n ℝ :=
  boltzmannEntropy kB W • 1

theorem boltzmannSurprisalOperator_mulVec
    {n : Type*} [Fintype n] [DecidableEq n]
    (kB W : ℝ) (v : n → ℝ) :
    boltzmannSurprisalOperator kB W *ᵥ v =
      boltzmannEntropy kB W • v := by
  simp [boltzmannSurprisalOperator, Matrix.smul_mulVec]

theorem boltzmannSurprisalOperator_eigenvector
    {n : Type*} [Fintype n] [DecidableEq n]
    (kB W : ℝ) (v : n → ℝ) :
    boltzmannSurprisalOperator kB W *ᵥ v =
      (kB * Real.log W) • v := by
  rw [boltzmannSurprisalOperator_mulVec, boltzmannEntropy]

end InfoGeometry.Thermodynamics.FiniteEntropyLeaves

import Mathlib
import InfoGeometry.Topology.EckmannDiscreteHodge

/-!
# Discrete Dirac--Hodge Chiral Calculus

Finite, theorem-safe algebraic surface for a discrete exterior derivative `d`,
its codifferential `δ`, the Dirac--Hodge operator `D = d + δ`, and a chirality
operator `γ` on a finite-dimensional cochain carrier.

This file does not construct a simplicial complex from a graph, prove analytic
Hodge decomposition, or identify Betti numbers.  It proves the finite algebraic
identities used by those owner layers:

* if `d² = 0` and `δ² = 0`, then `(d+δ)² = dδ + δd`;
* if `γ` anticommutes with both `d` and `δ`, then it anticommutes with `D`;
* exact/coexact/harmonic sectors are explicit finite predicates;
* degree-one Eckmann harmonicity is re-exported as the concrete graph/simplicial
  readback already owned by `EckmannDiscreteHodge`.
-/

namespace DiscreteDiracHodgeChiral

open Matrix
open InfoGeometry.Topology.EckmannDiscreteHodge

noncomputable section

universe u

variable {n : ℕ}

/-- Finite cochain carrier. -/
abbrev Cochains (n : ℕ) := Fin n → ℝ

/-- Finite endomorphism of the total cochain space. -/
abbrev EndCochain (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Discrete Dirac--Hodge operator `D = d + δ`. -/
def diracHodge (d δ : EndCochain n) : EndCochain n :=
  d + δ

/-- Hodge Laplacian `L = dδ + δd`. -/
def hodgeLaplacian (d δ : EndCochain n) : EndCochain n :=
  d * δ + δ * d

/-- Chirality anticommutator `{A,γ}=Aγ+γA`. -/
def anticommutator (A γ : EndCochain n) : EndCochain n :=
  A * γ + γ * A

/-- Exact finite cochains: image of `d`. -/
def IsExact (d : EndCochain n) (x : Cochains n) : Prop :=
  ∃ y : Cochains n, d.mulVec y = x

/-- Coexact finite cochains: image of `δ`. -/
def IsCoexact (δ : EndCochain n) (x : Cochains n) : Prop :=
  ∃ y : Cochains n, δ.mulVec y = x

/-- Dirac-harmonic finite cochains: kernel of `D`. -/
def IsDiracHarmonic (d δ : EndCochain n) (x : Cochains n) : Prop :=
  (diracHodge d δ).mulVec x = 0

/-- Laplace-harmonic finite cochains: kernel of `L`. -/
def IsLaplaceHarmonic (d δ : EndCochain n) (x : Cochains n) : Prop :=
  (hodgeLaplacian d δ).mulVec x = 0

/-- Nilpotence of `d` and `δ` makes the Dirac square equal the Hodge Laplacian. -/
theorem diracHodge_sq_eq_hodgeLaplacian
    (d δ : EndCochain n)
    (hd : d * d = 0)
    (hδ : δ * δ = 0) :
    diracHodge d δ * diracHodge d δ = hodgeLaplacian d δ := by
  unfold diracHodge hodgeLaplacian
  rw [add_mul, mul_add, mul_add, hd, hδ]
  ext i j
  simp

/-- The Dirac square annihilates every Dirac-harmonic cochain. -/
theorem diracHarmonic_sq_zero
    (d δ : EndCochain n) {x : Cochains n}
    (hx : IsDiracHarmonic d δ x) :
    (diracHodge d δ * diracHodge d δ).mulVec x = 0 := by
  have h := congrArg ((diracHodge d δ).mulVec) hx
  simpa [Matrix.mulVec_mulVec] using h

/-- Under nilpotence, Dirac-harmonic cochains are Laplace-harmonic. -/
theorem diracHarmonic_is_laplaceHarmonic
    (d δ : EndCochain n)
    (hd : d * d = 0)
    (hδ : δ * δ = 0)
    {x : Cochains n}
    (hx : IsDiracHarmonic d δ x) :
    IsLaplaceHarmonic d δ x := by
  unfold IsLaplaceHarmonic
  rw [← diracHodge_sq_eq_hodgeLaplacian d δ hd hδ]
  exact diracHarmonic_sq_zero d δ hx

/-- If chirality anticommutes with `d` and `δ`, then it anticommutes with `D=d+δ`. -/
theorem chirality_anticommutes_diracHodge
    (d δ γ : EndCochain n)
    (hdγ : anticommutator d γ = 0)
    (hδγ : anticommutator δ γ = 0) :
    anticommutator (diracHodge d δ) γ = 0 := by
  unfold anticommutator diracHodge at *
  have hd' : d * γ = -(γ * d) := eq_neg_of_add_eq_zero_left hdγ
  have hδ' : δ * γ = -(γ * δ) := eq_neg_of_add_eq_zero_left hδγ
  rw [add_mul, mul_add, hd', hδ']
  abel

/-- Chirality anticommutes with the Dirac action on every finite cochain. -/
theorem chirality_anticommutes_diracHodge_apply
    (d δ γ : EndCochain n)
    (hDγ : anticommutator (diracHodge d δ) γ = 0)
    (x : Cochains n) :
    (diracHodge d δ).mulVec (γ.mulVec x) = - γ.mulVec ((diracHodge d δ).mulVec x) := by
  have hmat : diracHodge d δ * γ = -(γ * diracHodge d δ) := by
    unfold anticommutator at hDγ
    exact eq_neg_of_add_eq_zero_left hDγ
  calc
    (diracHodge d δ).mulVec (γ.mulVec x)
        = (diracHodge d δ * γ).mulVec x := by
          rw [Matrix.mulVec_mulVec]
    _ = (-(γ * diracHodge d δ)).mulVec x := by
          rw [hmat]
    _ = -γ.mulVec ((diracHodge d δ).mulVec x) := by
          ext i
          simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]

/-! ## Degree-one graph/simplicial Hodge adapter -/

/-- Degree-one exact forms in the Eckmann owner are coboundaries `d₀ u`. -/
def EckmannExact1 {n0 n1 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ) (x : Fin n1 → ℝ) : Prop :=
  ∃ u : Fin n0 → ℝ, d0.mulVec u = x

/-- Degree-one coexact forms in the Eckmann owner are adjoint coboundaries `d₁ᵀ v`. -/
def EckmannCoexact1 {n1 n2 : ℕ}
    (d1 : Matrix (Fin n2) (Fin n1) ℝ) (x : Fin n1 → ℝ) : Prop :=
  ∃ v : Fin n2 → ℝ, d1.transpose.mulVec v = x

/-- Exact and coexact degree-one components are orthogonal when `d₁ d₀ = 0`. -/
theorem eckmann_exact_orthogonal_coexact {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : eckmannDegreeOneCochainComplex d0 d1)
    {x y : Fin n1 → ℝ}
    (hx : EckmannExact1 d0 x)
    (hy : EckmannCoexact1 d1 y) :
    eckmannDot x y = 0 := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  exact eckmann_coboundary_orthogonal_coexact d0 d1 hComplex u v

/-- Exact cochains are explicit images. -/
theorem exact_readout (d : EndCochain n) (x : Cochains n)
    (h : IsExact d x) : ∃ y : Cochains n, d.mulVec y = x := h

/-- Coexact cochains are explicit images. -/
theorem coexact_readout (δ : EndCochain n) (x : Cochains n)
    (h : IsCoexact δ x) : ∃ y : Cochains n, δ.mulVec y = x := h

/-- The degree-one Eckmann Laplacian expands to `d₁ᵀ d₁ + d₀ d₀ᵀ`. -/
theorem eckmann_degree_one_laplacian_readout {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ) :
    eckmannLaplacian1 d0 d1 = d1.transpose * d1 + d0 * d0.transpose :=
  rfl

/-- Degree-one harmonicity is the conjunction of closedness and coclosedness. -/
theorem eckmann_harmonic1_readout {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    eckmannHarmonic1 d0 d1 x ↔ d1.mulVec x = 0 ∧ d0.transpose.mulVec x = 0 :=
  Iff.rfl

end

end DiscreteDiracHodgeChiral

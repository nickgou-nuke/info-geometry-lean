/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Finite-rank algebra behind gerbe-twisted curvature

This file formalizes algebraic identities motivated by Córdova–Freed–Teleman,
*Gapped theories have torsion anomalies*, arXiv:2408.15148.  It does not model
differential cohomology or infer a global anomaly class from a matrix identity.
The coefficient ring is allowed to be noncommutative throughout.
-/

namespace InfoGeometry.OperatorAlgebra.GerbeTwistedCurvatureTorsion

section CechDefect

variable {G : Type*} [Group G]

def conjugate (g x : G) : G := g * x * g⁻¹

/-- The transition defect `ψᵢⱼ ψⱼₖ ψᵢₖ⁻¹`. -/
def gerbeDefect (ψᵢⱼ ψⱼₖ ψᵢₖ : G) : G := ψᵢⱼ * ψⱼₖ * ψᵢₖ⁻¹

theorem transition_composition (ψᵢⱼ ψⱼₖ ψᵢₖ : G) :
    ψᵢⱼ * ψⱼₖ = gerbeDefect ψᵢⱼ ψⱼₖ ψᵢₖ * ψᵢₖ := by
  simp [gerbeDefect]

/-- Associativity gives the tetrahedral coherence identity, with the indicated
conjugation action. No commutativity of `G` is assumed. -/
theorem gerbeDefect_tetrahedral
    (ψᵢⱼ ψⱼₖ ψₖₗ ψᵢₖ ψⱼₗ ψᵢₗ : G) :
    gerbeDefect ψᵢⱼ ψⱼₖ ψᵢₖ * gerbeDefect ψᵢₖ ψₖₗ ψᵢₗ =
      conjugate ψᵢⱼ (gerbeDefect ψⱼₖ ψₖₗ ψⱼₗ) *
        gerbeDefect ψᵢⱼ ψⱼₗ ψᵢₗ := by
  simp [gerbeDefect, conjugate]
  group

end CechDefect

section DerivationAndCurvature

variable {R : Type*} [Ring R]

/-- An additive map satisfying the Leibniz rule on the given associative ring. -/
def IsRingDerivation (d : R →+ R) : Prop :=
  ∀ x y, d (x * y) = d x * y + x * d y

def curvature (d₁ d₂ : R →+ R) (A₁ A₂ : R) : R :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

def covariantDerivative (d : R →+ R) (A ψ : R) : R := d ψ + A * ψ

def gaugeConnection (d : R →+ R) (u : Rˣ) (A : R) : R :=
  (u : R) * A * (↑u⁻¹ : R) - d (u : R) * (↑u⁻¹ : R)

theorem IsRingDerivation.map_one {d : R →+ R}
    (hd : IsRingDerivation d) : d 1 = 0 := by
  have h : d 1 = d 1 + d 1 := by simpa only [mul_one, one_mul] using hd 1 1
  have h' : d 1 + d 1 = d 1 + 0 := by simpa using h.symm
  exact add_left_cancel h'

theorem covariant_curvature_multiplication
    {d₁ d₂ : R →+ R} (hd₁ : IsRingDerivation d₁)
    (hd₂ : IsRingDerivation d₂)
    (hcomm : ∀ x, d₁ (d₂ x) = d₂ (d₁ x)) (A₁ A₂ ψ : R) :
    covariantDerivative d₁ A₁ (covariantDerivative d₂ A₂ ψ) -
      covariantDerivative d₂ A₂ (covariantDerivative d₁ A₁ ψ) =
      curvature d₁ d₂ A₁ A₂ * ψ := by
  dsimp [covariantDerivative, curvature]
  rw [Ring.lie_def, map_add, map_add, hd₁ A₂ ψ, hd₂ A₁ ψ, hcomm ψ]
  noncomm_ring

theorem covariant_gauge_intertwining {d : R →+ R}
    (hd : IsRingDerivation d) (u : Rˣ) (A ψ : R) :
    covariantDerivative d (gaugeConnection d u A) ((u : R) * ψ) =
      (u : R) * covariantDerivative d A ψ := by
  dsimp [covariantDerivative, gaugeConnection]
  rw [hd (u : R) ψ]
  have hu : (↑u⁻¹ : R) * (u : R) = 1 := Units.inv_mul u
  calc
    d (u : R) * ψ + (u : R) * d ψ +
        ((u : R) * A * (↑u⁻¹ : R) - d (u : R) * (↑u⁻¹ : R)) *
          ((u : R) * ψ)
      = d (u : R) * ψ + (u : R) * d ψ +
          (u : R) * A * ((↑u⁻¹ : R) * (u : R)) * ψ -
            d (u : R) * ((↑u⁻¹ : R) * (u : R)) * ψ := by noncomm_ring
    _ = d (u : R) * ψ + (u : R) * d ψ +
          (u : R) * A * 1 * ψ - d (u : R) * 1 * ψ := by rw [hu]
    _ = (u : R) * (d ψ + A * ψ) := by noncomm_ring

theorem curvature_gauge_covariant
    {d₁ d₂ : R →+ R}
    (hd₁ : IsRingDerivation d₁) (hd₂ : IsRingDerivation d₂)
    (hcomm : ∀ x, d₁ (d₂ x) = d₂ (d₁ x)) (u : Rˣ) (A₁ A₂ : R) :
    curvature d₁ d₂ (gaugeConnection d₁ u A₁) (gaugeConnection d₂ u A₂) =
      (u : R) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : R) := by
  have hleft := covariant_curvature_multiplication hd₁ hd₂ hcomm
    (gaugeConnection d₁ u A₁) (gaugeConnection d₂ u A₂) ((u : R) * 1)
  rw [covariant_gauge_intertwining hd₂ u A₂ 1,
      covariant_gauge_intertwining hd₁ u A₁ (covariantDerivative d₂ A₂ 1),
      covariant_gauge_intertwining hd₁ u A₁ 1,
      covariant_gauge_intertwining hd₂ u A₂ (covariantDerivative d₁ A₁ 1)] at hleft
  have hright := covariant_curvature_multiplication hd₁ hd₂ hcomm A₁ A₂ 1
  have hmul : curvature d₁ d₂ (gaugeConnection d₁ u A₁)
      (gaugeConnection d₂ u A₂) * (u : R) =
      (u : R) * curvature d₁ d₂ A₁ A₂ := by
    calc
      _ = curvature d₁ d₂ (gaugeConnection d₁ u A₁)
          (gaugeConnection d₂ u A₂) * ((u : R) * 1) := by rw [mul_one]
      _ = (u : R) * covariantDerivative d₁ A₁ (covariantDerivative d₂ A₂ 1) -
          (u : R) * covariantDerivative d₂ A₂ (covariantDerivative d₁ A₁ 1) := hleft.symm
      _ = (u : R) * (covariantDerivative d₁ A₁ (covariantDerivative d₂ A₂ 1) -
          covariantDerivative d₂ A₂ (covariantDerivative d₁ A₁ 1)) := by noncomm_ring
      _ = (u : R) * (curvature d₁ d₂ A₁ A₂ * 1) := by rw [hright]
      _ = (u : R) * curvature d₁ d₂ A₁ A₂ := by rw [mul_one]
  calc
    _ = curvature d₁ d₂ (gaugeConnection d₁ u A₁)
          (gaugeConnection d₂ u A₂) * ((u : R) * (↑u⁻¹ : R)) := by
          rw [Units.mul_inv, mul_one]
    _ = (curvature d₁ d₂ (gaugeConnection d₁ u A₁)
          (gaugeConnection d₂ u A₂) * (u : R)) * (↑u⁻¹ : R) := by noncomm_ring
    _ = (u : R) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : R) := by rw [hmul]

/-- Entrywise lifting of a ring derivation to a finite square matrix ring. -/
def liftMatrixDerivation {A : Type*} [Ring A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (d : A →+ A) :
    Matrix ι ι A →+ Matrix ι ι A where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; exact map_add d (M i j) (N i j)

theorem liftMatrixDerivation_leibniz {A : Type*} [Ring A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {d : A →+ A}
    (hd : ∀ x y, d (x * y) = d x * y + x * d y)
    (M N : Matrix ι ι A) :
    liftMatrixDerivation d (M * N) =
      liftMatrixDerivation d M * N + M * liftMatrixDerivation d N := by
  ext i k
  change d (∑ j, M i j * N j k) =
    (∑ j, d (M i j) * N j k) + ∑ j, M i j * d (N j k)
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => hd (M i j) (N j k))

end DerivationAndCurvature

section TraceCurvature

variable {B : Type*} [Ring B]

def ncTrace {r : ℕ} (M : Matrix (Fin r) (Fin r) B) : B :=
  ∑ i : Fin r, M i i

def gerbeEmbed (r : ℕ) (b : B) : Matrix (Fin r) (Fin r) B :=
  Matrix.diagonal (fun _ => b)

def twistedCurvature {r : ℕ} (d₁ d₂ : B →+ B)
    (A₁ A₂ : Matrix (Fin r) (Fin r) B) (b : B) : Matrix (Fin r) (Fin r) B :=
  (liftMatrixDerivation d₁) A₂ - (liftMatrixDerivation d₂) A₁ + ⁅A₁, A₂⁆ +
    gerbeEmbed r b

theorem ncTrace_add {r : ℕ} (M N : Matrix (Fin r) (Fin r) B) :
    ncTrace (M + N) = ncTrace M + ncTrace N := by
  simp [ncTrace, Finset.sum_add_distrib]

theorem ncTrace_sub {r : ℕ} (M N : Matrix (Fin r) (Fin r) B) :
    ncTrace (M - N) = ncTrace M - ncTrace N := by
  simp [ncTrace, Finset.sum_sub_distrib]

theorem ncTrace_lift {r : ℕ} (d : B →+ B) (M : Matrix (Fin r) (Fin r) B) :
    ncTrace (liftMatrixDerivation d M) = d (ncTrace M) := by
  change (∑ i : Fin r, d (M i i)) = d (∑ i : Fin r, M i i)
  rw [map_sum]

theorem ncTrace_gerbeEmbed (r : ℕ) (b : B) :
    ncTrace (gerbeEmbed r b) = r • b := by
  simp [ncTrace, gerbeEmbed, Finset.sum_const, Fintype.card_fin]

/-- Trace-curvature identity over a noncommutative coefficient ring. The trace
of the matrix commutator is retained; it is not generally zero. -/
theorem ncTrace_twistedCurvature {r : ℕ} (d₁ d₂ : B →+ B)
    (A₁ A₂ : Matrix (Fin r) (Fin r) B) (b : B) :
    ncTrace (twistedCurvature d₁ d₂ A₁ A₂ b) =
      d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆ + r • b := by
  simp only [twistedCurvature, ncTrace_add, ncTrace_sub,
    ncTrace_lift, ncTrace_gerbeEmbed]

/-- Algebraic consequence of projective flatness: the rank multiple of the
curving is the negative trace of the matrix curvature. This is an equality in
`B`; a cohomological torsion statement needs additional geometric data. -/
theorem projectively_flat_trace_relation {r : ℕ} (d₁ d₂ : B →+ B)
    (A₁ A₂ : Matrix (Fin r) (Fin r) B) (b : B)
    (hflat : twistedCurvature d₁ d₂ A₁ A₂ b = 0) :
    r • b = -(d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) := by
  have h := congrArg ncTrace hflat
  have hz : ncTrace (0 : Matrix (Fin r) (Fin r) B) = 0 := by simp [ncTrace]
  rw [hz] at h
  rw [ncTrace_twistedCurvature] at h
  have h' : r • b + (d₁ (ncTrace A₂) - d₂ (ncTrace A₁) +
      ncTrace ⁅A₁, A₂⁆) = 0 := by rw [add_comm]; exact h
  calc
    r • b = r • b + (d₁ (ncTrace A₂) - d₂ (ncTrace A₁) +
        ncTrace ⁅A₁, A₂⁆) -
          (d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) := by abel
    _ = 0 - (d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) := by rw [h']
    _ = _ := by simp

end TraceCurvature

section GerbeFlatness

variable {R : Type*} [Ring R]

def adjointDerivative (d : R →+ R) (A X : R) : R := d X + ⁅A, X⁆

theorem differentialBianchi
    {d₁ d₂ d₃ : R →+ R}
    (hd₁ : IsRingDerivation d₁) (hd₂ : IsRingDerivation d₂)
    (hd₃ : IsRingDerivation d₃)
    (h12 : ∀ x, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x, d₁ (d₃ x) = d₃ (d₁ x)) (A₁ A₂ A₃ : R) :
    adjointDerivative d₁ A₁ (curvature d₂ d₃ A₂ A₃) +
      adjointDerivative d₂ A₂ (curvature d₃ d₁ A₃ A₁) +
      adjointDerivative d₃ A₃ (curvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjointDerivative, curvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
    h12 A₃, h13 A₂, h23 A₁]
  noncomm_ring

/-- Under centrality of each curving component, projective flatness and the
non-Abelian Bianchi identity imply the cyclic derivative identity for the
curving. -/
theorem projectiveFlat_implies_cyclicCurvingClosed
    {d₁ d₂ d₃ : R →+ R}
    (hd₁ : IsRingDerivation d₁) (hd₂ : IsRingDerivation d₂)
    (hd₃ : IsRingDerivation d₃)
    (h12 : ∀ x, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x, d₁ (d₃ x) = d₃ (d₁ x))
    {A₁ A₂ A₃ B₂₃ B₃₁ B₁₂ : R}
    (h23flat : curvature d₂ d₃ A₂ A₃ + B₂₃ = 0)
    (h31flat : curvature d₃ d₁ A₃ A₁ + B₃₁ = 0)
    (h12flat : curvature d₁ d₂ A₁ A₂ + B₁₂ = 0)
    (hcentral₁ : ⁅A₁, B₂₃⁆ = 0)
    (hcentral₂ : ⁅A₂, B₃₁⁆ = 0)
    (hcentral₃ : ⁅A₃, B₁₂⁆ = 0) :
    d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂ = 0 := by
  have hb := differentialBianchi hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  rw [eq_neg_of_add_eq_zero_left h23flat,
    eq_neg_of_add_eq_zero_left h31flat,
    eq_neg_of_add_eq_zero_left h12flat] at hb
  dsimp [adjointDerivative] at hb
  have hc₁ : A₁ * B₂₃ - B₂₃ * A₁ = 0 := by
    simpa only [Ring.lie_def] using hcentral₁
  have hc₂ : A₂ * B₃₁ - B₃₁ * A₂ = 0 := by
    simpa only [Ring.lie_def] using hcentral₂
  have hc₃ : A₃ * B₁₂ - B₁₂ * A₃ = 0 := by
    simpa only [Ring.lie_def] using hcentral₃
  have hneg₁ : A₁ * (-B₂₃) - (-B₂₃) * A₁ = 0 := by
    calc
      _ = -(A₁ * B₂₃ - B₂₃ * A₁) := by noncomm_ring
      _ = 0 := by rw [hc₁]; simp
  have hneg₂ : A₂ * (-B₃₁) - (-B₃₁) * A₂ = 0 := by
    calc
      _ = -(A₂ * B₃₁ - B₃₁ * A₂) := by noncomm_ring
      _ = 0 := by rw [hc₂]; simp
  have hneg₃ : A₃ * (-B₁₂) - (-B₁₂) * A₃ = 0 := by
    calc
      _ = -(A₃ * B₁₂ - B₁₂ * A₃) := by noncomm_ring
      _ = 0 := by rw [hc₃]; simp
  simp only [Ring.lie_def, map_neg] at hb
  rw [hneg₁, hneg₂, hneg₃] at hb
  have hsum : -(d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂) = 0 := by
    have hb' : -d₁ B₂₃ + (-d₂ B₃₁ + -d₃ B₁₂) = 0 := by
      simpa only [add_zero, zero_add, add_assoc] using hb
    calc
      _ = -d₁ B₂₃ + (-d₂ B₃₁ + -d₃ B₁₂) := by abel
      _ = 0 := hb'
  exact neg_eq_zero.mp hsum

end GerbeFlatness

section RankFourExample

abbrev Mat4Z := Matrix (Fin 4) (Fin 4) ℤ

def boundaryT₁ : Mat4Z :=
  ![![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0]]

def boundaryT₂ : Mat4Z :=
  ![![0, -1, 0, 0], ![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

def torsionAnomaly : Mat4Z :=
  ![![0, 1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 1, 0]]

/-- Concrete orthogonal pair with the displayed finite-order projective
commutator. This proves orthogonality, without asserting determinant one. -/
theorem boundary_pair_relations :
    Matrix.transpose boundaryT₁ * boundaryT₁ = 1 ∧
      Matrix.transpose boundaryT₂ * boundaryT₂ = 1 ∧
      boundaryT₁ * boundaryT₂ = torsionAnomaly * boundaryT₂ * boundaryT₁ ∧
      torsionAnomaly * boundaryT₁ ≠ boundaryT₁ * torsionAnomaly := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem torsionAnomaly_exact_order_four :
    torsionAnomaly ≠ 1 ∧ torsionAnomaly ^ 2 = -1 ∧
      torsionAnomaly ^ 2 ≠ 1 ∧ torsionAnomaly ^ 4 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end RankFourExample

end InfoGeometry.OperatorAlgebra.GerbeTwistedCurvatureTorsion

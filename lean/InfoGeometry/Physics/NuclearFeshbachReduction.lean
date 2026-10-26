/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearOperatorSchurComplement
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

/-!
# Exact Feshbach elimination on a direct sum

The inverse belongs to the Q-space endomorphism D−E, not its singular
zero extension to the ambient space. No existence of this inverse is asserted
for the full phonon Hamiltonian. The theorem includes Q-space reconstruction.
-/

noncomputable section
namespace InfoGeometry.Physics.NuclearFeshbachReduction

variable {𝕜 P Q : Type*} [Field 𝕜]
  [AddCommGroup P] [Module 𝕜 P] [AddCommGroup Q] [Module 𝕜 Q]

/-- Native direct-sum block operator with independent P and Q dimensions. -/
def blockOperator (A : P →ₗ[𝕜] P) (B : Q →ₗ[𝕜] P)
    (C : P →ₗ[𝕜] Q) (D : Q →ₗ[𝕜] Q) : (P × Q) →ₗ[𝕜] (P × Q) :=
  (A.coprod B).prod (C.coprod D)

/-- Reconstruction at the chosen energy; K is the inverse of D−E. -/
def reconstruction (C : P →ₗ[𝕜] Q) (K : Q →ₗ[𝕜] Q) : P →ₗ[𝕜] (P × Q) :=
  LinearMap.id.prod (-(K.comp C))

theorem reconstruction_injective (C : P →ₗ[𝕜] Q) (K : Q →ₗ[𝕜] Q) :
    Function.Injective (reconstruction C K) := by
  intro x y h
  exact congrArg Prod.fst h

/-- Exact kernel equivalence, including the reconstructed complementary component. -/
theorem eigen_equation_iff
    (A : P →ₗ[𝕜] P) (B : Q →ₗ[𝕜] P) (C : P →ₗ[𝕜] Q) (D K : Q →ₗ[𝕜] Q)
    (E : 𝕜) (hK : NuclearOperatorSchurComplement.InversePair
      (D - E • LinearMap.id) K) (x : P) (y : Q) :
    blockOperator A B C D (x, y) = E • (x, y) ↔
      (A - B.comp (K.comp C)) x = E • x ∧ y = -K (C x) := by
  have hleft (z : Q) : K (D z - E • z) = z := by
    simpa using congrArg (fun T : Q →ₗ[𝕜] Q => T z) hK.left_inv
  have hright (z : Q) : D (K z) - E • K z = z := by
    simpa using congrArg (fun T : Q →ₗ[𝕜] Q => T z) hK.right_inv
  change (A x + B y, C x + D y) = (E • x, E • y) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq⟩
    have hden : D y - E • y = -C x := by rw [← hq]; abel
    have hy : y = -K (C x) := by rw [← hleft y, hden, map_neg]
    refine ⟨?_, hy⟩
    simpa [hy, sub_eq_add_neg] using hp
  · rintro ⟨hp, rfl⟩
    constructor
    · simpa [sub_eq_add_neg] using hp
    · have h := hright (C x)
      simp only [map_neg, smul_neg]
      calc
        C x + -D (K (C x)) =
            (D (K (C x)) - E • K (C x)) + -D (K (C x)) :=
          congrArg (fun z => z + -D (K (C x))) h.symm
        _ = -(E • K (C x)) := by abel

/-- A reduced eigenvector reconstructs to a full one, with nonzero preserved. -/
theorem reconstructed_nonzero_eigenvector_iff
    (A : P →ₗ[𝕜] P) (B : Q →ₗ[𝕜] P) (C : P →ₗ[𝕜] Q) (D K : Q →ₗ[𝕜] Q)
    (E : 𝕜) (hK : NuclearOperatorSchurComplement.InversePair
      (D - E • LinearMap.id) K) (x : P) :
    (reconstruction C K x ≠ 0 ∧
      blockOperator A B C D (reconstruction C K x) = E • reconstruction C K x) ↔
    (x ≠ 0 ∧ (A - B.comp (K.comp C)) x = E • x) := by
  have hn : reconstruction C K x = 0 ↔ x = 0 :=
    (reconstruction_injective C K).eq_iff' (map_zero _)
  change (_ ∧ blockOperator A B C D (x, -K (C x)) = E • (x, -K (C x))) ↔ _
  rw [eigen_equation_iff A B C D K E hK]
  simp [hn]

/-- For a common carrier this is precisely the existing noncommutative Schur owner. -/
theorem effective_eq_existing (A B C K : P →ₗ[𝕜] P) :
    A - B.comp (K.comp C) =
      NuclearOperatorSchurComplement.effectiveOperator A B C K := by
  rfl

open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

/-- Concrete two-channel specialization: the complementary pole is explicitly excluded. -/
theorem two_channel_feshbach (a d v E : ℝ) (h : d - E ≠ 0) (ψ : Carrier) :
    isEigenpair (blockHamiltonian a d v) ψ E ↔
      (a - v ^ 2 / (d - E)) * ψ 0 = E * ψ 0 ∧
      ψ 1 = -(v * ψ 0) / (d - E) := by
  rw [block_eigenpair_iff]
  constructor
  · rintro ⟨hp, hq⟩
    have hy : ψ 1 = -(v * ψ 0) / (d - E) := by
      apply (eq_div_iff h).mpr
      nlinarith [hq]
    refine ⟨?_, hy⟩
    rw [hy] at hp
    field_simp at hp ⊢
    nlinarith [hp]
  · rintro ⟨hp, hy⟩
    have hq := (eq_div_iff h).mp hy
    constructor
    · rw [hy]
      field_simp [h] at hp ⊢
      nlinarith [hp]
    · nlinarith [hq]

/-- At an excluded Q-space pole a pure complementary eigenvector really exists.
The inverse hypothesis cannot be dropped even when the coupling vanishes. -/
theorem complementary_pole_eigenvector (a d : ℝ) :
    isEigenpair (blockHamiltonian a d 0) ![0, 1] d ∧
      (![0, 1] : Carrier) ≠ 0 := by
  constructor
  · rw [block_eigenpair_iff]
    simp
  · intro h
    have := congrFun h 1
    norm_num at this

end InfoGeometry.Physics.NuclearFeshbachReduction

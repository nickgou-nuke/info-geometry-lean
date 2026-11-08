import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Symbolic BN2 Identity for the Rank-1 Levi Subgroup SL₂(𝔽₂)

Formalizes the exact $(B, N)$ axiom BN2 identity `s * B * s ⊆ B ∪ B * s * B`
for the rank-1 Levi subgroup `SL₂(𝔽₂) ≃ S₃` acting on the unipotent root subgroup
`U = {u(t) | t ∈ 𝔽₂}`.

Proves the two structural branches:
  1. `t = 0 ⟹ s * u(0) * s = 1 ∈ B` (Identity / Toral collapse)
  2. `t = 1 ⟹ s * u(1) * s = u(1) * s * u(1) ∈ B * s * B` (SL₂ Coxeter braid relation)
without brute-force searches over coset lookup tables.
-/

open Matrix

namespace InfoGeometry.Algebra.Zorn.SL2Levi

/-! =========================================================================
    1. SL₂(𝔽₂) Generators: Reflection and Unipotent Parametrization
    ========================================================================= -/

/-- Simple reflection generator `s = [[0, 1], [1, 0]]` in `SL₂(𝔽₂)`. -/
def sMatrix : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1],
    ![1, 0]]

/-- Unipotent root element `u(t) = [[1, t], [0, 1]]` parametrized by `t ∈ 𝔽₂`. -/
def uMatrix (t : ZMod 2) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, t],
    ![0, 1]]

/-! =========================================================================
    2. Borel Subgroup and Bruhat Double-Coset Cell Predicates
    ========================================================================= -/

/-- Borel subgroup predicate: `M ∈ B ↔ ∃ t : 𝔽₂, M = u(t)`. -/
def InBorel (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Prop :=
  ∃ t : ZMod 2, M = uMatrix t

/-- Big Bruhat cell predicate: `M ∈ B * s * B ↔ ∃ t₁ t₂ : 𝔽₂, M = u(t₁) * s * u(t₂)`. -/
def InBsB (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Prop :=
  ∃ t₁ t₂ : ZMod 2, M = uMatrix t₁ * sMatrix * uMatrix t₂

/-- Double coset union `B ∪ B * s * B`. -/
def InBruhatCover (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Prop :=
  InBorel M ∨ InBsB M

/-! =========================================================================
    3. Structural Rank-1 Levi Algebraic Identities
    ========================================================================= -/

/-- THEOREM: The simple reflection `s` is an involution: `s * s = 1`. -/
theorem sMatrix_sq : sMatrix * sMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/--
THEOREM (Branch 1 - Toral / Identity Collapse):
For `t = 0`, conjugation by `s` fixes the identity in `B`:
  `s * u(0) * s = 1 = u(0)`
-/
theorem s_u0_s_eq : sMatrix * uMatrix 0 * sMatrix = uMatrix 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/--
THEOREM (Branch 2 - Rank-1 Coxeter Braid Relation):
For the non-trivial unipotent generator `t = 1`, conjugation by `s` satisfies
the fundamental `SL₂(𝔽₂)` factorization:
  `s * u(1) * s = u(1) * s * u(1)`
-/
theorem s_u1_s_eq :
    sMatrix * uMatrix 1 * sMatrix = uMatrix 1 * sMatrix * uMatrix 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! =========================================================================
    4. Symbolic BN2 Theorem for SL₂(𝔽₂)
    ========================================================================= -/

/--
LEMMA: Explicit evaluation of `s * u(t) * s` for any field coordinate `t ∈ 𝔽₂`.
-/
theorem s_ut_s_in_cover (t : ZMod 2) : InBruhatCover (sMatrix * uMatrix t * sMatrix) := by
  fin_cases t
  · -- Case t = 0: lands in B
    left
    exact ⟨0, s_u0_s_eq⟩
  · -- Case t = 1: lands in B * s * B
    right
    exact ⟨1, 1, s_u1_s_eq⟩

/--
MAIN THEOREM (Axiom BN2 for Rank-1 Levi Subgroup):
For every element `b ∈ B = U(𝔽₂)`, the conjugate `s * b * s` is contained
in the Bruhat union `B ∪ B * s * B`:
  `s * B * s ⊆ B ∪ B * s * B`
-/
theorem sl2_bn2_symbolic (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hb : InBorel M) :
    InBruhatCover (sMatrix * M * sMatrix) := by
  obtain ⟨t, rfl⟩ := hb
  exact s_ut_s_in_cover t

end InfoGeometry.Algebra.Zorn.SL2Levi

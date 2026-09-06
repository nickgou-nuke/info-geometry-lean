import InfoGeometry.Canonical.SplitCliffordSuperVirasoroInductiveColimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

noncomputable section

namespace InfoGeometry.Canonical.SuperVirasoroColimitReadback

open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.SuperVirasoroInductiveColimit
open InfoGeometry.Canonical.SuperVirasoroFiniteWindow

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type} [AddCommGroup V] [Module 𝕜 V]

local notation "EndV" => Module.End 𝕜 V
local notation "StageFamily" => (fun _ : ℕ => EndV)

/--
Read back the exact `[L,G]` superbracket from the genuine algebraic direct limit
through any compatible cone.

This is the first honest downstream consumer of
`SplitCliffordSuperVirasoroInductiveColimit`: a stage-level exactness theorem in
`EndV` is first transported to the true direct-limit object, and then read back
through the universal factorization into an arbitrary target ring.
-/
theorem readback_superBracket_LG_of_boundaryDefect_zero
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (N m r : ℤ) (J ψ : ℤ → EndV)
    (hdef : boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0) :
    superBracket false true
        (toLimit N.natAbs (L_trunc N m J ψ))
        (toLimit N.natAbs (G_trunc N r J ψ))
      = toLimit N.natAbs ((LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ)) := by
  let φ := directLimitLift (Stage := StageFamily) bond toLimit hcone
  have hcolim :=
    directLimit_superBracket_LG_of_boundaryDefect_zero
      (𝕜 := 𝕜) (V := V) (bond := bond) N m r J ψ hdef
  have hread :=
    superBracket_eq_transport φ hcolim
  dsimp [φ] at hread
  unfold ofStage at hread
  rw [directLimitLift_of (Stage := StageFamily) bond toLimit hcone,
      directLimitLift_of (Stage := StageFamily) bond toLimit hcone,
      directLimitLift_of (Stage := StageFamily) bond toLimit hcone] at hread
  exact hread

/--
Read back the exact `{G,G}` superbracket from the genuine algebraic direct limit
through any compatible cone.
-/
theorem readback_superBracket_GG_of_boundaryDefect_zero
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜)
    (hdef : boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N = 0) :
    superBracket true true
        (toLimit N.natAbs (G_trunc N r J ψ))
        (toLimit N.natAbs (G_trunc N s J ψ))
      = toLimit N.natAbs
          ((2 : 𝕜) • (L_trunc N (r + s) J ψ) + (central_N r s) • (1 : EndV)) := by
  let φ := directLimitLift (Stage := StageFamily) bond toLimit hcone
  have hcolim :=
    directLimit_superBracket_GG_of_boundaryDefect_zero
      (𝕜 := 𝕜) (V := V) (bond := bond) N r s J ψ central_N hdef
  have hread :=
    superBracket_eq_transport φ hcolim
  dsimp [φ] at hread
  unfold ofStage at hread
  rw [directLimitLift_of (Stage := StageFamily) bond toLimit hcone,
      directLimitLift_of (Stage := StageFamily) bond toLimit hcone,
      directLimitLift_of (Stage := StageFamily) bond toLimit hcone] at hread
  exact hread

end InfoGeometry.Canonical.SuperVirasoroColimitReadback

import Mathlib
import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroFiniteWindow
import InfoGeometry.Canonical.SplitCliffordSuperVirasoroInductiveColimit
import InfoGeometry.Canonical.SplitCliffordSuperVirasoroColimitReadback
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.SupergradedBracket

noncomputable section

namespace VirasoroProjectColimitBridge

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Canonical.SuperVirasoroInductiveColimit
open InfoGeometry.Canonical.SuperVirasoroColimitReadback
open InfoGeometry.Canonical.SuperVirasoroFiniteWindow

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type} [AddCommGroup V] [Module 𝕜 V]

local notation "EndV" => Module.End 𝕜 V
local notation "StageFamily" => (fun _ : ℕ => EndV)

/--
Transport a vanishing finite mixed-superbracket boundary defect directly through any
compatible cone of the colimit.
-/
theorem readback_superBracket_LG_of_boundaryDefect_zero'
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (N m r : ℤ) (J ψ : ℤ → EndV)
    (hdef : boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0) :
    superBracket false true
        (toLimit N.natAbs (L_trunc N m J ψ))
        (toLimit N.natAbs (G_trunc N r J ψ))
      = toLimit N.natAbs ((LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ)) := by
  exact readback_superBracket_LG_of_boundaryDefect_zero (𝕜 := 𝕜) (V := V)
    bond toLimit hcone N m r J ψ hdef

/--
Transport a vanishing finite `{G,G}` boundary defect directly through any compatible
cone of the colimit.
-/
theorem readback_superBracket_GG_of_boundaryDefect_zero'
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
  exact readback_superBracket_GG_of_boundaryDefect_zero (𝕜 := 𝕜) (V := V)
    bond toLimit hcone N r s J ψ central_N hdef

/--
If the finite mixed defect is eventually zero along the cutoff filtration,
then the transported mixed super-bracket is eventually exact in the same
filtered colimit family.
-/
theorem readback_superBracket_LG_eventually_of_boundaryDefect_zero
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (m r : ℤ) (J ψ : ℤ → EndV)
    (hdef : ∀ᶠ N : ℤ in atTop, boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0) :
    ∀ᶠ N : ℤ in atTop,
      superBracket false true
        (toLimit N.natAbs (L_trunc N m J ψ))
        (toLimit N.natAbs (G_trunc N r J ψ))
      = toLimit N.natAbs ((LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ)) := by
  filter_upwards [hdef] with N hN
  exact readback_superBracket_LG_of_boundaryDefect_zero' (𝕜 := 𝕜) (V := V)
    bond toLimit hcone N m r J ψ hN

/--
If the finite `{G,G}` defect is eventually zero along the cutoff filtration,
then the transported anticommutator is eventually exact in the same filtered
colimit family.
-/
theorem readback_superBracket_GG_eventually_of_boundaryDefect_zero
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (toLimit : ∀ _n : ℕ, EndV →+* EndV)
    (hcone : CompatibleCone (Stage := StageFamily) bond toLimit)
    (r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜)
    (hdef : ∀ᶠ N : ℤ in atTop, boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N = 0) :
    ∀ᶠ N : ℤ in atTop,
      superBracket true true
        (toLimit N.natAbs (G_trunc N r J ψ))
        (toLimit N.natAbs (G_trunc N s J ψ))
      = toLimit N.natAbs
          ((2 : 𝕜) • (L_trunc N (r + s) J ψ) + (central_N r s) • (1 : EndV)) := by
  filter_upwards [hdef] with N hN
  exact readback_superBracket_GG_of_boundaryDefect_zero' (𝕜 := 𝕜) (V := V)
    bond toLimit hcone N r s J ψ central_N hN

/--
A direct concrete colimit readback in `End ℝ` at the witness mode families
`J_mode0` and `psi_mode1` for the `[L,G]` mixed relation.
-/
theorem concrete_readback_trivial_bond_LG_mode01_r0 (N : ℤ) :
    superBracket false true
      ((RingHom.id (Module.End ℝ ℝ))
        (L_trunc N 0 (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ)) (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))))
      ((RingHom.id (Module.End ℝ ℝ))
        (G_trunc N 0 (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ)) (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))))
      = (RingHom.id (Module.End ℝ ℝ))
          ((LG_coeff (𝕜 := ℝ) 0 0) •
            (G_trunc N (0 + 0) (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
              (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ)))) := by
  let bond : ∀ _n : ℕ, Module.End ℝ ℝ →+* Module.End ℝ ℝ :=
    fun _ => RingHom.id (Module.End ℝ ℝ)
  let hcone : CompatibleCone (Stage := fun _ : ℕ => Module.End ℝ ℝ) bond (fun _ => RingHom.id (Module.End ℝ ℝ)) := by
    intro n x
    simp [bond]
  have hdef : boundaryDefect_LG (𝕜 := ℝ) N 0 0 (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
      (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ)) = 0 :=
    boundaryDefect_LG_mode01_r0_eq_zero (𝕜 := ℝ) N 1 1
  simpa [bond, hcone, add_zero, zero_add] using
    readback_superBracket_LG_of_boundaryDefect_zero'
      (𝕜 := ℝ)
      (bond := bond)
      (toLimit := fun _ => RingHom.id (Module.End ℝ ℝ))
      hcone N 0 0 (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
      (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ)) hdef

/--
A direct concrete colimit readback in `End ℝ` at the witness mode families
`J_mode0` and `psi_mode1` for the `{G,G}` anticommutator relation.
-/
theorem concrete_readback_trivial_bond_GG_mode01_r0_s1 (N : ℤ) :
    superBracket true true
      ((RingHom.id (Module.End ℝ ℝ))
        (G_trunc N 0 (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
          (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))))
      ((RingHom.id (Module.End ℝ ℝ))
        (G_trunc N 1 (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
          (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))))
      = (RingHom.id (Module.End ℝ ℝ))
          ((2 : ℝ) •
            (L_trunc N (0 + 1) (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
              (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ)))
            + (centralZero (𝕜 := ℝ) 0 1) • (1 : Module.End ℝ ℝ)) := by
  let bond : ∀ _n : ℕ, Module.End ℝ ℝ →+* Module.End ℝ ℝ :=
    fun _ => RingHom.id (Module.End ℝ ℝ)
  let hcone : CompatibleCone (Stage := fun _ : ℕ => Module.End ℝ ℝ) bond (fun _ => RingHom.id (Module.End ℝ ℝ)) := by
    intro n x
    simp [bond]
  have hdef :
      boundaryDefect_GG (𝕜 := ℝ) N 0 1
        (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
        (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
        (centralZero (𝕜 := ℝ)) = 0 :=
    boundaryDefect_GG_mode01_r0_s1_centralZero_eq_zero (𝕜 := ℝ) N 1 1
  simpa [bond, hcone, add_comm, add_left_comm, add_assoc] using
    readback_superBracket_GG_of_boundaryDefect_zero'
      (𝕜 := ℝ)
      (bond := bond)
      (toLimit := fun _ => RingHom.id (Module.End ℝ ℝ))
      hcone N 0 1 (J_mode0 (𝕜 := ℝ) (1 : Module.End ℝ ℝ))
      (psi_mode1 (𝕜 := ℝ) (1 : Module.End ℝ ℝ)) (centralZero (𝕜 := ℝ)) hdef

end VirasoroProjectColimitBridge

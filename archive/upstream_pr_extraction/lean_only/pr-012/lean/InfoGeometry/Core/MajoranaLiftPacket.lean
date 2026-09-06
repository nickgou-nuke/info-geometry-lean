import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace
set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Core.MajoranaLiftPacket

Owner packet for the doubled-core Majorana lift.

This is intentionally root-level and algebraic:
it records only the doubled-carrier involution data `(J, ε, K = J ∘ ε)` and
its defining closure laws.
-/

namespace InfoGeometry.Core

open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Minimal doubled-core Majorana packet.

`J` and `ε` are involutions with split `Cl(1,1)` anticommutation, and `K` is
the derived phase axis.
-/
@[rep_depth krein]
structure MajoranaLiftPacket where
  J : EndH
  eps : EndH
  K : EndH
  hJ_sq : J.comp J = ContinuousLinearMap.id ℝ H₂
  hEps_sq : eps.comp eps = ContinuousLinearMap.id ℝ H₂
  hJ_eps_anticomm : J.comp eps = -(eps.comp J)
  hK_eq_J_comp_eps : K = J.comp eps

namespace MajoranaLiftPacket

variable (P : MajoranaLiftPacket (E := E))

/-- Derived phase-axis square law: `(Jε)^2 = -Id`. -/
@[rep_depth krein]
theorem K_sq_eq_neg_id :
    P.K.comp P.K = -(ContinuousLinearMap.id ℝ H₂) := by
  rw [P.hK_eq_J_comp_eps]
  exact
    InfoGeometry.Krein.K_sq_of_relations
      (J := P.J) (ε := P.eps)
      P.hJ_sq P.hEps_sq P.hJ_eps_anticomm

end MajoranaLiftPacket

/-- Canonical doubled-core Majorana packet from the repo-owned root maps. -/
@[rep_depth krein]
noncomputable def canonicalMajoranaLiftPacket : MajoranaLiftPacket (E := E) where
  J := modular_j (E := E)
  eps := spectral_epsilon (E := E)
  K := complex_i (E := E)
  hJ_sq := modular_j_involution (E := E)
  hEps_sq := spectral_epsilon_involution (E := E)
  hJ_eps_anticomm := modular_j_spectral_epsilon_anticommute (E := E)
  hK_eq_J_comp_eps := rfl

@[rep_depth krein, simp]
theorem canonicalMajoranaLiftPacket_J_eq_modular_j :
    (canonicalMajoranaLiftPacket (E := E)).J = modular_j (E := E) := rfl

@[rep_depth krein, simp]
theorem canonicalMajoranaLiftPacket_eps_eq_spectral_epsilon :
    (canonicalMajoranaLiftPacket (E := E)).eps = spectral_epsilon (E := E) := rfl

@[rep_depth krein, simp]
theorem canonicalMajoranaLiftPacket_K_eq_complex_i :
    (canonicalMajoranaLiftPacket (E := E)).K = complex_i (E := E) := rfl

@[rep_depth krein]
theorem canonicalMajoranaLiftPacket_root_laws :
    let P := canonicalMajoranaLiftPacket (E := E)
    P.J = modular_j (E := E)
      ∧ P.eps = spectral_epsilon (E := E)
      ∧ P.K = complex_i (E := E)
      ∧ P.K.comp P.K = -(ContinuousLinearMap.id ℝ H₂) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact MajoranaLiftPacket.K_sq_eq_neg_id (E := E) (canonicalMajoranaLiftPacket (E := E))

end Core

end InfoGeometry.Core

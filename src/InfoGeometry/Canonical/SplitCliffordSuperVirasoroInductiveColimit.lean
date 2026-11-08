import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroFiniteWindow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.SupergradedBracket

noncomputable section

namespace InfoGeometry.Canonical.SuperVirasoroInductiveColimit

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Canonical.SuperVirasoroFiniteWindow

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type} [AddCommGroup V] [Module 𝕜 V]

local notation "EndV" => Module.End 𝕜 V
local notation "StageFamily" => (fun _ : ℕ => EndV)

abbrev Limit (bond : ∀ _n : ℕ, EndV →+* EndV) : Type :=
  DirectLimitSuperClosure (Stage := StageFamily) bond

def ofStage (bond : ∀ _n : ℕ, EndV →+* EndV) (n : ℕ) : EndV →+* Limit bond :=
  directLimitOf (Stage := StageFamily) bond n

@[simp] theorem ofStage_apply_bond
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (n : ℕ) (x : EndV) :
    ofStage (bond := bond) (n + 1) (bond n x) = ofStage (bond := bond) n x := by
  exact directLimitOf_bond (Stage := StageFamily) bond n x

@[simp] theorem directLimit_superBracket_LG_of_boundaryDefect_zero
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (N m r : ℤ) (J ψ : ℤ → EndV)
    (hdef : boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0) :
    let φ := ofStage (bond := bond) N.natAbs
    superBracket false true
        (φ (L_trunc N m J ψ))
        (φ (G_trunc N r J ψ))
      = φ ((LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ)) := by
  dsimp
  exact superBracket_eq_transport (ofStage (bond := bond) N.natAbs)
    (superBracket_LG_of_boundaryDefect_zero (𝕜 := 𝕜) N m r J ψ hdef)

@[simp] theorem directLimit_superBracket_GG_of_boundaryDefect_zero
    (bond : ∀ _n : ℕ, EndV →+* EndV)
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜)
    (hdef : boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N = 0) :
    let φ := ofStage (bond := bond) N.natAbs
    superBracket true true
        (φ (G_trunc N r J ψ))
        (φ (G_trunc N s J ψ))
      = φ ((2 : 𝕜) • (L_trunc N (r + s) J ψ) + (central_N r s) • (1 : EndV)) := by
  dsimp
  exact superBracket_eq_transport (ofStage (bond := bond) N.natAbs)
    (superBracket_GG_of_boundaryDefect_zero (𝕜 := 𝕜) N r s J ψ central_N hdef)

end InfoGeometry.Canonical.SuperVirasoroInductiveColimit

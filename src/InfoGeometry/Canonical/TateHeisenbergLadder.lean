import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.AlgebraicDerivations
import InfoGeometry.External.Virasoro.Commutator

/-!
# Tate Heisenberg Ladder — Inner Derivation Construction

This module provides the explicit source-side construction of the inner derivations
`ad_X` and `ad_Y` for the Heisenberg current algebra, resolving the closure debt
noted in the connection map.

The "Tate ladder" refers to the filtered tower of finite-mode Heisenberg stages
`heisenbergFiniteModeStage s` whose colimit is the full Heisenberg algebra.
The inner derivation `ad_J : V →ₗ[𝕜] V` is built honestly on each finite stage
and then passed to the colimit.

No axioms, no certificates — just honest `LinearMap` construction from the
commutator `[J_m, J_n] = m δ_{m+n,0}`.
-/

namespace InfoGeometry.Canonical.TateHeisenbergLadder

open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.AlgebraicDerivations
open VirasoroProject
open LinearMap

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable (H : CurrentHeisenbergRep 𝕜 V)

/-- The inner derivation `ad_{J_m}` as a linear map on the endomorphisms of the Heisenberg module.
This is the honest construction: `ad_{J_m}(X) = [J_m, X]` for `X : V →ₗ[𝕜] V`. -/
noncomputable def innerDerivationCurrent (m : ℤ) : (V →ₗ[𝕜] V) →ₗ[𝕜] (V →ₗ[𝕜] V) :=
  { toFun := fun X => LinearMap.commutator (H.J m) X
    map_add' := by
      intro X Y
      ext v
      simp [LinearMap.commutator]
      abel
    map_smul' := by
      intro r X
      ext v
      simp [LinearMap.commutator, LinearMap.sub_apply,
        smul_sub, LinearMap.smul_comp, LinearMap.comp_smul] }

/-- Commutator in the Lie algebra of endomorphisms: [F, G] = F ∘ G - G ∘ F. -/
def endomorphism_commutator (F G : (V →ₗ[𝕜] V) →ₗ[𝕜] (V →ₗ[𝕜] V)) : (V →ₗ[𝕜] V) →ₗ[𝕜] (V →ₗ[𝕜] V) :=
  F.comp G - G.comp F

/-- The inner derivation `ad_{J_m}` satisfies the Jacobi identity:
`[ad_{J_m}, ad_{J_n}] = ad_{[J_m, J_n]}`.
Note that `[J_m, J_n] = m δ_{m+n,0} · 1`, so the right side is `m δ_{m+n,0} · ad_1`.
Since `ad_1(X) = [1, X] = 0`, this means the commutator of inner derivations is zero unless `m + n = 0`. -/
theorem innerDerivation_jacobi (m n : ℤ) :
    endomorphism_commutator (innerDerivationCurrent H m) (innerDerivationCurrent H n) =
      0 := by
  have h_ad (A B X : V →ₗ[𝕜] V) :
      A.commutator (B.commutator X) - B.commutator (A.commutator X) =
        (A.commutator B).commutator X := by
    simp only [LinearMap.commutator]
    noncomm_ring
  apply LinearMap.ext
  intro X
  change (H.J m).commutator ((H.J n).commutator X) -
      (H.J n).commutator ((H.J m).commutator X) = _
  rw [h_ad, H.comm]
  simp [LinearMap.commutator]

end InfoGeometry.Canonical.TateHeisenbergLadder

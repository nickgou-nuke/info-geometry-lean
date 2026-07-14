import Mathlib.Tactic
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# InfoGeometry.Canonical.SplitCliffordFiniteCurrentObstruction

Finite-support obstruction for the full Heisenberg current law.

This file proves a concrete no-go lemma:

a current family satisfying

  [J_m, J_n] = m δ_{m+n,0} 1

cannot vanish at both `k` and `-k` for any nonzero integer `k`.

Consequently, a finite two-mode seed supported only at `±1` cannot be promoted
to the global `CurrentHeisenbergRep` interface.

No wrappers.
No `sorry`.
-/

namespace SplitCliffordFiniteCurrentObstruction

open Filter
open InfoGeometry.Canonical.CurrentSugawaraBridge

/--
If a `CurrentHeisenbergRep` satisfies the global Heisenberg current law, then
opposite nonzero modes cannot both vanish.

This is the exact obstruction to upgrading a finite-support current family into
the full Heisenberg current representation.
-/
theorem currentHeisenbergRep_no_opposite_zero_modes
    {𝕜 V : Type*}
    [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [Nontrivial V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (k : Int)
    (hk : k ≠ 0)
    (hJk : H.J k = 0)
    (hJneg : H.J (-k) = 0) :
    False := by
  have hsum : k + (-k) = 0 := by omega

  have hcentral :
      (H.J k).commutator (H.J (-k)) =
        (k : 𝕜) • (1 : V →ₗ[𝕜] V) := by
    simpa [hsum] using H.comm k (-k)

  have hleft_zero :
      (H.J k).commutator (H.J (-k)) =
        (0 : V →ₗ[𝕜] V) := by
    rw [hJk, hJneg]
    ext v
    simp [LinearMap.commutator]

  have hscalar_zero :
      (k : 𝕜) • (1 : V →ₗ[𝕜] V) =
        (0 : V →ₗ[𝕜] V) := by
    rw [← hcentral]
    exact hleft_zero

  have hk_scalar : (k : 𝕜) ≠ 0 := by
    exact_mod_cast hk

  obtain ⟨v, hv⟩ := exists_ne (0 : V)

  have happ :
      ((k : 𝕜) • (1 : V →ₗ[𝕜] V)) v = 0 := by
    simpa using congrArg (fun f : V →ₗ[𝕜] V => f v) hscalar_zero

  have hv_zero : v = 0 := by
    have : (k : 𝕜) • v = 0 := by
      simpa using happ
    exact (smul_eq_zero.mp this).resolve_left hk_scalar

  exact hv hv_zero

/--
A full `CurrentHeisenbergRep` cannot be supported only in modes `±1`.

This blocks the false upgrade

  finite two-mode CAR seed ⟶ global `CurrentHeisenbergRep`.

The obstruction is the mode pair `(2,-2)`: finite support gives both modes zero,
but the Heisenberg law would force their commutator to be `2 • 1`.
-/
theorem no_two_mode_supported_currentHeisenbergRep
    {𝕜 V : Type*}
    [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [Nontrivial V]
    (H : CurrentHeisenbergRep 𝕜 V)
    (hSupport :
      ∀ n : Int,
        n ≠ 1 → n ≠ -1 → H.J n = 0) :
    False := by
  exact currentHeisenbergRep_no_opposite_zero_modes
    (H := H)
    (k := 2)
    (by norm_num)
    (hSupport 2 (by norm_num) (by norm_num))
    (hSupport (-2) (by norm_num) (by norm_num))

end SplitCliffordFiniteCurrentObstruction

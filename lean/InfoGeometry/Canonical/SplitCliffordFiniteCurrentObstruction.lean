import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.SplitCliffordFiniteCurrentObstruction

Finite-support obstruction for the Heisenberg current law.

This file proves a concrete no-go lemma:

a current family satisfying

  `[J_m, J_n] = m δ_{m+n,0} 1`

cannot vanish at both `k` and `-k` for any nonzero integer `k`.

Consequently, a finite two-mode CAR seed cannot be promoted to the full
`CurrentHeisenbergRep` interface. It may be a finite local model, but it is not
the global Heisenberg current algebra.
-/

namespace InfoGeometry.Canonical.SplitCliffordFiniteCurrentObstruction

def linComm
    {𝕜 V : Type*} [Semiring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (A B : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  A.comp B - B.comp A

/--
If a current family satisfies the global Heisenberg commutator law, then it
cannot vanish at both `k` and `-k` for any nonzero integer `k`.

This is the exact obstruction to upgrading a finite-support two-mode current
into the full Heisenberg current representation.
-/
theorem no_zero_opposite_modes_of_heisenberg_comm
    {𝕜 V : Type*}
    [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [Nontrivial V]
    (J : Int → V →ₗ[𝕜] V)
    (k : Int)
    (hk : k ≠ 0)
    (hJk : J k = 0)
    (hJneg : J (-k) = 0)
    (hcomm :
      ∀ m n : Int,
        linComm (J m) (J n) =
          if m + n = 0 then
            (m : 𝕜) • (1 : V →ₗ[𝕜] V)
          else
            0) :
    False := by
  have hsum : k + (-k) = 0 := by omega
  have hcentral :
      linComm (J k) (J (-k)) =
        (k : 𝕜) • (1 : V →ₗ[𝕜] V) := by
    rw [hcomm k (-k), if_pos hsum]
  have hleft_zero :
      linComm (J k) (J (-k)) =
        (0 : V →ₗ[𝕜] V) := by
    simpa [linComm, hJk, hJneg]
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
    exact (smul_eq_zero.mp happ).resolve_left hk_scalar
  exact hv hv_zero

/--
Special case: a current family supported only in modes `±1` cannot satisfy the
full Heisenberg current law.

This is the concrete theorem blocking a false finite two-mode
`CurrentHeisenbergRep` construction.
-/
theorem no_two_mode_support_heisenberg_comm
    {𝕜 V : Type*}
    [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [Nontrivial V]
    (J : Int → V →ₗ[𝕜] V)
    (hSupport :
      ∀ n : Int,
        n ≠ 1 → n ≠ -1 → J n = 0)
    (hcomm :
      ∀ m n : Int,
        linComm (J m) (J n) =
          if m + n = 0 then
            (m : 𝕜) • (1 : V →ₗ[𝕜] V)
          else
            0) :
    False := by
  apply no_zero_opposite_modes_of_heisenberg_comm
    (J := J) (k := 2)
  · norm_num
  · exact hSupport 2 (by norm_num) (by norm_num)
  · exact hSupport (-2) (by norm_num) (by norm_num)
  · exact hcomm

end InfoGeometry.Canonical.SplitCliffordFiniteCurrentObstruction

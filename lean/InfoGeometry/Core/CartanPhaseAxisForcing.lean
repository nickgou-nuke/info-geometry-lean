import InfoGeometry.Core.SymmetricLie

/-!
# Cartan Phase-Axis Forcing

Owner surface for forcing lemmas that place phase-axis commutators in the odd
sector from symmetric-pair assumptions.
-/

namespace InfoGeometry.Core

namespace SymmetricLieAlgebra

/-- The ordered commutator `[I, K]` lies in the odd sector. -/
theorem commutator_IK_mem_odd
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) (K I : L)
    (hK_odd : K ∈ S.oddSubmodule)
    (hI_even : I ∈ S.evenLieSubalgebra) :
    ⁅I, K⁆ ∈ S.oddSubmodule := by
  exact
    SymmetricLieAlgebra.bracket_k_p (S := S) (x := I) (y := K)
      hI_even hK_odd

/-- The commutator `[K, I]` lies in the odd sector as well. -/
theorem commutator_KI_mem_odd
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) (K I : L)
    (hK_odd : K ∈ S.oddSubmodule)
    (hI_even : I ∈ S.evenLieSubalgebra) :
    ⁅K, I⁆ ∈ S.oddSubmodule := by
  simpa [lie_skew] using
    S.oddSubmodule.neg_mem
      (commutator_IK_mem_odd S K I hK_odd hI_even)

/-- Compatibility naming: odd sector as `𝔭`. -/
theorem commutator_KI_mem_p
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) (K I : L)
    (hK_odd : K ∈ S.oddSubmodule)
    (hI_even : I ∈ S.evenLieSubalgebra) :
    ⁅K, I⁆ ∈ S.𝔭 :=
  commutator_KI_mem_odd S K I hK_odd hI_even

/--
Over the real Cartan split, the even and odd eigenspaces of the same
involution intersect only at zero.
-/
theorem eq_zero_of_mem_even_and_odd
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) {x : L}
    (hxEven : x ∈ S.evenLieSubalgebra)
    (hxOdd : x ∈ S.oddSubmodule) :
    x = 0 := by
  have hEven : S.θ x = x := (S.mem_even_iff).1 hxEven
  have hOdd : S.θ x = -x := (S.mem_oddSubmodule_iff).1 hxOdd
  have hx : x = -x := by
    calc
      x = S.θ x := hEven.symm
      _ = -x := hOdd
  have htwo : (2 : ℝ) • x = 0 := by
    calc
      (2 : ℝ) • x = x + x := by simp [two_smul]
      _ = x + -x := by exact congrArg (fun y : L => x + y) hx
      _ = 0 := by simp
  have hhalf :
      ((2 : ℝ)⁻¹) • ((2 : ℝ) • x) = ((2 : ℝ)⁻¹) • (0 : L) := by
    exact congrArg (fun y : L => ((2 : ℝ)⁻¹) • y) htwo
  simpa [smul_smul] using hhalf

/--
If the forced commutator also lies in the even sector, the Cartan-grade
intersection rule kills it.
-/
theorem commutator_KI_eq_zero_of_mem_even
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) (K I : L)
    (hK_odd : K ∈ S.oddSubmodule)
    (hI_even : I ∈ S.evenLieSubalgebra)
    (hEven : ⁅K, I⁆ ∈ S.evenLieSubalgebra) :
    ⁅K, I⁆ = 0 :=
  eq_zero_of_mem_even_and_odd S hEven
    (commutator_KI_mem_odd S K I hK_odd hI_even)

/--
Constructive variant of the Cartan-grade collapse theorem using an explicit
even-sector witness object instead of a bare membership proof.
-/
theorem commutator_KI_eq_zero_of_evenWitness
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) (K I : L)
    (hK_odd : K ∈ S.oddSubmodule)
    (hI_even : I ∈ S.evenLieSubalgebra)
    (evenElement : S.evenLieSubalgebra)
    (evenElement_eq_commutator : (evenElement : L) = ⁅K, I⁆) :
    ⁅K, I⁆ = 0 := by
  apply commutator_KI_eq_zero_of_mem_even S K I hK_odd hI_even
  rw [← evenElement_eq_commutator]
  exact evenElement.property

namespace CartanEvenCommutatorWitness

/--
A native even-subalgebra carrier whose value is the commutator proves the
corresponding even-sector membership.
-/
theorem commutator_mem_even
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) (K I : L)
    (evenElement : S.evenLieSubalgebra)
    (evenElement_eq_commutator : (evenElement : L) = ⁅K, I⁆) :
    ⁅K, I⁆ ∈ S.evenLieSubalgebra := by
  rw [← evenElement_eq_commutator]
  exact evenElement.property

end CartanEvenCommutatorWitness

/--
Compatibility name for the D1 closure pattern: odd-sector forcing plus
independent even-sector membership gives a zero phase-axis commutator.
-/
theorem commutator_KI_eq_zero_of_dual_grade_forcing
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (S : SymmetricLieAlgebra L) (K I : L)
    (hK_odd : K ∈ S.𝔭)
    (hI_even : I ∈ S.𝔨)
    (hEven : ⁅K, I⁆ ∈ S.𝔨) :
    ⁅K, I⁆ = 0 :=
  commutator_KI_eq_zero_of_mem_even S K I hK_odd hI_even hEven

end SymmetricLieAlgebra

end InfoGeometry.Core

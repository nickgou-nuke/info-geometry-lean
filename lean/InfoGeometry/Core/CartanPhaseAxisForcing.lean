import InfoGeometry.Core.SymmetricLie

/-!
# Cartan Phase-Axis Forcing

Owner surface for forcing lemmas that place phase-axis commutators in the odd
sector from symmetric-pair assumptions.
-/

namespace InfoGeometry.Core

namespace SymmetricLieAlgebra

/--
Minimal owner data for odd-sector commutator forcing of a phase-axis pair.

`K` is the odd generator candidate and `I` is the even phase-axis anchor.
-/
structure CartanPhaseAxisForcingData
    (L : Type _) [LieRing L] [LieAlgebra ℝ L] where
  S : SymmetricLieAlgebra L
  K : L
  I : L
  hK_odd : K ∈ S.oddSubmodule
  hI_even : I ∈ S.evenLieSubalgebra

/--
Explicit even-sector witness for the phase-axis commutator.  This replaces a
bare membership hypothesis with an actual even-sector carrier whose underlying
element is the forced commutator.
-/
structure CartanEvenCommutatorWitness
    (L : Type _) [LieRing L] [LieAlgebra ℝ L] where
  data : CartanPhaseAxisForcingData L
  evenElement : data.S.evenLieSubalgebra
  evenElement_eq_commutator : (evenElement : L) = ⁅data.K, data.I⁆

namespace CartanEvenCommutatorWitness

/-- Recover the legacy even-sector membership from the explicit witness object. -/
theorem commutator_mem_even
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (W : CartanEvenCommutatorWitness L) :
    ⁅W.data.K, W.data.I⁆ ∈ W.data.S.evenLieSubalgebra := by
  rw [← W.evenElement_eq_commutator]
  exact W.evenElement.property

end CartanEvenCommutatorWitness

/-- The ordered commutator `[I, K]` lies in the odd sector. -/
theorem commutator_IK_mem_odd
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (D : CartanPhaseAxisForcingData L) :
    ⁅D.I, D.K⁆ ∈ D.S.oddSubmodule := by
  exact
    SymmetricLieAlgebra.bracket_k_p (S := D.S) (x := D.I) (y := D.K)
      D.hI_even D.hK_odd

/-- The commutator `[K, I]` lies in the odd sector as well. -/
theorem commutator_KI_mem_odd
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (D : CartanPhaseAxisForcingData L) :
    ⁅D.K, D.I⁆ ∈ D.S.oddSubmodule := by
  simpa [lie_skew] using
    D.S.oddSubmodule.neg_mem (commutator_IK_mem_odd (D := D))

/-- Compatibility naming: odd sector as `𝔭`. -/
theorem commutator_KI_mem_p
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (D : CartanPhaseAxisForcingData L) :
    ⁅D.K, D.I⁆ ∈ D.S.𝔭 :=
  commutator_KI_mem_odd (D := D)

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
    (D : CartanPhaseAxisForcingData L)
    (hEven : ⁅D.K, D.I⁆ ∈ D.S.evenLieSubalgebra) :
    ⁅D.K, D.I⁆ = 0 :=
  eq_zero_of_mem_even_and_odd D.S hEven (commutator_KI_mem_odd (D := D))

/--
Constructive variant of the Cartan-grade collapse theorem using an explicit
even-sector witness object instead of a bare membership proof.
-/
theorem commutator_KI_eq_zero_of_evenWitness
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (W : CartanEvenCommutatorWitness L) :
    ⁅W.data.K, W.data.I⁆ = 0 :=
  commutator_KI_eq_zero_of_mem_even W.data W.commutator_mem_even

/--
Compatibility name for the D1 closure pattern: odd-sector forcing plus
independent even-sector membership gives a zero phase-axis commutator.
-/
theorem commutator_KI_eq_zero_of_dual_grade_forcing
    {L : Type _} [LieRing L] [LieAlgebra ℝ L]
    (D : CartanPhaseAxisForcingData L)
    (hEven : ⁅D.K, D.I⁆ ∈ D.S.𝔨) :
    ⁅D.K, D.I⁆ = 0 :=
  commutator_KI_eq_zero_of_mem_even (D := D) hEven

end SymmetricLieAlgebra

end InfoGeometry.Core

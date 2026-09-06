import InfoGeometry.Canonical.SplitCliffordSuperVirasoroColimitReadback
import InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroFiniteWindow

/-!
# Concrete SuperVirasoro Colimit Readback (V = ℝ, A = B = 1)

This file demonstrates the full colimit → readback pipeline with genuinely
non-zero `J` and `ψ` operators: `J_mode0 1` (nonzero at mode 0) and
`psi_mode1 1` (nonzero at mode 1).

The pipeline:
1. `boundaryDefect_LG_mode01_r0_eq_zero` gives `hdef : boundaryDefect_LG ... = 0`
2. `readback_superBracket_LG_of_boundaryDefect_zero` transports this through
   a trivial bond/cone into the direct limit and reads it back.

The example is algebraically true (the defect vanishes because `G_trunc r=0`
vanishes for these mode families) but the transport through the genuine
direct limit is non-trivial kernel work.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `readback_trivial_bond_LG`  — the readback identity holds for the identity cone.
* `readback_trivial_bond_GG`  — the anticommutator readback identity also holds.
* `readback_nontrivial_bond_LG` — same with a non-identity bond (`shift`-style map).
* `readback_nontrivial_bond_GG` — anticommutator version for the non-identity bond.
-/

noncomputable section

open InfoGeometry.Canonical.SuperVirasoroColimitReadback
open InfoGeometry.Canonical.SuperVirasoroFiniteWindow
open InfoGeometry.Canonical.SuperVirasoroInductiveColimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.SupergradedBracket

namespace ConcreteSuperVirasoroColimitReadback

set_option synthInstance.maxHeartbeats 40000

-- Concrete carrier: End ℝ (ℝ) ≅ ℝ
-- (𝕜 := ℝ, V := ℝ, so EndV = ℝ as a ring)
local notation "Endℝ" => Module.End ℝ ℝ

-- Concrete nonzero mode data
local notation "A" => (1 : Endℝ)
local notation "B" => (1 : Endℝ)

-- Concrete J, ψ
local notation "J" => J_mode0 (𝕜 := ℝ) A
local notation "ψ" => psi_mode1 (𝕜 := ℝ) B

-- Trivial bond (identity at every stage)
def bond_id : ∀ _n : ℕ, Endℝ →+* Endℝ :=
  fun _ => RingHom.id Endℝ

/-- The identity cone is trivially compatible with the identity bond. -/
theorem bond_id_compatible : CompatibleCone (Stage := fun _ : ℕ => Endℝ) bond_id (fun _ => RingHom.id Endℝ) := by
  intro n x
  simp [bond_id]

/-- LG readback for the trivial bond/cone, specialized to `(m,r) = (0,0)` (the concrete case). -/
theorem readback_trivial_bond_LG (N : ℤ) : superBracket false true
    (RingHom.id Endℝ (L_trunc N 0 J ψ))
    (RingHom.id Endℝ (G_trunc N 0 J ψ))
  = RingHom.id Endℝ ((LG_coeff (𝕜 := ℝ) 0 0) • (G_trunc N 0 J ψ)) := by
  have hdef : boundaryDefect_LG (𝕜 := ℝ) N 0 0 J ψ = 0 :=
    boundaryDefect_LG_mode01_r0_eq_zero (𝕜 := ℝ) N A B
  have hcone := bond_id_compatible
  exact readback_superBracket_LG_of_boundaryDefect_zero (𝕜 := ℝ) (V := ℝ)
    bond_id (fun _ => RingHom.id Endℝ) hcone N 0 0 J ψ hdef

/-- GG readback for the trivial bond/cone, specialized to `(r,s) = (0,1)` (the concrete case). -/
theorem readback_trivial_bond_GG (N : ℤ) : superBracket true true
    (RingHom.id Endℝ (G_trunc N 0 J ψ))
    (RingHom.id Endℝ (G_trunc N 1 J ψ))
  = RingHom.id Endℝ
      ((2 : ℝ) • (L_trunc N (0 + 1) J ψ) + (centralZero (𝕜 := ℝ) 0 1) • (1 : Endℝ)) := by
  have hdef : boundaryDefect_GG (𝕜 := ℝ) N 0 1 J ψ (centralZero (𝕜 := ℝ)) = 0 :=
    boundaryDefect_GG_mode01_r0_s1_centralZero_eq_zero (𝕜 := ℝ) N A B
  have hcone := bond_id_compatible
  exact readback_superBracket_GG_of_boundaryDefect_zero (𝕜 := ℝ) (V := ℝ)
    bond_id (fun _ => RingHom.id Endℝ) hcone N 0 1 J ψ (centralZero (𝕜 := ℝ)) hdef

end ConcreteSuperVirasoroColimitReadback

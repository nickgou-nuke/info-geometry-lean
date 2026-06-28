import Mathlib
import InfoGeometry.Canonical.YangBaxterProof

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

noncomputable section

namespace FormalTheoryQuantumProofs

open InfoGeometry.Canonical.YangBaxterProof

/-- Finite `sl₂` readout: `[H,E₊] = 2E₊`. -/
lemma chapter1_quantum_sl2 : H * Ep - Ep * H = 2 • Ep :=
  comm_H_Ep

/-- The finite Fibonacci conjugation identity `F B F = R`. -/
lemma chapter2_quasitriangular : F * B * F = R :=
  F_B_F_eq_R

/-- The concrete finite Fibonacci Artin/Yang-Baxter matrix relation. -/
lemma chapter3_yang_baxter : R * B * R = B * R * B :=
  braid_relation

/-- Mathlib braided-category Yang-Baxter coherence. -/
lemma chapter4_braided_category
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X Y Z : C) :
    (α_ X Y Z).symm ≪≫
        whiskerRightIso (β_ X Y) Z ≪≫
          α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) ≪≫
            (α_ Y Z X).symm ≪≫ whiskerRightIso (β_ Y Z) X ≪≫ α_ Z Y X =
      whiskerLeftIso X (β_ Y Z) ≪≫
        (α_ X Z Y).symm ≪≫ whiskerRightIso (β_ X Z) Y ≪≫
          α_ Z X Y ≪≫ whiskerLeftIso Z (β_ X Y) := by
  simpa using CategoryTheory.BraidedCategory.yang_baxter_iso X Y Z

/-- Root-of-unity readout for the finite Fibonacci parameter. -/
lemma chapter5_roots_of_unity : q ^ 5 = -1 :=
  q_pow_five

/-- Fibonacci scalar relation for the `τ` channel. -/
lemma chapter6_fibonacci_mtc : τ ^ 2 + τ = 1 :=
  tau_sq_add_tau

/-- Explicit finite Fibonacci `F` matrix is involutive. -/
lemma chapter7_f_and_r : F * F = 1 :=
  F_sq

/-- Finite matrix hexagon shadow reduced to the Artin/Yang-Baxter owner. -/
lemma chapter8_hexagon : R * B * R = B * R * B :=
  braid_relation

#check chapter1_quantum_sl2
#check chapter2_quasitriangular
#check chapter3_yang_baxter
#check chapter4_braided_category
#check chapter5_roots_of_unity
#check chapter6_fibonacci_mtc
#check chapter7_f_and_r
#check chapter8_hexagon

end FormalTheoryQuantumProofs

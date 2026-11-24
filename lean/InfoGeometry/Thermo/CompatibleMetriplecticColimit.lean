/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.CompatibleEndomorphisms
import InfoGeometry.LinearAlgebra.CompatibleBilinearColimit
import InfoGeometry.Physics.FiniteMetriplecticDynamics

/-!
# Metriplectic rate laws on the native algebraic direct limit

The operators and pairing are constructed by the existing compatible-colimit
owners. Their adjoint and positivity laws descend from the stages, after which
the existing bilinear metriplectic theorems apply to the actual limit carrier.

The vectors `e` and `s` are explicit algebraic inputs. Interpreting them as
gradients, or the pairings as derivatives along a solution, requires additional
calculus witnesses. No dual/colimit identification, Riesz map, completion,
Poisson Jacobi identity, or foliation is asserted here.
-/

noncomputable section

namespace InfoGeometry.Thermo.CompatibleMetriplecticColimit

open InfoGeometry.Categorical.CompatibleEndomorphisms
open InfoGeometry.LinearAlgebra.CompatibleBilinearColimit

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
variable {H : ∀ ⦃i j : I⦄, i ≤ j → Type*}
variable [∀ i j (h : i ≤ j), FunLike (H h) (V i) (V j)]
variable [∀ i j (h : i ≤ j), LinearMapClass (H h) ℝ (V i) (V j)]
variable (f : ∀ i j (h : i ≤ j), H h) [DirectedSystem V (f · · ·)]
variable (B : ∀ i, LinearMap.BilinForm ℝ (V i))
variable (hB : ∀ i j h x y, B j (f i j h x) (f i j h y) = B i x y)
variable (L : ∀ i, Module.End ℝ (V i))
variable (hL : ∀ i j h x, L j (f i j h x) = f i j h (L i x))
variable (M : ∀ i, Module.End ℝ (V i))
variable (hM : ∀ i j h x, M j (f i j h x) = f i j h (M i x))

/-- Both actual operator summands agree with the finite-stage velocity. -/
-- theorem-class: transport
theorem velocity_of (i : I) (e s : V i) :
    liftEnd f L hL (DirectLimit.Module.of ℝ I V f i e) +
      liftEnd f M hM (DirectLimit.Module.of ℝ I V f i s) =
    DirectLimit.Module.of ℝ I V f i (L i e + M i s) := by
  rw [liftEnd_of, liftEnd_of, map_add]

/-- The algebraic energy rate vanishes for the constructed limit operators.
Only the energy degeneracy condition is needed for this law. -/
theorem energy_rate
    (hSymm : ∀ i, LinearMap.IsSymm (B i))
    (hSkew : ∀ i, (B i).IsSkewAdjoint (L i))
    (hSelf : ∀ i, (B i).IsSelfAdjoint (M i))
    (e s : _root_.DirectLimit V f) (he : liftEnd f M hM e = 0) :
    form f B hB e (liftEnd f L hL e + liftEnd f M hM s) = 0 := by
  exact Physics.energy_conserved
    (State := Unit) (Tangent := fun _ => _root_.DirectLimit V f)
    (fun _ => form f B hB)
    (fun _ x y => (form_isSymm f B hB hSymm).eq x y)
    (fun _ => liftEnd f L hL) (fun _ => liftEnd f M hM)
    (fun _ x y => by
      have h := ((form_isSkewAdjoint_iff f B hB L hL).2 hSkew) x y
      simpa only [Pi.neg_apply, map_neg] using h)
    (fun _ x y => ((form_isSelfAdjoint_iff f B hB M hM).2 hSelf) x y)
    (fun _ => e) (fun _ => s) (fun _ => he) Unit.unit

/-- Entropy degeneracy removes the reversible contribution on the colimit. -/
theorem entropy_rate_eq_dissipative
    (hSymm : ∀ i, LinearMap.IsSymm (B i))
    (hSkew : ∀ i, (B i).IsSkewAdjoint (L i))
    (e s : _root_.DirectLimit V f) (hs : liftEnd f L hL s = 0) :
    form f B hB s (liftEnd f L hL e + liftEnd f M hM s) =
      form f B hB s (liftEnd f M hM s) := by
  exact Physics.entropyRate_eq_onsager_quadratic
    (State := Unit) (Tangent := fun _ => _root_.DirectLimit V f)
    (fun _ => form f B hB)
    (fun _ x y => (form_isSymm f B hB hSymm).eq x y)
    (fun _ => liftEnd f L hL) (fun _ => liftEnd f M hM)
    (fun _ x y => by
      have h := ((form_isSkewAdjoint_iff f B hB L hL).2 hSkew) x y
      simpa only [Pi.neg_apply, map_neg] using h)
    (fun _ => e) (fun _ => s) (fun _ => hs) Unit.unit

/-- Nonnegative stage Onsager quadratics give a nonnegative limit entropy rate.
Positivity of the pairing itself is not assumed or substituted for this law. -/
theorem entropy_rate_nonneg
    (hSymm : ∀ i, LinearMap.IsSymm (B i))
    (hSkew : ∀ i, (B i).IsSkewAdjoint (L i))
    (hNonneg : ∀ i x, 0 ≤ B i x (M i x))
    (e s : _root_.DirectLimit V f) (hs : liftEnd f L hL s = 0) :
    0 ≤ form f B hB s (liftEnd f L hL e + liftEnd f M hM s) := by
  rw [entropy_rate_eq_dissipative f B hB L hL M hM hSymm hSkew e s hs]
  exact (form_apply_liftEnd_nonneg_iff f B hB M hM).2 hNonneg s

/-- A stage energy degeneracy equation suffices for conservation at its image. -/
-- theorem-class: transport
theorem energy_rate_of
    (hSymm : ∀ i, LinearMap.IsSymm (B i))
    (hSkew : ∀ i, (B i).IsSkewAdjoint (L i))
    (hSelf : ∀ i, (B i).IsSelfAdjoint (M i))
    (i : I) (e s : V i) (he : M i e = 0) :
    form f B hB (DirectLimit.Module.of ℝ I V f i e)
      (liftEnd f L hL (DirectLimit.Module.of ℝ I V f i e) +
        liftEnd f M hM (DirectLimit.Module.of ℝ I V f i s)) = 0 := by
  apply energy_rate f B hB L hL M hM hSymm hSkew hSelf
  rw [liftEnd_of, he, map_zero]

/-- A stage entropy degeneracy equation gives exact finite entropy production
at the corresponding limit vectors. -/
-- theorem-class: transport
theorem entropy_rate_of_eq
    (hSymm : ∀ i, LinearMap.IsSymm (B i))
    (hSkew : ∀ i, (B i).IsSkewAdjoint (L i))
    (i : I) (e s : V i) (hs : L i s = 0) :
    form f B hB (DirectLimit.Module.of ℝ I V f i s)
      (liftEnd f L hL (DirectLimit.Module.of ℝ I V f i e) +
        liftEnd f M hM (DirectLimit.Module.of ℝ I V f i s)) =
      B i s (M i s) := by
  have hs' : liftEnd f L hL (DirectLimit.Module.of ℝ I V f i s) = 0 := by
    rw [liftEnd_of, hs, map_zero]
  rw [entropy_rate_eq_dissipative f B hB L hL M hM hSymm hSkew _ _ hs',
    liftEnd_of, form_of]

/-- Only the selected stage entropy-production value needs to be nonnegative
for this particular pair of stage images. -/
-- theorem-class: transport
theorem entropy_rate_of_nonneg
    (hSymm : ∀ i, LinearMap.IsSymm (B i))
    (hSkew : ∀ i, (B i).IsSkewAdjoint (L i))
    (i : I) (e s : V i) (hs : L i s = 0) (hNonneg : 0 ≤ B i s (M i s)) :
    0 ≤ form f B hB (DirectLimit.Module.of ℝ I V f i s)
      (liftEnd f L hL (DirectLimit.Module.of ℝ I V f i e) +
        liftEnd f M hM (DirectLimit.Module.of ℝ I V f i s)) := by
  rw [entropy_rate_of_eq f B hB L hL M hM hSymm hSkew i e s hs]
  exact hNonneg

end InfoGeometry.Thermo.CompatibleMetriplecticColimit

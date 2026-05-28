import InfoGeometry.Clifford.ConformalLift55
import InfoGeometry.Canonical.DrazinChiralLightconeBoundary

/-!
# InfoGeometry.Canonical.DrazinCl55LightconeAlignment

Finite algebraic alignment of the Drazin defect lane with the real split
`Cl(5,5)` lightcone lane.

This file proves only the concrete algebraic joints:

* the repo-owned split `Cl(5,5)` stage contains a conformal null pair;
* that pair has square-zero/null generators and unit anticommutator;
* finite-stage ring homomorphisms transport those identities;
* finite chains of split-`Cl(5,5)` endomorphisms preserve the same null-pair
  relations.

This is only finite algebraic data: no analytic completion, limit passage, or
bulk-boundary reconstruction is asserted here.
-/

namespace InfoGeometry.Canonical.DrazinCl55LightconeAlignment

open InfoGeometry.Clifford.ConformalLift55

/-- The repo-owned split `Cl(5,5)` stage contains a conformal null pair. -/
theorem cl55_conformal_null_pair_exists :
    ∃ u v : Cl55, u ^ 2 = 0 ∧ v ^ 2 = 0 ∧ u * v + v * u = 1 := by
  rcases conformalNullPair_exists with ⟨P⟩
  exact ⟨P.u, P.v, P.u_square, P.v_square, P.anticomm⟩

/--
Any finite-stage ring homomorphism out of `Cl(5,5)` transports a chosen
conformal null pair to a square-zero pair with unit anticommutator.
-/
theorem ringHom_transports_cl55_conformal_null_pair
    {B : Type*} [Ring B]
    (f : Cl55 →+* B)
    {u v : Cl55}
    (hu : u ^ 2 = 0)
    (hv : v ^ 2 = 0)
    (huv : u * v + v * u = 1) :
    f u ^ 2 = 0 ∧ f v ^ 2 = 0 ∧ f u * f v + f v * f u = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [pow_two] using congrArg f hu
  · simpa [pow_two] using congrArg f hv
  · simpa using
      InfoGeometry.Canonical.FiniteInvariantTransport.ringHom_preserves_anticommutator
        f huv

/--
Existential transport of the repo-owned `Cl(5,5)` conformal null pair along a
finite-stage ring homomorphism.
-/
theorem ringHom_image_contains_conformal_null_pair
    {B : Type*} [Ring B]
    (f : Cl55 →+* B) :
    ∃ u' v' : B, u' ^ 2 = 0 ∧ v' ^ 2 = 0 ∧ u' * v' + v' * u' = 1 := by
  rcases cl55_conformal_null_pair_exists with ⟨u, v, hu, hv, huv⟩
  exact ⟨f u, f v, ringHom_transports_cl55_conformal_null_pair f hu hv huv⟩

/-- Ring-hom chains preserve the unit element. -/
theorem chainApply_ringHom_one
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A) (n k : Nat) :
    InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k (1 : A) = 1 := by
  induction k with
  | zero =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply]
  | succ k ih =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply, ih]

/--
Finite chains of split-`Cl(5,5)` endomorphisms preserve the conformal null-pair
relations.
-/
theorem cl55_conformal_null_pair_preserved_along_ringHom_chain
    (φ : Nat → Cl55 →+* Cl55)
    (n k : Nat) {u v : Cl55}
    (hu : u ^ 2 = 0)
    (hv : v ^ 2 = 0)
    (huv : u * v + v * u = 1) :
    let uₖ := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k u
    let vₖ := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k v
    uₖ ^ 2 = 0 ∧ vₖ ^ 2 = 0 ∧ uₖ * vₖ + vₖ * uₖ = 1 := by
  intro uₖ vₖ
  refine ⟨?_, ?_, ?_⟩
  · simpa [uₖ, pow_two] using
      InfoGeometry.Canonical.FiniteInvariantTransport.square_zero_preserved_along_ringHom_chain
        φ n k (by simpa [pow_two] using hu)
  · simpa [vₖ, pow_two] using
      InfoGeometry.Canonical.FiniteInvariantTransport.square_zero_preserved_along_ringHom_chain
        φ n k (by simpa [pow_two] using hv)
  · have hchain :=
      InfoGeometry.Canonical.FiniteInvariantTransport.anticommutator_preserved_along_ringHom_chain
        φ n k huv
    have hone :
        InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
          (fun i a => φ i a) n k (1 : Cl55) = 1 :=
      chainApply_ringHom_one φ n k
    simpa [uₖ, vₖ, hone] using hchain

/--
A finite-stage ring homomorphism transports the Drazin regular/defect projector
packet and the Drazin-power annihilation identities.
-/
theorem ringHom_transports_drazin_defect_packet
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    let P := InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b
    let Q := InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b
    f Q * f Q = f Q ∧
      f P * f Q = 0 ∧
      f Q * f P = 0 ∧
      f P + f Q = 1 ∧
      (f a) ^ m * f Q = 0 ∧
      f Q * (f a) ^ m = 0 := by
  intro P Q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Q] using congrArg f
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent hD)
  · simpa [P, Q] using congrArg f
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_mul_complementaryProjection hD)
  · simpa [P, Q] using congrArg f
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_projection hD)
  · simpa [P, Q] using congrArg f
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_add_complementaryProjection
        (a := a) (b := b))
  · have h := congrArg f
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_mul_complementaryProjection_eq_zero hD)
    simpa [Q, map_pow] using h
  · have h := congrArg f
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_power_eq_zero hD)
    simpa [Q, map_pow] using h

/--
The transported finite alignment theorem: a target finite stage receives both a
transported `Cl(5,5)` conformal null pair and a transported Drazin defect packet.
-/
theorem ringHom_transports_cl55_drazin_finite_alignment
    {R S B : Type*} [Ring R] [Ring S] [Ring B]
    (g : Cl55 →+* B) (f : R →+* S)
    {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    (∃ u' v' : B, u' ^ 2 = 0 ∧ v' ^ 2 = 0 ∧ u' * v' + v' * u' = 1) ∧
      (let P := InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b
       let Q := InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b
       f Q * f Q = f Q ∧
        f P * f Q = 0 ∧
        f Q * f P = 0 ∧
        f P + f Q = 1 ∧
        (f a) ^ m * f Q = 0 ∧
        f Q * (f a) ^ m = 0) := by
  exact ⟨ringHom_image_contains_conformal_null_pair g,
    ringHom_transports_drazin_defect_packet f hD⟩

/--
The split `Cl(5,5)` lightcone lane and Drazin defect lane align at the finite
algebraic level: `Cl(5,5)` supplies a conformal null pair, while the Drazin
complement supplies an idempotent defect projector annihilated by the Drazin
power.
-/
theorem cl55_drazin_defect_finite_alignment
    {R : Type*} [Ring R] {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    (∃ u v : Cl55, u ^ 2 = 0 ∧ v ^ 2 = 0 ∧ u * v + v * u = 1) ∧
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b *
          InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b =
        InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b ∧
      a ^ m * InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b = 0 ∧
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b * a ^ m = 0 := by
  exact
    ⟨cl55_conformal_null_pair_exists,
     InfoGeometry.Canonical.DrazinChiralLightconeBoundary.drazin_defect_projector_idempotent hD,
     (InfoGeometry.Canonical.DrazinChiralLightconeBoundary.drazin_power_annihilates_defect_lane hD).1,
     (InfoGeometry.Canonical.DrazinChiralLightconeBoundary.drazin_power_annihilates_defect_lane hD).2⟩

end InfoGeometry.Canonical.DrazinCl55LightconeAlignment

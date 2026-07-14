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

/-- Ring-hom chains preserve addition. -/
theorem chainApply_ringHom_add
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A) (n k : Nat) (x y : A) :
    InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k (x + y) =
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k x +
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k y := by
  induction k with
  | zero =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply]
  | succ k ih =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply, ih]

/-- Ring-hom chains preserve multiplication. -/
theorem chainApply_ringHom_mul
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A) (n k : Nat) (x y : A) :
    InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k (x * y) =
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k x *
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k y := by
  induction k with
  | zero =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply]
  | succ k ih =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply, ih]

/-- Ring-hom chains preserve powers. -/
theorem chainApply_ringHom_pow
    {A : Type*} [Semiring A]
    (φ : Nat → A →+* A) (n k m : Nat) (x : A) :
    InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k (x ^ m) =
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i z => φ i z) n k x ^ m := by
  induction k with
  | zero =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply]
  | succ k ih =>
      simp [InfoGeometry.Canonical.FiniteInvariantTransport.chainApply, ih, map_pow]

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

/-- Ring homomorphisms preserve idempotence of the Drazin complementary projector. -/
theorem ringHom_drazin_complementaryProjection_idempotent
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
      * f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
      =
    f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b) := by
  simpa using congrArg f
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent hD)

/-- Ring homomorphisms preserve left orthogonality of Drazin regular and defect projectors. -/
theorem ringHom_drazin_projection_mul_complementaryProjection_eq_zero
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b)
      * f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b) = 0 := by
  simpa using congrArg f
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_mul_complementaryProjection hD)

/-- Ring homomorphisms preserve right orthogonality of Drazin regular and defect projectors. -/
theorem ringHom_drazin_complementaryProjection_mul_projection_eq_zero
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
      * f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b) = 0 := by
  simpa using congrArg f
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_projection hD)

/-- Ring homomorphisms preserve the Drazin projector partition of unity. -/
theorem ringHom_drazin_projection_add_complementaryProjection_eq_one
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (a b : R) :
    f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b)
      + f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
      = 1 := by
  simpa using congrArg f
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_add_complementaryProjection
      (a := a) (b := b))

/-- Ring homomorphisms preserve Drazin power annihilation on the left. -/
theorem ringHom_drazin_power_mul_complementaryProjection_eq_zero
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    (f a) ^ m * f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
      = 0 := by
  have h := congrArg f
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_mul_complementaryProjection_eq_zero hD)
  simpa [map_pow] using h

/-- Ring homomorphisms preserve Drazin power annihilation on the right. -/
theorem ringHom_drazin_complementaryProjection_mul_power_eq_zero
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    f (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b) * (f a) ^ m
      = 0 := by
  have h := congrArg f
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_power_eq_zero hD)
  simpa [map_pow] using h

/--
The transported finite alignment theorem: a target finite stage receives both a
transported `Cl(5,5)` conformal null pair and transported Drazin defect laws.
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
  refine ⟨ringHom_image_contains_conformal_null_pair g, ?_⟩
  dsimp
  exact
    ⟨ringHom_drazin_complementaryProjection_idempotent f hD,
      ringHom_drazin_projection_mul_complementaryProjection_eq_zero f hD,
      ringHom_drazin_complementaryProjection_mul_projection_eq_zero f hD,
      ringHom_drazin_projection_add_complementaryProjection_eq_one f a b,
      ringHom_drazin_power_mul_complementaryProjection_eq_zero f hD,
      ringHom_drazin_complementaryProjection_mul_power_eq_zero f hD⟩

/-- Ring-hom chains preserve idempotence of the Drazin complementary projector. -/
theorem chainApply_drazin_complementaryProjection_idempotent
    {R : Type*} [Ring R]
    (φ : Nat → R →+* R) (n k : Nat)
    {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    let Q := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
    Q * Q = Q := by
  intro Q
  simpa [Q] using
    InfoGeometry.Canonical.FiniteInvariantTransport.idempotent_preserved_along_ringHom_chain
      φ n k
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent hD)

/-- Ring-hom chains preserve left orthogonality of Drazin regular and defect projectors. -/
theorem chainApply_drazin_projection_mul_complementaryProjection_eq_zero
    {R : Type*} [Ring R]
    (φ : Nat → R →+* R) (n k : Nat)
    {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    let P := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b)
    let Q := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
    P * Q = 0 := by
  intro P Q
  simpa [P, Q] using
    InfoGeometry.Canonical.FiniteInvariantTransport.orthogonal_preserved_along_ringHom_chain
      φ n k
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_mul_complementaryProjection hD)

/-- Ring-hom chains preserve right orthogonality of Drazin regular and defect projectors. -/
theorem chainApply_drazin_complementaryProjection_mul_projection_eq_zero
    {R : Type*} [Ring R]
    (φ : Nat → R →+* R) (n k : Nat)
    {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    let P := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b)
    let Q := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
    Q * P = 0 := by
  intro P Q
  simpa [P, Q] using
    InfoGeometry.Canonical.FiniteInvariantTransport.orthogonal_preserved_along_ringHom_chain
      φ n k
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_projection hD)

/-- Ring-hom chains preserve the Drazin projector partition of unity. -/
theorem chainApply_drazin_projection_add_complementaryProjection_eq_one
    {R : Type*} [Ring R]
    (φ : Nat → R →+* R) (n k : Nat) (a b : R) :
    let P := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection a b)
    let Q := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
    P + Q = 1 := by
  intro P Q
  have hsum := congrArg
    (InfoGeometry.Canonical.FiniteInvariantTransport.chainApply (fun i x => φ i x) n k)
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_add_complementaryProjection
      (a := a) (b := b))
  have hone :
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i x => φ i x) n k (1 : R) = 1 :=
    chainApply_ringHom_one φ n k
  simpa [P, Q, chainApply_ringHom_add φ n k, hone] using hsum

/-- Ring-hom chains preserve Drazin power annihilation on the left. -/
theorem chainApply_drazin_power_mul_complementaryProjection_eq_zero
    {R : Type*} [Ring R]
    (φ : Nat → R →+* R) (n k : Nat)
    {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    let Q := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
    let aₖ := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k a
    aₖ ^ m * Q = 0 := by
  intro Q aₖ
  have hann :=
    InfoGeometry.Canonical.FiniteInvariantTransport.orthogonal_preserved_along_ringHom_chain
      φ n k
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_mul_complementaryProjection_eq_zero hD)
  have hpowa :
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i x => φ i x) n k (a ^ m) = aₖ ^ m := by
    simpa [aₖ] using chainApply_ringHom_pow φ n k m a
  simpa [Q, hpowa] using hann

/-- Ring-hom chains preserve Drazin power annihilation on the right. -/
theorem chainApply_drazin_complementaryProjection_mul_power_eq_zero
    {R : Type*} [Ring R]
    (φ : Nat → R →+* R) (n k : Nat)
    {a b : R} {m : ℕ}
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b m) :
    let Q := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k
        (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection a b)
    let aₖ := InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
      (fun i x => φ i x) n k a
    Q * aₖ ^ m = 0 := by
  intro Q aₖ
  have hann :=
    InfoGeometry.Canonical.FiniteInvariantTransport.orthogonal_preserved_along_ringHom_chain
      φ n k
      (InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_power_eq_zero hD)
  have hpowa :
      InfoGeometry.Canonical.FiniteInvariantTransport.chainApply
        (fun i x => φ i x) n k (a ^ m) = aₖ ^ m := by
    simpa [aₖ] using chainApply_ringHom_pow φ n k m a
  simpa [Q, hpowa] using hann

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

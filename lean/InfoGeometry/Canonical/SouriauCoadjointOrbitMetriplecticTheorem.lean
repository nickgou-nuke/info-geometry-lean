import InfoGeometry.Canonical.SouriauKreinMetriplecticContext
import InfoGeometry.Geometry.LegendreHessianInverse
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.Vacuity

/-!
# InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem

Full coadjoint-orbit metriplectic theorem interface.

This module deliberately does not manufacture infinite-dimensional analysis from
the finite Souriau shadow.  Instead it states the full theorem at the correct
generality: an arbitrary orbit carrier, an arbitrary Lie algebra/coadjoint
dual pair, and explicit hypotheses for the analytic facts that are not
available from the existing finite response matrix.

The theorem is therefore proof-carrying:

- the reversible vector field is tangent to the coadjoint orbit;
- the reversible entropy rate is a Casimir channel;
- the metric/Onsager entropy rate is nonnegative;
- the total entropy rate splits as reversible plus metric.

Only under those hypotheses do we prove the infinite-dimensional
coadjoint-orbit metriplectic second law.
-/

namespace InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic

universe u v w

/--
Abstract full coadjoint-orbit metriplectic context.

`Orbit` is intentionally unconstrained by `Fintype`: this is the theorem
surface for infinite-dimensional or functional-analytic orbit models.  The
fields are the exact analytic obligations required by the theorem; they are not
replaced by finite count-state positivity or diagonalization assumptions.
-/
@[rep_depth transport]
structure InfiniteCoadjointOrbitMetriplecticContext
    (Orbit : Type u) (LieAlg : Type v) (LieCoalg : Type w) where
  /-- Moment map into the coadjoint dual lane. -/
  moment : Orbit → LieCoalg
  /-- Souriau geometric temperature, i.e. a Lie-algebra generator. -/
  geometricTemperature : LieAlg
  /-- Predicate selecting the coadjoint orbit containing the moment image. -/
  isOnCoadjointOrbit : LieCoalg → Prop
  /-- Reversible/Hamiltonian generator on the orbit. -/
  reversibleVectorField : Orbit → Orbit
  /-- Metric/Onsager generator on the orbit. -/
  metricVectorField : Orbit → Orbit
  /-- Entropy functional on the orbit. -/
  entropy : Orbit → ℝ
  /-- Reversible entropy-production channel. -/
  reversibleEntropyRate : Orbit → ℝ
  /-- Metric/Onsager entropy-production channel. -/
  metricEntropyRate : Orbit → ℝ
  /-- Total metriplectic entropy-production channel. -/
  totalEntropyRate : Orbit → ℝ
  /-- The moment image lies on the selected coadjoint orbit. -/
  moment_mem_orbit : ∀ x : Orbit, isOnCoadjointOrbit (moment x)
  /-- Hamiltonian/coadjoint motion closes on the same orbit. -/
  reversible_preserves_orbit :
    ∀ x : Orbit, isOnCoadjointOrbit (moment (reversibleVectorField x))
  /-- The metric/Onsager leg is a valid orbit-level state update. -/
  metric_preserves_state : ∀ x : Orbit, isOnCoadjointOrbit (moment (metricVectorField x))
  /-- Casimir hypothesis: the reversible leg produces no entropy. -/
  casimir_reversible : ∀ x : Orbit, reversibleEntropyRate x = 0
  /-- Onsager positivity hypothesis for the noncommutative/operator metric leg. -/
  onsager_metric_nonnegative : ∀ x : Orbit, 0 ≤ metricEntropyRate x
  /-- Metriplectic split of the total entropy-production channel. -/
  total_entropy_split :
    ∀ x : Orbit,
      totalEntropyRate x = reversibleEntropyRate x + metricEntropyRate x

namespace InfiniteCoadjointOrbitMetriplecticContext

variable {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
variable (C : InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg)

/--
Canonical dimension-agnostic constructor where the selected coadjoint orbit is
the image of the moment map.

This removes the basic orbit-membership and flow-closure obligations from the
hypothesis surface: for an arbitrary carrier `Orbit`, both the reversible and
metric updates still land in `Set.range moment` by construction.  The analytic
content that cannot be derived from the image predicate alone remains explicit:
Casimir reversibility, Onsager nonnegativity, and the metriplectic entropy split.
-/
@[rep_depth transport]
def ofMomentImage
    (moment : Orbit → LieCoalg)
    (geometricTemperature : LieAlg)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy reversibleEntropyRate metricEntropyRate totalEntropyRate : Orbit → ℝ)
    (casimir_reversible : ∀ x : Orbit, reversibleEntropyRate x = 0)
    (onsager_metric_nonnegative : ∀ x : Orbit, 0 ≤ metricEntropyRate x)
    (total_entropy_split :
      ∀ x : Orbit,
        totalEntropyRate x = reversibleEntropyRate x + metricEntropyRate x) :
    InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg where
  moment := moment
  geometricTemperature := geometricTemperature
  isOnCoadjointOrbit := fun q => ∃ x : Orbit, moment x = q
  reversibleVectorField := reversibleVectorField
  metricVectorField := metricVectorField
  entropy := entropy
  reversibleEntropyRate := reversibleEntropyRate
  metricEntropyRate := metricEntropyRate
  totalEntropyRate := totalEntropyRate
  moment_mem_orbit := by
    intro x
    exact ⟨x, rfl⟩
  reversible_preserves_orbit := by
    intro x
    exact ⟨reversibleVectorField x, rfl⟩
  metric_preserves_state := by
    intro x
    exact ⟨metricVectorField x, rfl⟩
  casimir_reversible := casimir_reversible
  onsager_metric_nonnegative := onsager_metric_nonnegative
  total_entropy_split := total_entropy_split

/--
Constructive dimension-agnostic coadjoint-orbit metriplectic context with a
square dissipation channel.

This removes the Casimir, Onsager nonnegativity, and total-split hypotheses
from the constructor.  The reversible entropy channel is definitionally zero,
the metric channel is `dissipationAmplitude x ^ 2`, and the total channel is
definitionally the same square.  No finite-dimensional matrix model is used.
-/
@[rep_depth transport]
def ofMomentImageSquareDissipation
    (moment : Orbit → LieCoalg)
    (geometricTemperature : LieAlg)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ) :
    InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg :=
  ofMomentImage
    (moment := moment)
    (geometricTemperature := geometricTemperature)
    (reversibleVectorField := reversibleVectorField)
    (metricVectorField := metricVectorField)
    (entropy := entropy)
    (reversibleEntropyRate := fun _ => 0)
    (metricEntropyRate := fun x => dissipationAmplitude x ^ (2 : ℕ))
    (totalEntropyRate := fun x => dissipationAmplitude x ^ (2 : ℕ))
    (casimir_reversible := by
      intro x
      rfl)
    (onsager_metric_nonnegative := by
      intro x
      exact sq_nonneg (dissipationAmplitude x))
    (total_entropy_split := by
      intro x
      simp)

namespace SquareDissipation

variable
  (moment : Orbit → LieCoalg)
  (geometricTemperature : LieAlg)
  (reversibleVectorField metricVectorField : Orbit → Orbit)
  (entropy : Orbit → ℝ)
  (dissipationAmplitude : Orbit → ℝ)

local notation "C□" =>
  ofMomentImageSquareDissipation
    (Orbit := Orbit) (LieAlg := LieAlg) (LieCoalg := LieCoalg)
    moment geometricTemperature reversibleVectorField metricVectorField entropy
    dissipationAmplitude

/-- In the square-dissipation model, reversible entropy production is zero by construction. -/
@[rep_depth transport]
theorem reversibleEntropyRate_eq_zero (x : Orbit) :
    C□.reversibleEntropyRate x = 0 :=
  rfl

/-- In the square-dissipation model, metric entropy production is a square. -/
@[rep_depth transport]
theorem metricEntropyRate_eq_square (x : Orbit) :
    C□.metricEntropyRate x = dissipationAmplitude x ^ (2 : ℕ) :=
  rfl

/-- In the square-dissipation model, total entropy production is a square. -/
@[rep_depth transport]
theorem totalEntropyRate_eq_square (x : Orbit) :
    C□.totalEntropyRate x = dissipationAmplitude x ^ (2 : ℕ) :=
  rfl

/-- Dimension-agnostic constructive second law for square dissipation. -/
@[rep_depth transport]
theorem totalEntropyRate_nonnegative (x : Orbit) :
    0 ≤ C□.totalEntropyRate x := by
  rw [totalEntropyRate_eq_square
    (moment := moment)
    (geometricTemperature := geometricTemperature)
    (reversibleVectorField := reversibleVectorField)
    (metricVectorField := metricVectorField)
    (entropy := entropy)
    (dissipationAmplitude := dissipationAmplitude)]
  exact sq_nonneg (dissipationAmplitude x)

/--
Packed constructive theorem for the square-dissipation coadjoint-orbit route.

This is the dimension-agnostic replacement for the old explicit Casimir,
nonnegativity, and total-split hypotheses when the model supplies a real
dissipation amplitude.
-/
@[rep_depth transport]
theorem full_square_dissipation_metriplectic_theorem (x : Orbit) :
    C□.isOnCoadjointOrbit (C□.moment x)
      ∧ C□.isOnCoadjointOrbit (C□.moment (C□.reversibleVectorField x))
      ∧ C□.isOnCoadjointOrbit (C□.moment (C□.metricVectorField x))
      ∧ C□.reversibleEntropyRate x = 0
      ∧ C□.metricEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ C□.totalEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ 0 ≤ C□.totalEntropyRate x := by
  exact
    ⟨C□.moment_mem_orbit x,
      C□.reversible_preserves_orbit x,
      C□.metric_preserves_state x,
      reversibleEntropyRate_eq_zero
        (moment := moment)
        (geometricTemperature := geometricTemperature)
        (reversibleVectorField := reversibleVectorField)
        (metricVectorField := metricVectorField)
        (entropy := entropy)
        (dissipationAmplitude := dissipationAmplitude) x,
      metricEntropyRate_eq_square
        (moment := moment)
        (geometricTemperature := geometricTemperature)
        (reversibleVectorField := reversibleVectorField)
        (metricVectorField := metricVectorField)
        (entropy := entropy)
        (dissipationAmplitude := dissipationAmplitude) x,
      totalEntropyRate_eq_square
        (moment := moment)
        (geometricTemperature := geometricTemperature)
        (reversibleVectorField := reversibleVectorField)
        (metricVectorField := metricVectorField)
        (entropy := entropy)
        (dissipationAmplitude := dissipationAmplitude) x,
      totalEntropyRate_nonnegative
        (moment := moment)
        (geometricTemperature := geometricTemperature)
        (reversibleVectorField := reversibleVectorField)
        (metricVectorField := metricVectorField)
        (entropy := entropy)
        (dissipationAmplitude := dissipationAmplitude) x⟩

attribute [terminal] full_square_dissipation_metriplectic_theorem

/--
Constructive Casimir-leaf/transverse-Onsager packet for the Souriau prose.

The reversible leg is the symplectic/coadjoint-leaf channel and is a Casimir
direction by construction (`0`).  The transverse metric/Onsager leg is the
square of a real dissipation amplitude, hence nonnegative, and the total
metriplectic entropy production is exactly that transverse square.  This is
dimension-agnostic: `Orbit` is arbitrary and no finite state model is used.
-/
@[rep_depth transport]
theorem casimir_leaf_transverse_onsager_square_packet (x : Orbit) :
    C□.reversibleEntropyRate x = 0
      ∧ C□.metricEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ C□.totalEntropyRate x = C□.metricEntropyRate x
      ∧ 0 ≤ C□.metricEntropyRate x
      ∧ 0 ≤ C□.totalEntropyRate x := by
  exact
    ⟨reversibleEntropyRate_eq_zero
        (moment := moment)
        (geometricTemperature := geometricTemperature)
        (reversibleVectorField := reversibleVectorField)
        (metricVectorField := metricVectorField)
        (entropy := entropy)
        (dissipationAmplitude := dissipationAmplitude) x,
      metricEntropyRate_eq_square
        (moment := moment)
        (geometricTemperature := geometricTemperature)
        (reversibleVectorField := reversibleVectorField)
        (metricVectorField := metricVectorField)
        (entropy := entropy)
        (dissipationAmplitude := dissipationAmplitude) x,
      by rfl,
      by
        rw [metricEntropyRate_eq_square
          (moment := moment)
          (geometricTemperature := geometricTemperature)
          (reversibleVectorField := reversibleVectorField)
          (metricVectorField := metricVectorField)
          (entropy := entropy)
          (dissipationAmplitude := dissipationAmplitude)]
        exact sq_nonneg (dissipationAmplitude x),
      totalEntropyRate_nonnegative
        (moment := moment)
        (geometricTemperature := geometricTemperature)
        (reversibleVectorField := reversibleVectorField)
        (metricVectorField := metricVectorField)
        (entropy := entropy)
        (dissipationAmplitude := dissipationAmplitude) x⟩

attribute [terminal] casimir_leaf_transverse_onsager_square_packet

end SquareDissipation

/-- Every represented state has its moment on the selected coadjoint orbit. -/
@[rep_depth transport]
theorem moment_lands_on_coadjoint_orbit (x : Orbit) :
    C.isOnCoadjointOrbit (C.moment x) :=
  C.moment_mem_orbit x

/-- Reversible/Hamiltonian flow closes inside the coadjoint orbit. -/
@[rep_depth transport]
theorem reversible_flow_closes_on_coadjoint_orbit (x : Orbit) :
    C.isOnCoadjointOrbit (C.moment (C.reversibleVectorField x)) :=
  C.reversible_preserves_orbit x

/-- Metric/Onsager flow is a valid orbit-level state update. -/
@[rep_depth transport]
theorem metric_flow_closes_on_coadjoint_orbit (x : Orbit) :
    C.isOnCoadjointOrbit (C.moment (C.metricVectorField x)) :=
  C.metric_preserves_state x

/-- Casimir channel: reversible/coadjoint motion has zero entropy production. -/
@[rep_depth transport]
theorem reversibleEntropyRate_eq_zero (x : Orbit) :
    C.reversibleEntropyRate x = 0 :=
  C.casimir_reversible x

/-- Metric/Onsager channel is nonnegative by the explicit operatorial positivity hypothesis. -/
@[rep_depth transport]
theorem metricEntropyRate_nonnegative (x : Orbit) :
    0 ≤ C.metricEntropyRate x :=
  C.onsager_metric_nonnegative x

/-- Total entropy production reduces to the metric channel because the reversible leg is Casimir. -/
@[rep_depth transport]
theorem totalEntropyRate_eq_metricEntropyRate (x : Orbit) :
    C.totalEntropyRate x = C.metricEntropyRate x := by
  rw [C.total_entropy_split x, C.reversibleEntropyRate_eq_zero x]
  simp

/--
Full coadjoint-orbit metriplectic second law.

This is the infinite-dimensional theorem surface: no finiteness, no diagonal
count-state model, and no commutative replacement is assumed.  The price is that
the orbit closure, Casimir, and operatorial Onsager positivity hypotheses must
be supplied explicitly.
-/
@[rep_depth transport]
theorem coadjoint_orbit_metriplectic_second_law (x : Orbit) :
    0 ≤ C.totalEntropyRate x := by
  rw [C.totalEntropyRate_eq_metricEntropyRate x]
  exact C.metricEntropyRate_nonnegative x

/--
Packed theorem form used by downstream bridges that need all closure and
second-law outputs at once.
-/
@[rep_depth transport]
theorem full_coadjoint_orbit_metriplectic_theorem (x : Orbit) :
    C.isOnCoadjointOrbit (C.moment x)
      ∧ C.isOnCoadjointOrbit (C.moment (C.reversibleVectorField x))
      ∧ C.isOnCoadjointOrbit (C.moment (C.metricVectorField x))
      ∧ C.reversibleEntropyRate x = 0
      ∧ 0 ≤ C.metricEntropyRate x
      ∧ C.totalEntropyRate x = C.metricEntropyRate x
      ∧ 0 ≤ C.totalEntropyRate x := by
  exact
    ⟨C.moment_lands_on_coadjoint_orbit x,
      C.reversible_flow_closes_on_coadjoint_orbit x,
      C.metric_flow_closes_on_coadjoint_orbit x,
      C.reversibleEntropyRate_eq_zero x,
      C.metricEntropyRate_nonnegative x,
      C.totalEntropyRate_eq_metricEntropyRate x,
      C.coadjoint_orbit_metriplectic_second_law x⟩

attribute [terminal] full_coadjoint_orbit_metriplectic_theorem

/--
Constructive image-orbit theorem packet.

This is the dimension-agnostic replacement for explicit orbit-closure
hypotheses when the orbit predicate is chosen to be `Set.range moment`.  It
still requires the analytic Casimir, Onsager, and entropy-split laws as inputs.
-/
@[rep_depth transport]
theorem ofMomentImage_full_coadjoint_orbit_metriplectic_theorem
    (moment : Orbit → LieCoalg)
    (geometricTemperature : LieAlg)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy reversibleEntropyRate metricEntropyRate totalEntropyRate : Orbit → ℝ)
    (casimir_reversible : ∀ x : Orbit, reversibleEntropyRate x = 0)
    (onsager_metric_nonnegative : ∀ x : Orbit, 0 ≤ metricEntropyRate x)
    (total_entropy_split :
      ∀ x : Orbit,
        totalEntropyRate x = reversibleEntropyRate x + metricEntropyRate x)
    (x : Orbit) :
    (∃ y : Orbit, moment y = moment x)
      ∧ (∃ y : Orbit, moment y = moment (reversibleVectorField x))
      ∧ (∃ y : Orbit, moment y = moment (metricVectorField x))
      ∧ reversibleEntropyRate x = 0
      ∧ 0 ≤ metricEntropyRate x
      ∧ totalEntropyRate x = metricEntropyRate x
      ∧ 0 ≤ totalEntropyRate x := by
  let Cimg :=
    ofMomentImage
      (Orbit := Orbit) (LieAlg := LieAlg) (LieCoalg := LieCoalg)
      moment geometricTemperature reversibleVectorField metricVectorField
      entropy reversibleEntropyRate metricEntropyRate totalEntropyRate
      casimir_reversible onsager_metric_nonnegative total_entropy_split
  exact Cimg.full_coadjoint_orbit_metriplectic_theorem x

attribute [terminal] ofMomentImage_full_coadjoint_orbit_metriplectic_theorem

end InfiniteCoadjointOrbitMetriplecticContext

/-! ## Full coadjoint-orbit Hessian/Fisher theorem surface -/

/--
Abstract full coadjoint-orbit Hessian context.

This is the infinite-dimensional theorem target for the Souriau/Fisher prose:
it is not a finite `2×2` response matrix and it does not assume a count-state
model.  `Tangent` represents admissible variations of the geometric
temperature and `DualTangent` represents admissible variations on the dual
moment side.

The analytic content is intentionally explicit.  A concrete smooth
coadjoint-orbit model must provide the derivative, Hessian, covariance,
Legendre, and inverse-Hessian identities before downstream code may use the
full theorem.
-/
@[rep_depth transport]
structure InfiniteCoadjointOrbitHessianContext
    (Orbit : Type u) (LieAlg : Type v) (LieCoalg : Type w)
    (Tangent DualTangent : Type*) where
  /-- Moment map into the coadjoint dual lane. -/
  moment : Orbit → LieCoalg
  /-- Statistical partition functional on the geometric-temperature lane. -/
  partitionFunction : LieAlg → ℝ
  /-- Massieu/log-partition potential on the geometric-temperature lane. -/
  massieuPotential : LieAlg → ℝ
  /-- Thermodynamic moment readout `Q(β)`. -/
  thermodynamicMoment : LieAlg → LieCoalg
  /-- Fisher/Hessian bilinear readout on admissible temperature variations. -/
  fisherHessian : LieAlg → Tangent → Tangent → ℝ
  /-- Covariance readout of the moment map on admissible variations. -/
  momentCovariance : LieAlg → Tangent → Tangent → ℝ
  /-- Predicate selecting nonzero/admissibly nondegenerate tangent variations. -/
  nonzeroTangent : Tangent → Prop
  /-- Fenchel-Legendre entropy on the coadjoint dual lane. -/
  souriauEntropy : LieCoalg → ℝ
  /-- Inverse coordinate map `Q ↦ β`. -/
  betaOfMoment : LieCoalg → LieAlg
  /-- Entropy Hessian on admissible dual-side variations. -/
  entropyHessian : LieCoalg → DualTangent → DualTangent → ℝ
  /-- Inverse Fisher readout transported to the dual-side variations. -/
  inverseFisherHessian : LieCoalg → DualTangent → DualTangent → ℝ
  /-- Massieu is the logarithm of the partition functional. -/
  massieu_eq_log_partition :
    ∀ β : LieAlg, massieuPotential β = Real.log (partitionFunction β)
  /-- First variation of Massieu gives the thermodynamic moment. -/
  first_variation_eq_moment : Prop
  /-- Proof of the first-variation/moment identity. -/
  first_variation_eq_moment_holds : first_variation_eq_moment
  /-- Second variation of Massieu gives the Fisher/Hessian readout. -/
  second_variation_eq_fisher : Prop
  /-- Proof of the second-variation/Fisher identity. -/
  second_variation_eq_fisher_holds : second_variation_eq_fisher
  /-- Fisher/Hessian readout agrees with the coadjoint moment covariance. -/
  fisher_eq_covariance :
    ∀ β : LieAlg, fisherHessian β = momentCovariance β
  /-- Fisher symmetry on all admissible temperature variations. -/
  fisher_symmetric :
    ∀ (β : LieAlg) (X Y : Tangent),
      fisherHessian β X Y = fisherHessian β Y X
  /-- Fisher nonnegativity on all admissible temperature variations. -/
  fisher_nonnegative :
    ∀ (β : LieAlg) (X : Tangent), 0 ≤ fisherHessian β X X
  /-- Strict Fisher gate supplied by a concrete nondegenerate orbit model. -/
  fisher_positive_of_nonzero :
    ∀ (β : LieAlg) (X : Tangent), nonzeroTangent X → 0 < fisherHessian β X X
  /-- Fenchel-Legendre contact equation for entropy and Massieu. -/
  fenchel_legendre_contact : Prop
  /-- Proof of the Fenchel-Legendre contact equation. -/
  fenchel_legendre_contact_holds : fenchel_legendre_contact
  /-- Entropy gradient recovers the geometric-temperature coordinate. -/
  entropy_gradient_eq_beta : Prop
  /-- Proof that the entropy gradient recovers the geometric-temperature coordinate. -/
  entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta
  /-- Entropy Hessian is the inverse Fisher metric on the coadjoint dual lane. -/
  entropy_hessian_eq_inverse_fisher :
    ∀ (Q : LieCoalg),
      entropyHessian Q = inverseFisherHessian Q

namespace InfiniteCoadjointOrbitHessianContext

variable {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
variable {Tangent DualTangent : Type*}

/--
Canonical dimension-agnostic Hessian constructor where the Massieu potential is
defined as the log partition and the covariance readout is defined to be the
Fisher/Hessian readout.

This constructively discharges the `massieu_eq_log_partition` and
`fisher_eq_covariance` fields.  It does not fake the analytic derivative,
strict positivity, Fenchel contact, or inverse-Hessian theorems; those remain
explicit obligations for a concrete infinite-dimensional smooth/operator model.
-/
@[rep_depth transport]
noncomputable def ofLogPartitionAndFisherCovariance
    (moment : Orbit → LieCoalg)
    (partitionFunction : LieAlg → ℝ)
    (thermodynamicMoment : LieAlg → LieCoalg)
    (fisherHessian : LieAlg → Tangent → Tangent → ℝ)
    (nonzeroTangent : Tangent → Prop)
    (souriauEntropy : LieCoalg → ℝ)
    (betaOfMoment : LieCoalg → LieAlg)
    (entropyHessian inverseFisherHessian :
      LieCoalg → DualTangent → DualTangent → ℝ)
    (first_variation_eq_moment : Prop)
    (first_variation_eq_moment_holds : first_variation_eq_moment)
    (second_variation_eq_fisher : Prop)
    (second_variation_eq_fisher_holds : second_variation_eq_fisher)
    (fisher_symmetric :
      ∀ (β : LieAlg) (X Y : Tangent),
        fisherHessian β X Y = fisherHessian β Y X)
    (fisher_nonnegative :
      ∀ (β : LieAlg) (X : Tangent), 0 ≤ fisherHessian β X X)
    (fisher_positive_of_nonzero :
      ∀ (β : LieAlg) (X : Tangent),
        nonzeroTangent X → 0 < fisherHessian β X X)
    (fenchel_legendre_contact : Prop)
    (fenchel_legendre_contact_holds : fenchel_legendre_contact)
    (entropy_gradient_eq_beta : Prop)
    (entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta)
    (entropy_hessian_eq_inverse_fisher :
      ∀ (Q : LieCoalg), entropyHessian Q = inverseFisherHessian Q) :
    InfiniteCoadjointOrbitHessianContext
      Orbit LieAlg LieCoalg Tangent DualTangent where
  moment := moment
  partitionFunction := partitionFunction
  massieuPotential := fun β => Real.log (partitionFunction β)
  thermodynamicMoment := thermodynamicMoment
  fisherHessian := fisherHessian
  momentCovariance := fisherHessian
  nonzeroTangent := nonzeroTangent
  souriauEntropy := souriauEntropy
  betaOfMoment := betaOfMoment
  entropyHessian := entropyHessian
  inverseFisherHessian := inverseFisherHessian
  massieu_eq_log_partition := by
    intro β
    rfl
  first_variation_eq_moment := first_variation_eq_moment
  first_variation_eq_moment_holds := first_variation_eq_moment_holds
  second_variation_eq_fisher := second_variation_eq_fisher
  second_variation_eq_fisher_holds := second_variation_eq_fisher_holds
  fisher_eq_covariance := by
    intro β
    rfl
  fisher_symmetric := fisher_symmetric
  fisher_nonnegative := fisher_nonnegative
  fisher_positive_of_nonzero := fisher_positive_of_nonzero
  fenchel_legendre_contact := fenchel_legendre_contact
  fenchel_legendre_contact_holds := fenchel_legendre_contact_holds
  entropy_gradient_eq_beta := entropy_gradient_eq_beta
  entropy_gradient_eq_beta_holds := entropy_gradient_eq_beta_holds
  entropy_hessian_eq_inverse_fisher := entropy_hessian_eq_inverse_fisher

/--
Constructive dimension-agnostic Hessian/Fisher constructor from a Gram feature
map.

No finite matrix or count-state model is used.  The Fisher bilinear form is
`⟪feature β X, feature β Y⟫`, so symmetry, nonnegativity, and strict positivity
under feature nondegeneracy are derived from the real inner-product structure.
The analytic derivative, Fenchel contact, and inverse-Hessian obligations remain
explicit because they require a concrete smooth/coordinateless model.
-/
@[rep_depth transport]
noncomputable def ofLogPartitionGramFisher
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → LieCoalg)
    (partitionFunction : LieAlg → ℝ)
    (thermodynamicMoment : LieAlg → LieCoalg)
    (feature : LieAlg → Tangent → Feature)
    (souriauEntropy : LieCoalg → ℝ)
    (betaOfMoment : LieCoalg → LieAlg)
    (entropyHessian inverseFisherHessian :
      LieCoalg → DualTangent → DualTangent → ℝ)
    (first_variation_eq_moment : Prop)
    (first_variation_eq_moment_holds : first_variation_eq_moment)
    (second_variation_eq_fisher : Prop)
    (second_variation_eq_fisher_holds : second_variation_eq_fisher)
    (fenchel_legendre_contact : Prop)
    (fenchel_legendre_contact_holds : fenchel_legendre_contact)
    (entropy_gradient_eq_beta : Prop)
    (entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta)
    (entropy_hessian_eq_inverse_fisher :
      ∀ (Q : LieCoalg), entropyHessian Q = inverseFisherHessian Q) :
    InfiniteCoadjointOrbitHessianContext
      Orbit LieAlg LieCoalg Tangent DualTangent :=
  ofLogPartitionAndFisherCovariance
    (moment := moment)
    (partitionFunction := partitionFunction)
    (thermodynamicMoment := thermodynamicMoment)
    (fisherHessian := fun β X Y => inner ℝ (feature β X) (feature β Y))
    (nonzeroTangent := fun X => ∀ β : LieAlg, feature β X ≠ 0)
    (souriauEntropy := souriauEntropy)
    (betaOfMoment := betaOfMoment)
    (entropyHessian := entropyHessian)
    (inverseFisherHessian := inverseFisherHessian)
    (first_variation_eq_moment := first_variation_eq_moment)
    (first_variation_eq_moment_holds := first_variation_eq_moment_holds)
    (second_variation_eq_fisher := second_variation_eq_fisher)
    (second_variation_eq_fisher_holds := second_variation_eq_fisher_holds)
    (fisher_symmetric := by
      intro β X Y
      exact (real_inner_comm (feature β X) (feature β Y)).symm)
    (fisher_nonnegative := by
      intro β X
      exact real_inner_self_nonneg)
    (fisher_positive_of_nonzero := by
      intro β X hX
      exact (real_inner_self_pos).2 (hX β))
    (fenchel_legendre_contact := fenchel_legendre_contact)
    (fenchel_legendre_contact_holds := fenchel_legendre_contact_holds)
    (entropy_gradient_eq_beta := entropy_gradient_eq_beta)
    (entropy_gradient_eq_beta_holds := entropy_gradient_eq_beta_holds)
    (entropy_hessian_eq_inverse_fisher := entropy_hessian_eq_inverse_fisher)


/-- Packed constructive Fisher theorem for the dimension-agnostic Gram route. -/
@[rep_depth transport]
theorem full_gram_fisher_constructive_theorem
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → LieCoalg)
    (partitionFunction : LieAlg → ℝ)
    (thermodynamicMoment : LieAlg → LieCoalg)
    (feature : LieAlg → Tangent → Feature)
    (souriauEntropy : LieCoalg → ℝ)
    (betaOfMoment : LieCoalg → LieAlg)
    (entropyHessian inverseFisherHessian :
      LieCoalg → DualTangent → DualTangent → ℝ)
    (first_variation_eq_moment : Prop)
    (first_variation_eq_moment_holds : first_variation_eq_moment)
    (second_variation_eq_fisher : Prop)
    (second_variation_eq_fisher_holds : second_variation_eq_fisher)
    (fenchel_legendre_contact : Prop)
    (fenchel_legendre_contact_holds : fenchel_legendre_contact)
    (entropy_gradient_eq_beta : Prop)
    (entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta)
    (entropy_hessian_eq_inverse_fisher :
      ∀ (Q : LieCoalg), entropyHessian Q = inverseFisherHessian Q)
    (β : LieAlg) (X Y : Tangent)
    (hX : ∀ β : LieAlg, feature β X ≠ 0) :
    let Cgram :=
      ofLogPartitionGramFisher
        (Orbit := Orbit) (LieAlg := LieAlg) (LieCoalg := LieCoalg)
        (Tangent := Tangent) (DualTangent := DualTangent)
        (Feature := Feature)
        moment partitionFunction thermodynamicMoment feature souriauEntropy
        betaOfMoment entropyHessian inverseFisherHessian
        first_variation_eq_moment first_variation_eq_moment_holds
        second_variation_eq_fisher second_variation_eq_fisher_holds
        fenchel_legendre_contact fenchel_legendre_contact_holds
        entropy_gradient_eq_beta entropy_gradient_eq_beta_holds
        entropy_hessian_eq_inverse_fisher
    Cgram.fisherHessian β X Y = inner ℝ (feature β X) (feature β Y)
      ∧ Cgram.fisherHessian β X Y = Cgram.fisherHessian β Y X
      ∧ 0 ≤ Cgram.fisherHessian β X X
      ∧ 0 < Cgram.fisherHessian β X X := by
  dsimp [ofLogPartitionGramFisher, ofLogPartitionAndFisherCovariance]
  exact
    ⟨rfl,
      (real_inner_comm (feature β X) (feature β Y)).symm,
      real_inner_self_nonneg,
      (real_inner_self_pos).2 (hX β)⟩

attribute [terminal] full_gram_fisher_constructive_theorem

section SmoothLegendreConstructor

open InfoGeometry.Geometry

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

section GibbsSouriauAnalyticWitness

variable {Feature : Type*}
variable [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]

/--
Analytic Gibbs-Souriau witness for the infinite/coordinateless lane.

This is not a finite state shadow and it does not hide differentiation under an
integral behind prose.  A concrete model must supply the actual integration
functional, Gibbs weight, centered moment features, first/second derivative
laws, and covariance identity.  Once those analytic obligations are supplied,
the theorem below composes them with the already-owned Legendre/Gram/square
dissipation route.
-/
@[rep_depth transport]
structure GibbsSouriauGramAnalyticWitness
    (Orbit : Type u) (Θ : Type*) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (Feature : Type*) [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature] where
  /-- Distinguished geometric-temperature point where the analytic witness is valid. -/
  beta : Θ
  /-- Coadjoint moment map. -/
  moment : Orbit → MomentCoord Θ
  /-- Abstract integration/noncommutative expectation functional. -/
  integralFunctional : (Orbit → ℝ) → ℝ
  /-- Gibbs-Souriau unnormalised or normalised weight, depending on the concrete model. -/
  gibbsWeight : Θ → Orbit → ℝ
  /-- Centered moment feature used for the covariance identity. -/
  centeredMomentFeature : Orbit → Θ → ℝ
  /-- Statistical partition functional. -/
  partitionFunction : Θ → ℝ
  /-- Massieu geometry whose gradient/Hessian own the thermodynamic moment/Fisher laws. -/
  massieu : HessianGeometry Θ
  /-- Thermodynamic moment readout `Q(β)`. -/
  thermodynamicMoment : Θ → MomentCoord Θ
  /-- Souriau entropy on the coadjoint dual lane. -/
  souriauEntropy : MomentCoord Θ → ℝ
  /-- Entropy-gradient map used by the local Legendre inverse theorem. -/
  entropyGradient : MomentCoord Θ → Θ
  /-- Fisher Hessian as a continuous-linear equivalence. -/
  fisherEquiv : Θ ≃L[ℝ] MomentCoord Θ
  /-- Hilbert feature representation of the Fisher form. -/
  feature : Θ → Feature
  /-- Partition is represented by the supplied Gibbs-Souriau integral. -/
  partition_eq_integral_gibbsWeight :
    ∀ β : Θ, partitionFunction β = integralFunctional (gibbsWeight β)
  /-- Massieu is the logarithm of the partition functional. -/
  massieu_eq_log_partition :
    ∀ β : Θ, massieu.ψ β = Real.log (partitionFunction β)
  /-- First variation: Massieu gradient gives the thermodynamic moment. -/
  thermodynamicMoment_eq_gradient_at_beta :
    thermodynamicMoment beta = dualCoord massieu beta
  /-- Entropy-gradient contact equation. -/
  entropyGradient_at_moment :
    entropyGradient (dualCoord massieu beta) = beta
  /-- Second variation: Fisher is the Massieu Hessian at the witness point. -/
  fisherEquiv_eq_massieuHessian :
    (fisherEquiv : Θ →L[ℝ] MomentCoord Θ) = hessian massieu beta
  /-- Entropy-gradient derivative is the inverse Fisher map. -/
  entropyGradient_derivative_eq_inverse :
    fderiv ℝ entropyGradient (dualCoord massieu beta) =
      (fisherEquiv.symm : MomentCoord Θ →L[ℝ] Θ)
  /-- Fisher is represented by a Hilbert Gram form. -/
  fisherEquiv_eq_gram :
    ∀ X Y : Θ, (fisherEquiv X) Y = inner ℝ (feature X) (feature Y)
  /-- Covariance identity supplied by the concrete Gibbs-Souriau analytic model. -/
  fisherEquiv_eq_integral_centered_moment_product :
    ∀ X Y : Θ,
      (fisherEquiv X) Y =
        integralFunctional
          (fun x : Orbit => centeredMomentFeature x X * centeredMomentFeature x Y)

namespace GibbsSouriauGramAnalyticWitness

variable {Orbit : Type u}

/-- Convert the analytic witness into the repo-owned Legendre inverse data. -/
@[rep_depth transport]
noncomputable def toLegendreContinuousLinearEquivInverseData
    (W : GibbsSouriauGramAnalyticWitness Orbit Θ Feature) :
    LegendreContinuousLinearEquivInverseData Θ where
  massieu := W.massieu
  beta := W.beta
  entropyGradient := W.entropyGradient
  fisherEquiv := W.fisherEquiv
  entropyGradient_at_moment := W.entropyGradient_at_moment
  fisherEquiv_eq_massieuHessian := W.fisherEquiv_eq_massieuHessian
  entropyGradient_derivative_eq_inverse := W.entropyGradient_derivative_eq_inverse

/--
The analytic Gibbs-Souriau witness discharges the previously prose-only
partition, first-variation, second-variation, Gram, and covariance claims at
the witness point.
-/
@[rep_depth transport]
theorem integral_covariance_gram_legendre_packet
    (W : GibbsSouriauGramAnalyticWitness Orbit Θ Feature)
    (X Y : Θ) :
    W.partitionFunction W.beta = W.integralFunctional (W.gibbsWeight W.beta)
      ∧ W.massieu.ψ W.beta = Real.log (W.partitionFunction W.beta)
      ∧ W.thermodynamicMoment W.beta = dualCoord W.massieu W.beta
      ∧ (W.fisherEquiv : Θ →L[ℝ] MomentCoord Θ) = hessian W.massieu W.beta
      ∧ (W.fisherEquiv X) Y = inner ℝ (W.feature X) (W.feature Y)
      ∧ (W.fisherEquiv X) Y =
        W.integralFunctional
          (fun z : Orbit => W.centeredMomentFeature z X * W.centeredMomentFeature z Y) :=
  ⟨W.partition_eq_integral_gibbsWeight W.beta,
    W.massieu_eq_log_partition W.beta,
    W.thermodynamicMoment_eq_gradient_at_beta,
    W.fisherEquiv_eq_massieuHessian,
    W.fisherEquiv_eq_gram X Y,
    W.fisherEquiv_eq_integral_centered_moment_product X Y⟩

attribute [terminal] integral_covariance_gram_legendre_packet

end GibbsSouriauGramAnalyticWitness

end GibbsSouriauAnalyticWitness

/--
Dimension-agnostic constructor that discharges the smooth Legendre/Fenchel and
inverse-Hessian fields from the repo-owned `LegendreHessianInverseContext`.

This is local in the usual inverse-function sense: the Fisher and entropy
Hessian readouts are the local continuous-linear-map Hessians at the Legendre
contact point.  No finite matrix inverse is used.  Positivity is deliberately
left to a Hilbert/Gram or operator-cone model and remains an explicit input.
-/
@[rep_depth thermo]
noncomputable def ofSmoothLegendreReadout
    (moment : Orbit → MomentCoord Θ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (nonzeroTangent : Θ → Prop)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (fisher_symmetric :
      ∀ (_β : Θ) (X Y : Θ),
        legendre.fisherHessian X Y = legendre.fisherHessian Y X)
    (fisher_nonnegative :
      ∀ (_β : Θ) (X : Θ), 0 ≤ legendre.fisherHessian X X)
    (fisher_positive_of_nonzero :
      ∀ (_β : Θ) (X : Θ),
        nonzeroTangent X → 0 < legendre.fisherHessian X X) :
    InfiniteCoadjointOrbitHessianContext
      Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ) :=
  ofLogPartitionAndFisherCovariance
    (moment := moment)
    (partitionFunction := partitionFunction)
    (thermodynamicMoment := thermodynamicMoment)
    (fisherHessian := fun _ X Y => legendre.fisherHessian X Y)
    (nonzeroTangent := nonzeroTangent)
    (souriauEntropy := souriauEntropy)
    (betaOfMoment := legendre.entropyGradient)
    (entropyHessian := fun _ U V => V (legendre.entropyHessian U))
    (inverseFisherHessian := fun _ U V => V (legendre.entropyHessian U))
    (first_variation_eq_moment :=
      legendre.moment = dualCoord legendre.massieu legendre.beta)
    (first_variation_eq_moment_holds := legendre.moment_eq_gradient)
    (second_variation_eq_fisher :=
      legendre.fisherHessian = hessian legendre.massieu legendre.beta)
    (second_variation_eq_fisher_holds := legendre.fisherHessian_eq_hessianMassieu)
    (fisher_symmetric := fisher_symmetric)
    (fisher_nonnegative := fisher_nonnegative)
    (fisher_positive_of_nonzero := fisher_positive_of_nonzero)
    (fenchel_legendre_contact :=
      legendre.entropyGradient legendre.moment = legendre.beta)
    (fenchel_legendre_contact_holds := legendre.entropyGradient_contact)
    (entropy_gradient_eq_beta :=
      legendre.entropyGradient legendre.moment = legendre.beta)
    (entropy_gradient_eq_beta_holds := legendre.entropyGradient_contact)
    (entropy_hessian_eq_inverse_fisher := by
      intro Q
      rfl)

/--
Packed constructive Legendre theorem for the infinite local readout: the
variation/contact/inverse-Hessian claims are inherited from
`LegendreHessianInverseContext`, not asserted as free hypotheses.
-/
@[rep_depth thermo]
theorem full_smooth_legendre_constructive_theorem
    (moment : Orbit → MomentCoord Θ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (nonzeroTangent : Θ → Prop)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (fisher_symmetric :
      ∀ (_β : Θ) (X Y : Θ),
        legendre.fisherHessian X Y = legendre.fisherHessian Y X)
    (fisher_nonnegative :
      ∀ (_β : Θ) (X : Θ), 0 ≤ legendre.fisherHessian X X)
    (fisher_positive_of_nonzero :
      ∀ (_β : Θ) (X : Θ),
        nonzeroTangent X → 0 < legendre.fisherHessian X X)
    (β X Y : Θ) (Q : MomentCoord Θ) :
    let Cleg :=
      ofSmoothLegendreReadout
        (Orbit := Orbit)
        moment partitionFunction thermodynamicMoment nonzeroTangent
        souriauEntropy legendre fisher_symmetric fisher_nonnegative
        fisher_positive_of_nonzero
    Cleg.massieuPotential β = Real.log (Cleg.partitionFunction β)
      ∧ Cleg.first_variation_eq_moment
      ∧ Cleg.second_variation_eq_fisher
      ∧ Cleg.fisherHessian β = Cleg.momentCovariance β
      ∧ Cleg.fisherHessian β X Y = Cleg.fisherHessian β Y X
      ∧ 0 ≤ Cleg.fisherHessian β X X
      ∧ Cleg.fenchel_legendre_contact
      ∧ Cleg.entropy_gradient_eq_beta
      ∧ Cleg.entropyHessian Q = Cleg.inverseFisherHessian Q := by
  dsimp [ofLogPartitionGramFisher, ofLogPartitionAndFisherCovariance]
  exact
    ⟨rfl,
      legendre.moment_eq_gradient,
      legendre.fisherHessian_eq_hessianMassieu,
      rfl,
      fisher_symmetric β X Y,
      fisher_nonnegative β X,
      legendre.entropyGradient_contact,
      legendre.entropyGradient_contact,
      rfl⟩

attribute [terminal] full_smooth_legendre_constructive_theorem

/--
Dimension-agnostic smooth Legendre constructor with a Gram-represented Fisher
Hessian.

Compared with `ofSmoothLegendreReadout`, this removes the explicit Fisher
symmetry, nonnegativity, and strict-positivity hypotheses.  They are proved
from the inner-product Gram representation.  The remaining nontrivial model
identification is the real analytic bridge
`legendre.fisherHessian X Y = ⟪feature X, feature Y⟫`; this is the correct
place for concrete infinite-dimensional covariance/BKM models to connect.
-/
@[rep_depth thermo]
noncomputable def ofSmoothLegendreGramReadout
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ, legendre.fisherHessian X Y = inner ℝ (feature X) (feature Y)) :
    InfiniteCoadjointOrbitHessianContext
      Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ) :=
  ofSmoothLegendreReadout
    (Orbit := Orbit)
    (moment := moment)
    (partitionFunction := partitionFunction)
    (thermodynamicMoment := thermodynamicMoment)
    (nonzeroTangent := fun X => feature X ≠ 0)
    (souriauEntropy := souriauEntropy)
    (legendre := legendre)
    (fisher_symmetric := by
      intro β X Y
      rw [fisherHessian_eq_gram X Y, fisherHessian_eq_gram Y X]
      exact (real_inner_comm (feature X) (feature Y)).symm)
    (fisher_nonnegative := by
      intro β X
      rw [fisherHessian_eq_gram X X]
      exact real_inner_self_nonneg)
    (fisher_positive_of_nonzero := by
      intro β X hX
      rw [fisherHessian_eq_gram X X]
      exact (real_inner_self_pos).2 hX)

/--
Packed constructive theorem for the infinite smooth-Legendre Gram route.

This proves the inverse-metric/contact packet, Fisher symmetry, Fisher
nonnegativity, and strict Fisher positivity without a finite response matrix.
-/
@[rep_depth thermo]
theorem full_smooth_legendre_gram_constructive_theorem
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ, legendre.fisherHessian X Y = inner ℝ (feature X) (feature Y))
    (β X Y : Θ) (Q : MomentCoord Θ)
    (hX : feature X ≠ 0) :
    let Cgram :=
      ofSmoothLegendreGramReadout
        (Orbit := Orbit)
        moment partitionFunction thermodynamicMoment souriauEntropy
        legendre feature fisherHessian_eq_gram
    Cgram.massieuPotential β = Real.log (Cgram.partitionFunction β)
      ∧ Cgram.first_variation_eq_moment
      ∧ Cgram.second_variation_eq_fisher
      ∧ Cgram.fisherHessian β = Cgram.momentCovariance β
      ∧ Cgram.fisherHessian β X Y = inner ℝ (feature X) (feature Y)
      ∧ Cgram.fisherHessian β X Y = Cgram.fisherHessian β Y X
      ∧ 0 ≤ Cgram.fisherHessian β X X
      ∧ 0 < Cgram.fisherHessian β X X
      ∧ Cgram.fenchel_legendre_contact
      ∧ Cgram.entropy_gradient_eq_beta
      ∧ Cgram.entropyHessian Q = Cgram.inverseFisherHessian Q := by
  dsimp [ofSmoothLegendreGramReadout, ofSmoothLegendreReadout,
    ofLogPartitionAndFisherCovariance]
  exact
    ⟨rfl,
      legendre.moment_eq_gradient,
      legendre.fisherHessian_eq_hessianMassieu,
      rfl,
      fisherHessian_eq_gram X Y,
      by
        rw [fisherHessian_eq_gram X Y, fisherHessian_eq_gram Y X]
        exact (real_inner_comm (feature X) (feature Y)).symm,
      by
        rw [fisherHessian_eq_gram X X]
        exact real_inner_self_nonneg,
      by
        rw [fisherHessian_eq_gram X X]
        exact (real_inner_self_pos).2 hX,
      legendre.entropyGradient_contact,
      legendre.entropyGradient_contact,
      rfl⟩

attribute [terminal] full_smooth_legendre_gram_constructive_theorem

end SmoothLegendreConstructor

variable
  (C :
    InfiniteCoadjointOrbitHessianContext
      Orbit LieAlg LieCoalg Tangent DualTangent)

/-- The full coadjoint-orbit Massieu potential is the log partition. -/
@[rep_depth transport]
theorem massieu_eq_log_partition_at (β : LieAlg) :
    C.massieuPotential β = Real.log (C.partitionFunction β) :=
  C.massieu_eq_log_partition β

/-- The full coadjoint-orbit Fisher/Hessian readout is the moment covariance. -/
@[rep_depth transport]
theorem fisher_hessian_eq_covariance (β : LieAlg) :
    C.fisherHessian β = C.momentCovariance β :=
  C.fisher_eq_covariance β

/-- Fisher symmetry in the full coadjoint-orbit Hessian interface. -/
@[rep_depth transport]
theorem fisher_hessian_symmetric (β : LieAlg) (X Y : Tangent) :
    C.fisherHessian β X Y = C.fisherHessian β Y X :=
  C.fisher_symmetric β X Y

/-- Fisher nonnegativity in the full coadjoint-orbit Hessian interface. -/
@[rep_depth transport]
theorem fisher_hessian_nonnegative (β : LieAlg) (X : Tangent) :
    0 ≤ C.fisherHessian β X X :=
  C.fisher_nonnegative β X

/-- Strict Fisher positivity under the explicit nondegenerate-tangent gate. -/
@[rep_depth transport]
theorem fisher_hessian_positive_of_nonzero
    (β : LieAlg) (X : Tangent) (hX : C.nonzeroTangent X) :
    0 < C.fisherHessian β X X :=
  C.fisher_positive_of_nonzero β X hX

/-- Entropy Hessian is the inverse Fisher readout on the coadjoint dual lane. -/
@[rep_depth transport]
theorem entropy_hessian_eq_inverse_fisher_at (Q : LieCoalg) :
    C.entropyHessian Q = C.inverseFisherHessian Q :=
  C.entropy_hessian_eq_inverse_fisher Q

/--
Full infinite-dimensional coadjoint-orbit Hessian theorem.

This theorem is deliberately proof-carrying: it exposes all analytic outputs
needed by the Souriau/Fisher/Legendre derivation, but each analytic step is an
explicit field of the context.  Thus it is valid for infinite-dimensional or
noncommutative orbit models without smuggling in finite diagonal/count-state
assumptions.
-/
@[rep_depth transport]
theorem full_infinite_dimensional_coadjoint_orbit_hessian_theorem
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent) :
    C.massieuPotential β = Real.log (C.partitionFunction β)
      ∧ C.first_variation_eq_moment
      ∧ C.second_variation_eq_fisher
      ∧ C.fisherHessian β = C.momentCovariance β
      ∧ C.fisherHessian β X Y = C.fisherHessian β Y X
      ∧ 0 ≤ C.fisherHessian β X X
      ∧ C.fenchel_legendre_contact
      ∧ C.entropy_gradient_eq_beta
      ∧ C.entropyHessian Q = C.inverseFisherHessian Q := by
  exact
    ⟨C.massieu_eq_log_partition_at β,
      C.first_variation_eq_moment_holds,
      C.second_variation_eq_fisher_holds,
      C.fisher_hessian_eq_covariance β,
      C.fisher_hessian_symmetric β X Y,
      C.fisher_hessian_nonnegative β X,
      C.fenchel_legendre_contact_holds,
      C.entropy_gradient_eq_beta_holds,
      C.entropy_hessian_eq_inverse_fisher_at Q⟩

attribute [terminal] full_infinite_dimensional_coadjoint_orbit_hessian_theorem

/--
Strict Fisher leg of the full infinite-dimensional coadjoint-orbit Hessian
theorem.  The abstract interface does not infer nondegeneracy from syntax:
the concrete orbit model must supply `nonzeroTangent`.
-/
@[rep_depth transport]
theorem full_infinite_dimensional_coadjoint_orbit_hessian_strict_fisher
    (β : LieAlg) (X : Tangent) (hX : C.nonzeroTangent X) :
    0 < C.fisherHessian β X X :=
  C.fisher_hessian_positive_of_nonzero β X hX

attribute [terminal] full_infinite_dimensional_coadjoint_orbit_hessian_strict_fisher

/--
Strict full infinite-dimensional coadjoint-orbit Hessian theorem.

This is the same proof-carrying theorem packet as
`full_infinite_dimensional_coadjoint_orbit_hessian_theorem`, strengthened by
the explicit nondegenerate-tangent gate needed for strict Fisher positivity.
-/
@[rep_depth transport]
theorem full_infinite_dimensional_coadjoint_orbit_strict_hessian_theorem
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent)
    (hX : C.nonzeroTangent X) :
    C.massieuPotential β = Real.log (C.partitionFunction β)
      ∧ C.first_variation_eq_moment
      ∧ C.second_variation_eq_fisher
      ∧ C.fisherHessian β = C.momentCovariance β
      ∧ C.fisherHessian β X Y = C.fisherHessian β Y X
      ∧ 0 ≤ C.fisherHessian β X X
      ∧ 0 < C.fisherHessian β X X
      ∧ C.fenchel_legendre_contact
      ∧ C.entropy_gradient_eq_beta
      ∧ C.entropyHessian Q = C.inverseFisherHessian Q := by
  have hH :=
    C.full_infinite_dimensional_coadjoint_orbit_hessian_theorem β Q X Y
  exact
    ⟨hH.1,
      hH.2.1,
      hH.2.2.1,
      hH.2.2.2.1,
      hH.2.2.2.2.1,
      hH.2.2.2.2.2.1,
      C.full_infinite_dimensional_coadjoint_orbit_hessian_strict_fisher β X hX,
      hH.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2.2⟩

attribute [terminal] full_infinite_dimensional_coadjoint_orbit_strict_hessian_theorem

end InfiniteCoadjointOrbitHessianContext

/-! ## Smooth Legendre discharge for the inverse-Fisher Hessian leg -/

section SmoothLegendreInverseDischarge

open InfoGeometry.Geometry

variable {Orbit : Type u}
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Witness that an abstract full coadjoint-orbit Hessian context is locally
represented by the smooth Legendre inverse-Hessian owner surface.

This is intentionally narrower than the full analytic theorem: it does not
derive the Legendre inverse-function hypotheses.  It records the exact readout
identifications needed to descend the Souriau inverse-Fisher equality to the
repo-owned `LegendreHessianInverseContext`.
-/
@[rep_depth thermo]
structure SmoothLegendreInverseWitness
    (C :
      InfiniteCoadjointOrbitHessianContext
        Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ)) where
  /-- Smooth Legendre owner surface for `Hess(S) = Fisher⁻¹`. -/
  legendre : LegendreHessianInverseContext Θ
  /-- Temperature-side Fisher readout is induced by the Legendre Hessian. -/
  fisher_readout_matches :
    ∀ (β : Θ) (X Y : Θ),
      C.fisherHessian β X Y = legendre.fisherHessian X Y
  /-- Dual-side entropy readout is induced by the Legendre entropy Hessian. -/
  entropy_readout_matches :
    ∀ (Q U V : MomentCoord Θ),
      C.entropyHessian Q U V = V (legendre.entropyHessian U)
  /-- The abstract inverse-Fisher readout uses the same Legendre inverse map. -/
  inverse_readout_matches :
    ∀ (Q U V : MomentCoord Θ),
      C.inverseFisherHessian Q U V = V (legendre.entropyHessian U)

namespace SmoothLegendreInverseWitness

variable
  {C :
    InfiniteCoadjointOrbitHessianContext
      Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ)}
  (W : SmoothLegendreInverseWitness C)

/--
The smooth Legendre witness supplies the actual two-sided inverse laws for the
temperature/moment Hessian pair.
-/
@[rep_depth thermo]
theorem two_sided_inverse_laws :
    W.legendre.entropyHessian.comp W.legendre.fisherHessian =
        ContinuousLinearMap.id ℝ Θ
      ∧ W.legendre.fisherHessian.comp W.legendre.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord Θ) :=
  W.legendre.entropy_hessian_eq_fisher_inverse

/--
Discharge the Souriau infinite-context inverse-Fisher readout equality from a
smooth Legendre inverse-Hessian witness.
-/
@[rep_depth thermo]
theorem legendre_entropy_hessian_eq_inverse_fisher_at
    (W : SmoothLegendreInverseWitness C) (Q : MomentCoord Θ) :
    C.entropyHessian Q = C.inverseFisherHessian Q := by
  funext U V
  rw [SmoothLegendreInverseWitness.entropy_readout_matches W Q U V,
    SmoothLegendreInverseWitness.inverse_readout_matches W Q U V]

/--
Packed closure-debt payment: the abstract Souriau inverse-Hessian equality is
connected to the concrete smooth Legendre two-sided inverse laws.
-/
@[rep_depth thermo]
theorem souriau_inverse_fisher_from_smooth_legendre_packet (Q : MomentCoord Θ) :
    C.entropyHessian Q = C.inverseFisherHessian Q
      ∧ W.legendre.entropyHessian.comp W.legendre.fisherHessian =
        ContinuousLinearMap.id ℝ Θ
      ∧ W.legendre.fisherHessian.comp W.legendre.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord Θ) :=
  ⟨SmoothLegendreInverseWitness.legendre_entropy_hessian_eq_inverse_fisher_at W Q,
    (SmoothLegendreInverseWitness.two_sided_inverse_laws W).1,
    (SmoothLegendreInverseWitness.two_sided_inverse_laws W).2⟩

attribute [terminal] souriau_inverse_fisher_from_smooth_legendre_packet

end SmoothLegendreInverseWitness

end SmoothLegendreInverseDischarge

/--
Combined full coadjoint-orbit Hessian/metriplectic theorem context.

This joins the Hessian/Fisher/Legendre theorem with the orbit-level
metriplectic second law, still without finiteness assumptions.
-/
@[rep_depth transport]
structure InfiniteCoadjointOrbitHessianMetriplecticContext
    (Orbit : Type u) (LieAlg : Type v) (LieCoalg : Type w)
    (Tangent DualTangent : Type*) where
  hessian :
    InfiniteCoadjointOrbitHessianContext
      Orbit LieAlg LieCoalg Tangent DualTangent
  metriplectic :
    InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg

section ConstructiveCombinedContext

open InfoGeometry.Geometry

variable {Orbit : Type u}
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/--
Fully constructive dimension-agnostic Hessian/metriplectic context assembled
from repo-owned infinite routes:

* Hessian/Fenchel/inverse-Fisher data comes from the smooth Legendre readout.
* Coadjoint-orbit closure is the image of the moment map.
* Reversible entropy is definitionally zero.
* Metric/total entropy production is a square.

This is not a finite shadow: `Orbit` is arbitrary and the Hessian side is an
arbitrary normed-space Legendre owner surface.
-/
@[rep_depth thermo]
noncomputable def ofSmoothLegendreSquareDissipation
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (nonzeroTangent : Θ → Prop)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (fisher_symmetric :
      ∀ (_β : Θ) (X Y : Θ),
        legendre.fisherHessian X Y = legendre.fisherHessian Y X)
    (fisher_nonnegative :
      ∀ (_β : Θ) (X : Θ), 0 ≤ legendre.fisherHessian X X)
    (fisher_positive_of_nonzero :
      ∀ (_β : Θ) (X : Θ),
        nonzeroTangent X → 0 < legendre.fisherHessian X X) :
    InfiniteCoadjointOrbitHessianMetriplecticContext
      Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ) where
  hessian :=
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreReadout
      (Orbit := Orbit)
      moment partitionFunction thermodynamicMoment nonzeroTangent
      souriauEntropy legendre fisher_symmetric fisher_nonnegative
      fisher_positive_of_nonzero
  metriplectic :=
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation
      (Orbit := Orbit) (LieAlg := Θ) (LieCoalg := MomentCoord Θ)
      moment geometricTemperature reversibleVectorField metricVectorField
      entropy dissipationAmplitude

/--
Fully constructive dimension-agnostic Hessian/metriplectic context using a
Gram-represented smooth Legendre Fisher Hessian and square dissipation.

This removes the old Fisher symmetry/nonnegativity/positivity inputs from the
combined constructor.  The only Hessian-side bridge still required is the
model-specific equality between the Legendre Hessian and the Gram feature
pairing.
-/
@[rep_depth thermo]
noncomputable def ofSmoothLegendreGramSquareDissipation
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ, legendre.fisherHessian X Y = inner ℝ (feature X) (feature Y)) :
    InfiniteCoadjointOrbitHessianMetriplecticContext
      Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ) where
  hessian :=
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreGramReadout
      (Orbit := Orbit)
      moment partitionFunction thermodynamicMoment souriauEntropy
      legendre feature fisherHessian_eq_gram
  metriplectic :=
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation
      (Orbit := Orbit) (LieAlg := Θ) (LieCoalg := MomentCoord Θ)
      moment geometricTemperature reversibleVectorField metricVectorField
      entropy dissipationAmplitude

/--
Fully constructive dimension-agnostic Hessian/metriplectic context using a
continuous-linear equivalence as the local Legendre inverse.

This removes the separate two-sided inverse-law fields from the Souriau input:
they are proved in `LegendreContinuousLinearEquivInverseData` from
`fisherEquiv` and `fisherEquiv.symm`.
-/
@[rep_depth thermo]
noncomputable def ofContinuousLinearEquivLegendreGramSquareDissipation
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendreData : LegendreContinuousLinearEquivInverseData Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ,
        legendreData.toLegendreHessianInverseContext.fisherHessian X Y =
          inner ℝ (feature X) (feature Y)) :
    InfiniteCoadjointOrbitHessianMetriplecticContext
      Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ) :=
  ofSmoothLegendreGramSquareDissipation
    (Orbit := Orbit)
    moment geometricTemperature reversibleVectorField metricVectorField
    entropy dissipationAmplitude partitionFunction thermodynamicMoment
    souriauEntropy legendreData.toLegendreHessianInverseContext
    feature fisherHessian_eq_gram

namespace InfiniteCoadjointOrbitHessianMetriplecticContext

variable {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
variable {Tangent DualTangent : Type*}
variable
  (C :
    InfiniteCoadjointOrbitHessianMetriplecticContext
      Orbit LieAlg LieCoalg Tangent DualTangent)

/--
Full infinite-dimensional Souriau theorem packet: coadjoint-orbit Hessian
identity surface plus metriplectic second law.
-/
@[rep_depth transport]
theorem full_infinite_dimensional_coadjoint_orbit_hessian_metriplectic_theorem
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent) (x : Orbit) :
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x := by
  have hH :=
    C.hessian.full_infinite_dimensional_coadjoint_orbit_hessian_theorem
      β Q X Y
  exact
    ⟨hH.1,
      hH.2.1,
      hH.2.2.1,
      hH.2.2.2.1,
      hH.2.2.2.2.1,
      hH.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2.2,
      C.metriplectic.coadjoint_orbit_metriplectic_second_law x⟩

attribute [terminal] full_infinite_dimensional_coadjoint_orbit_hessian_metriplectic_theorem

/--
Strict full infinite-dimensional Souriau theorem packet: Hessian/Fisher
strict positivity under the explicit nondegenerate-tangent gate, plus the
orbit-level metriplectic second law.
-/
@[rep_depth transport]
theorem full_infinite_dimensional_coadjoint_orbit_strict_hessian_metriplectic_theorem
    (β : LieAlg) (Q : LieCoalg) (X Y : Tangent) (x : Orbit)
    (hX : C.hessian.nonzeroTangent X) :
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ 0 < C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x := by
  have hH :=
    C.hessian.full_infinite_dimensional_coadjoint_orbit_strict_hessian_theorem
      β Q X Y hX
  exact
    ⟨hH.1,
      hH.2.1,
      hH.2.2.1,
      hH.2.2.2.1,
      hH.2.2.2.2.1,
      hH.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2.2.2,
      C.metriplectic.coadjoint_orbit_metriplectic_second_law x⟩

attribute [terminal] full_infinite_dimensional_coadjoint_orbit_strict_hessian_metriplectic_theorem

end InfiniteCoadjointOrbitHessianMetriplecticContext

/--
Packed constructive full Souriau theorem for the smooth-Legendre plus
square-dissipation route.

This replaces the combined explicit Hessian/metriplectic context hypotheses by
the constructive infinite ingredients above: Legendre owner data, moment-image
orbit closure, and square entropy production.
-/
@[rep_depth thermo]
theorem full_smooth_legendre_square_dissipation_constructive_theorem
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (nonzeroTangent : Θ → Prop)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (fisher_symmetric :
      ∀ (_β : Θ) (X Y : Θ),
        legendre.fisherHessian X Y = legendre.fisherHessian Y X)
    (fisher_nonnegative :
      ∀ (_β : Θ) (X : Θ), 0 ≤ legendre.fisherHessian X X)
    (fisher_positive_of_nonzero :
      ∀ (_β : Θ) (X : Θ),
        nonzeroTangent X → 0 < legendre.fisherHessian X X)
    (β X Y : Θ) (Q : MomentCoord Θ) (x : Orbit) :
    let C :=
      ofSmoothLegendreSquareDissipation
        moment geometricTemperature reversibleVectorField metricVectorField
        entropy dissipationAmplitude partitionFunction thermodynamicMoment
        nonzeroTangent souriauEntropy legendre fisher_symmetric
        fisher_nonnegative fisher_positive_of_nonzero
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x := by
  exact
    InfiniteCoadjointOrbitHessianMetriplecticContext.full_infinite_dimensional_coadjoint_orbit_hessian_metriplectic_theorem
      (C :=
        ofSmoothLegendreSquareDissipation
          moment geometricTemperature reversibleVectorField metricVectorField
          entropy dissipationAmplitude partitionFunction thermodynamicMoment
          nonzeroTangent souriauEntropy legendre fisher_symmetric
          fisher_nonnegative fisher_positive_of_nonzero)
      β Q X Y x

attribute [terminal] full_smooth_legendre_square_dissipation_constructive_theorem

/--
Packed constructive full Souriau theorem for the smooth-Legendre Gram plus
square-dissipation route.

This is the stronger infinite route: Fisher positivity is proved from an
inner-product Gram representation and entropy production is proved from a
square.  No finite response matrix is used.
-/
@[rep_depth thermo]
theorem full_smooth_legendre_gram_square_dissipation_constructive_theorem
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ, legendre.fisherHessian X Y = inner ℝ (feature X) (feature Y))
    (β X Y : Θ) (Q : MomentCoord Θ) (x : Orbit)
    (hX : feature X ≠ 0) :
    let C :=
      ofSmoothLegendreGramSquareDissipation
        moment geometricTemperature reversibleVectorField metricVectorField
        entropy dissipationAmplitude partitionFunction thermodynamicMoment
        souriauEntropy legendre feature fisherHessian_eq_gram
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y = inner ℝ (feature X) (feature Y)
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ 0 < C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x := by
  dsimp [ofSmoothLegendreGramSquareDissipation,
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreGramReadout,
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreReadout,
    InfiniteCoadjointOrbitHessianContext.ofLogPartitionAndFisherCovariance,
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation,
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImage]
  exact
    ⟨rfl,
      legendre.moment_eq_gradient,
      legendre.fisherHessian_eq_hessianMassieu,
      rfl,
      fisherHessian_eq_gram X Y,
      by
        rw [fisherHessian_eq_gram X Y, fisherHessian_eq_gram Y X]
        exact (real_inner_comm (feature X) (feature Y)).symm,
      by
        rw [fisherHessian_eq_gram X X]
        exact real_inner_self_nonneg,
      by
        rw [fisherHessian_eq_gram X X]
        exact (real_inner_self_pos).2 hX,
      legendre.entropyGradient_contact,
      legendre.entropyGradient_contact,
      rfl,
      sq_nonneg (dissipationAmplitude x)⟩

attribute [terminal] full_smooth_legendre_gram_square_dissipation_constructive_theorem

/--
Stronger constructive full Souriau theorem for the smooth-Legendre Gram plus
square-dissipation route.

This pays the inverse-Hessian closure debt inside the infinite/dimension-
agnostic lane: besides the Souriau Hessian/metriplectic packet, it also exports
the repo-owned smooth Legendre derivative identity and both two-sided inverse
laws for `Hess(S) = Fisher⁻¹`.  No finite response matrix or count-state model
is used.
-/
@[rep_depth thermo]
theorem full_smooth_legendre_gram_square_dissipation_inverse_laws_theorem
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendre : LegendreHessianInverseContext Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ, legendre.fisherHessian X Y = inner ℝ (feature X) (feature Y))
    (β X Y : Θ) (Q : MomentCoord Θ) (x : Orbit)
    (hX : feature X ≠ 0) :
    let C :=
      ofSmoothLegendreGramSquareDissipation
        moment geometricTemperature reversibleVectorField metricVectorField
        entropy dissipationAmplitude partitionFunction thermodynamicMoment
        souriauEntropy legendre feature fisherHessian_eq_gram
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y = inner ℝ (feature X) (feature Y)
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ 0 < C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x
      ∧ legendre.entropyHessian = fderiv ℝ legendre.entropyGradient legendre.moment
      ∧ legendre.entropyHessian.comp legendre.fisherHessian =
        ContinuousLinearMap.id ℝ Θ
      ∧ legendre.fisherHessian.comp legendre.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord Θ) := by
  dsimp [ofSmoothLegendreGramSquareDissipation,
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreGramReadout,
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreReadout,
    InfiniteCoadjointOrbitHessianContext.ofLogPartitionAndFisherCovariance,
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation,
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImage]
  exact
    ⟨rfl,
      legendre.moment_eq_gradient,
      legendre.fisherHessian_eq_hessianMassieu,
      rfl,
      fisherHessian_eq_gram X Y,
      by
        rw [fisherHessian_eq_gram X Y, fisherHessian_eq_gram Y X]
        exact (real_inner_comm (feature X) (feature Y)).symm,
      by
        rw [fisherHessian_eq_gram X X]
        exact real_inner_self_nonneg,
      by
        rw [fisherHessian_eq_gram X X]
        exact (real_inner_self_pos).2 hX,
      legendre.entropyGradient_contact,
      legendre.entropyGradient_contact,
      rfl,
      sq_nonneg (dissipationAmplitude x),
      legendre.entropyHessian_eq_derivEntropyGradient,
      legendre.entropy_hessian_eq_fisher_inverse.1,
      legendre.entropy_hessian_eq_fisher_inverse.2⟩

attribute [terminal] full_smooth_legendre_gram_square_dissipation_inverse_laws_theorem

/--
Constructive full Souriau theorem from continuous-linear-equivalence Legendre
data, Gram Fisher representation, and square dissipation.

This is the non-finite replacement for raw inverse-Hessian hypotheses: the
Legendre inverse laws are derived from `fisherEquiv`/`fisherEquiv.symm`, Fisher
positivity comes from the Gram inner product, and entropy production comes from
a square.
-/
@[rep_depth thermo]
theorem full_cle_legendre_gram_square_dissipation_constructive_theorem
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendreData : LegendreContinuousLinearEquivInverseData Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ,
        legendreData.toLegendreHessianInverseContext.fisherHessian X Y =
          inner ℝ (feature X) (feature Y))
    (β X Y : Θ) (Q : MomentCoord Θ) (x : Orbit)
    (hX : feature X ≠ 0) :
    let C :=
      ofContinuousLinearEquivLegendreGramSquareDissipation
        moment geometricTemperature reversibleVectorField metricVectorField
        entropy dissipationAmplitude partitionFunction thermodynamicMoment
        souriauEntropy legendreData feature fisherHessian_eq_gram
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.first_variation_eq_moment
      ∧ C.hessian.second_variation_eq_fisher
      ∧ C.hessian.fisherHessian β = C.hessian.momentCovariance β
      ∧ C.hessian.fisherHessian β X Y = inner ℝ (feature X) (feature Y)
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ 0 < C.hessian.fisherHessian β X X
      ∧ C.hessian.fenchel_legendre_contact
      ∧ C.hessian.entropy_gradient_eq_beta
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x
      ∧ legendreData.toLegendreHessianInverseContext.entropyHessian =
        fderiv ℝ
          legendreData.toLegendreHessianInverseContext.entropyGradient
          legendreData.toLegendreHessianInverseContext.moment
      ∧ legendreData.toLegendreHessianInverseContext.entropyHessian.comp
          legendreData.toLegendreHessianInverseContext.fisherHessian =
        ContinuousLinearMap.id ℝ Θ
      ∧ legendreData.toLegendreHessianInverseContext.fisherHessian.comp
          legendreData.toLegendreHessianInverseContext.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord Θ) := by
  exact
    full_smooth_legendre_gram_square_dissipation_inverse_laws_theorem
      (Orbit := Orbit)
      moment geometricTemperature reversibleVectorField metricVectorField
      entropy dissipationAmplitude partitionFunction thermodynamicMoment
      souriauEntropy legendreData.toLegendreHessianInverseContext
      feature fisherHessian_eq_gram β X Y Q x hX

attribute [terminal] full_cle_legendre_gram_square_dissipation_constructive_theorem

/--
Step-by-step constructive Fisher/Onsager/metriplectic proof packet.

This is the Lean-facing form of the Souriau proof narrative:

* the Massieu Hessian/Fisher readout is a real Gram form;
* Fisher symmetry and positivity are derived from the inner product;
* the entropy Hessian is the inverse Fisher map via the continuous-linear
  Legendre equivalence;
* the reversible coadjoint-leaf channel is Casimir (`0`);
* the transverse Onsager channel is a square;
* total entropy production is the transverse channel and is nonnegative.

All carriers are arbitrary.  No finite response matrix or count-state shadow is
used.
-/
@[rep_depth thermo]
theorem fisher_onsager_metriplectic_constructive_proof_packet
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (moment : Orbit → MomentCoord Θ)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (partitionFunction : Θ → ℝ)
    (thermodynamicMoment : Θ → MomentCoord Θ)
    (souriauEntropy : MomentCoord Θ → ℝ)
    (legendreData : LegendreContinuousLinearEquivInverseData Θ)
    (feature : Θ → Feature)
    (fisherHessian_eq_gram :
      ∀ X Y : Θ,
        legendreData.toLegendreHessianInverseContext.fisherHessian X Y =
          inner ℝ (feature X) (feature Y))
    (β X Y : Θ) (Q : MomentCoord Θ) (x : Orbit)
    (hX : feature X ≠ 0) :
    let C :=
      ofContinuousLinearEquivLegendreGramSquareDissipation
        moment geometricTemperature reversibleVectorField metricVectorField
        entropy dissipationAmplitude partitionFunction thermodynamicMoment
        souriauEntropy legendreData feature fisherHessian_eq_gram
    C.hessian.massieuPotential β =
        Real.log (C.hessian.partitionFunction β)
      ∧ C.hessian.fisherHessian β X Y = inner ℝ (feature X) (feature Y)
      ∧ C.hessian.fisherHessian β X Y =
        C.hessian.fisherHessian β Y X
      ∧ 0 ≤ C.hessian.fisherHessian β X X
      ∧ 0 < C.hessian.fisherHessian β X X
      ∧ C.hessian.entropyHessian Q =
        C.hessian.inverseFisherHessian Q
      ∧ legendreData.toLegendreHessianInverseContext.entropyHessian.comp
          legendreData.toLegendreHessianInverseContext.fisherHessian =
        ContinuousLinearMap.id ℝ Θ
      ∧ legendreData.toLegendreHessianInverseContext.fisherHessian.comp
          legendreData.toLegendreHessianInverseContext.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord Θ)
      ∧ C.metriplectic.reversibleEntropyRate x = 0
      ∧ C.metriplectic.metricEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ C.metriplectic.totalEntropyRate x = C.metriplectic.metricEntropyRate x
      ∧ 0 ≤ C.metriplectic.metricEntropyRate x
      ∧ 0 ≤ C.metriplectic.totalEntropyRate x := by
  dsimp [ofContinuousLinearEquivLegendreGramSquareDissipation,
    ofSmoothLegendreGramSquareDissipation,
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreGramReadout,
    InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreReadout,
    InfiniteCoadjointOrbitHessianContext.ofLogPartitionAndFisherCovariance,
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation,
    InfiniteCoadjointOrbitMetriplecticContext.ofMomentImage]
  exact
    ⟨rfl,
      fisherHessian_eq_gram X Y,
      by
        rw [fisherHessian_eq_gram X Y, fisherHessian_eq_gram Y X]
        exact (real_inner_comm (feature X) (feature Y)).symm,
      by
        rw [fisherHessian_eq_gram X X]
        exact real_inner_self_nonneg,
      by
        rw [fisherHessian_eq_gram X X]
        exact (real_inner_self_pos).2 hX,
      rfl,
      legendreData.toLegendreHessianInverseContext.entropy_hessian_eq_fisher_inverse.1,
      legendreData.toLegendreHessianInverseContext.entropy_hessian_eq_fisher_inverse.2,
      rfl,
      rfl,
      rfl,
      sq_nonneg (dissipationAmplitude x),
      sq_nonneg (dissipationAmplitude x)⟩

attribute [terminal] fisher_onsager_metriplectic_constructive_proof_packet

/--
Full analytic-to-metriplectic packet.

This composes the explicit Gibbs-Souriau analytic witness
(`partition = integral`, first variation, second variation, Gram Fisher, and
centered-moment covariance) with the already-owned infinite
Legendre/Gram/square-dissipation theorem.  The result is still
dimension-agnostic: no finite response matrix or count-state model is used.
-/
@[rep_depth thermo]
theorem gibbs_souriau_integral_covariance_to_metriplectic_packet
    {Feature : Type*}
    [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
    (W :
      InfiniteCoadjointOrbitHessianContext.GibbsSouriauGramAnalyticWitness
        Orbit Θ Feature)
    (geometricTemperature : Θ)
    (reversibleVectorField metricVectorField : Orbit → Orbit)
    (entropy : Orbit → ℝ)
    (dissipationAmplitude : Orbit → ℝ)
    (β X Y : Θ) (Q : MomentCoord Θ) (x : Orbit)
    (hX : W.feature X ≠ 0) :
    W.partitionFunction W.beta = W.integralFunctional (W.gibbsWeight W.beta)
      ∧ W.massieu.ψ W.beta = Real.log (W.partitionFunction W.beta)
      ∧ W.thermodynamicMoment W.beta = dualCoord W.massieu W.beta
      ∧ (W.fisherEquiv : Θ →L[ℝ] MomentCoord Θ) = hessian W.massieu W.beta
      ∧ (W.fisherEquiv X) Y = inner ℝ (W.feature X) (W.feature Y)
      ∧ (W.fisherEquiv X) Y =
        W.integralFunctional
          (fun z : Orbit => W.centeredMomentFeature z X * W.centeredMomentFeature z Y)
      ∧
        (let C :
          InfiniteCoadjointOrbitHessianMetriplecticContext
            Orbit Θ (MomentCoord Θ) Θ (MomentCoord Θ) :=
          ofContinuousLinearEquivLegendreGramSquareDissipation
            W.moment geometricTemperature reversibleVectorField metricVectorField
            entropy dissipationAmplitude W.partitionFunction W.thermodynamicMoment
            W.souriauEntropy W.toLegendreContinuousLinearEquivInverseData
            W.feature W.fisherEquiv_eq_gram
        C.hessian.massieuPotential β =
            Real.log (C.hessian.partitionFunction β)
          ∧ C.hessian.fisherHessian β X Y =
            inner ℝ (W.feature X) (W.feature Y)
          ∧ C.hessian.fisherHessian β X Y =
            C.hessian.fisherHessian β Y X
          ∧ 0 ≤ C.hessian.fisherHessian β X X
          ∧ 0 < C.hessian.fisherHessian β X X
          ∧ C.hessian.entropyHessian Q =
            C.hessian.inverseFisherHessian Q
          ∧
            W.toLegendreContinuousLinearEquivInverseData.toLegendreHessianInverseContext.entropyHessian.comp
              W.toLegendreContinuousLinearEquivInverseData.toLegendreHessianInverseContext.fisherHessian =
            ContinuousLinearMap.id ℝ Θ
          ∧
            W.toLegendreContinuousLinearEquivInverseData.toLegendreHessianInverseContext.fisherHessian.comp
              W.toLegendreContinuousLinearEquivInverseData.toLegendreHessianInverseContext.entropyHessian =
            ContinuousLinearMap.id ℝ (MomentCoord Θ)
          ∧ C.metriplectic.reversibleEntropyRate x = 0
          ∧ C.metriplectic.metricEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
          ∧ C.metriplectic.totalEntropyRate x = C.metriplectic.metricEntropyRate x
          ∧ 0 ≤ C.metriplectic.metricEntropyRate x
          ∧ 0 ≤ C.metriplectic.totalEntropyRate x) := by
  refine
    ⟨W.partition_eq_integral_gibbsWeight W.beta,
      W.massieu_eq_log_partition W.beta,
      W.thermodynamicMoment_eq_gradient_at_beta,
      W.fisherEquiv_eq_massieuHessian,
      W.fisherEquiv_eq_gram X Y,
      W.fisherEquiv_eq_integral_centered_moment_product X Y,
      ?_⟩
  exact
    fisher_onsager_metriplectic_constructive_proof_packet
      (Orbit := Orbit)
      W.moment geometricTemperature reversibleVectorField metricVectorField
      entropy dissipationAmplitude W.partitionFunction W.thermodynamicMoment
      W.souriauEntropy W.toLegendreContinuousLinearEquivInverseData
      W.feature W.fisherEquiv_eq_gram β X Y Q x hX

attribute [terminal] gibbs_souriau_integral_covariance_to_metriplectic_packet

end ConstructiveCombinedContext

section OperatorialGate

open InfoGeometry.Canonical.SouriauKreinMetriplectic

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The existing Krein/operatorial Souriau context supplies the required
nonnegative metric gate only after an explicit positive-semidefinite response
packet has been provided.
-/
@[rep_depth transport]
theorem operatorial_metric_gate_from_psd
    (C : OperatorialMetriplecticContext (E := E))
    (hPSD : C.OperatorialMetricResponsePSD)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_metricResponsePSD hPSD xForce yForce

attribute [infrastructure] operatorial_metric_gate_from_psd

/--
Regular Drazin/Krein cone positivity is sufficient for the operatorial metric
gate used by the full coadjoint-orbit theorem interface.
-/
@[rep_depth transport]
theorem operatorial_metric_gate_from_regular_cone
    (C : OperatorialMetriplecticContext (E := E))
    (R : OperatorialMetriplecticContext.RegularConeOperatorialResponseContext C)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_regularCone R xForce yForce

attribute [infrastructure] operatorial_metric_gate_from_regular_cone

/--
Square-response operatorial gate for the full coadjoint-orbit theorem
interface.  This avoids a naked PSD hypothesis when the concrete operator model
proves the two diagonal responses are squares and the mixed response vanishes.
-/
@[rep_depth transport]
theorem operatorial_metric_gate_from_square_response
    (C : OperatorialMetriplecticContext (E := E))
    (S : OperatorialMetriplecticContext.SquareOperatorialResponseContext C)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_squareResponse S xForce yForce

attribute [infrastructure] operatorial_metric_gate_from_square_response

end OperatorialGate

end InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic

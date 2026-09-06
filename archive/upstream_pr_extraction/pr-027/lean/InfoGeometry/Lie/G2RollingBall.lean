import Mathlib.Tactic
import InfoGeometry.Lie.SagerschnigS2S3Distribution

/-!
# `G₂` and the rolling ball: theorem-safe algebraic core

This module formalizes kernel-checked fragments of John Huerta's
n-Category Café post "G₂ and the Rolling Ball".

The file records the parts that are native finite algebra and linear algebra:

* the elementary turn-count arithmetic for a ball of radius `r` rolling once
  around a fixed ball of radius `R`;
* the blog's `R = 3` coda for a unit rolling spinor on a projective plane;
* an abstract null-subalgebra incidence geometry and its functoriality under
  multiplication- and quadratic-form-preserving linear automorphisms;
* a bridge name for the already-existing explicit Sagerschnig `(2,3,5)`
  distribution model used for the rolling-ball/G₂ lane.

The scope is the finite algebraic and linear-algebraic content listed above,
together with the explicit Sagerschnig bridge.
-/

noncomputable section

namespace InfoGeometry.Lie.G2RollingBall

/-! ## Turn-count arithmetic -/

/-- Algebraic turn count for a ball of radius `r` rolling once around a fixed
sphere of radius `R`.  This is `(R + r) / r`; the physical use case assumes
`r > 0`, but the algebraic definition is total over `ℝ`. -/
def turnsAroundFixedSphere (R r : ℝ) : ℝ :=
  (R + r) / r

/-- The unit rolling-ball specialization used in the blog post. -/
def unitTurnsAroundFixedSphere (R : ℝ) : ℝ :=
  turnsAroundFixedSphere R 1

@[simp] theorem unitTurnsAroundFixedSphere_eq (R : ℝ) :
    unitTurnsAroundFixedSphere R = R + 1 := by
  simp [unitTurnsAroundFixedSphere, turnsAroundFixedSphere]

/-- Turning from a point to its antipode is half of the full great-circle trip. -/
def unitTurnsPointToAntipode (R : ℝ) : ℝ :=
  unitTurnsAroundFixedSphere R / 2

@[simp] theorem unitTurnsPointToAntipode_eq (R : ℝ) :
    unitTurnsPointToAntipode R = (R + 1) / 2 := by
  simp [unitTurnsPointToAntipode]

/-- For a unit rolling ball, four full turns around the fixed sphere force and
are forced by fixed radius `R = 3`. -/
theorem unit_four_turns_iff_radius_three (R : ℝ) :
    unitTurnsAroundFixedSphere R = 4 ↔ R = 3 := by
  rw [unitTurnsAroundFixedSphere_eq]
  constructor <;> intro h <;> linarith

/-- Equivalent antipodal version: the unit rolling ball turns twice on the
half-trip from a point to its antipode exactly when `R = 3`. -/
theorem unit_antipode_two_turns_iff_radius_three (R : ℝ) :
    unitTurnsPointToAntipode R = 2 ↔ R = 3 := by
  rw [unitTurnsPointToAntipode_eq]
  constructor <;> intro h <;> linarith

/-- General radius version: four turns around the fixed sphere are equivalent
to the fixed radius being three times the rolling radius, assuming `r ≠ 0`. -/
theorem four_turns_iff_radius_three_times {R r : ℝ} (hr : r ≠ 0) :
    turnsAroundFixedSphere R r = 4 ↔ R = 3 * r := by
  unfold turnsAroundFixedSphere
  constructor
  · intro h
    have hmul : R + r = 4 * r := by
      calc
        R + r = ((R + r) / r) * r := by field_simp [hr]
        _ = 4 * r := by rw [h]
    linarith
  · intro h
    subst R
    field_simp [hr]
    ring

/-- Half-trip version for arbitrary rolling radius. -/
theorem antipode_two_turns_iff_radius_three_times {R r : ℝ} (hr : r ≠ 0) :
    turnsAroundFixedSphere R r / 2 = 2 ↔ R = 3 * r := by
  constructor
  · intro h
    exact (four_turns_iff_radius_three_times (R := R) (r := r) hr).mp (by linarith)
  · intro h
    have h4 := (four_turns_iff_radius_three_times (R := R) (r := r) hr).mpr h
    linarith

/-! ## Abstract null-subalgebra incidence geometry -/

variable {A : Type*} [AddCommGroup A] [Module ℝ A] [Mul A] [Zero A]

/-- A submodule on which multiplication is identically zero. -/
def ProductZeroOn (U : Submodule ℝ A) : Prop :=
  ∀ ⦃x : A⦄, x ∈ U → ∀ ⦃y : A⦄, y ∈ U → x * y = 0

/-- A null subalgebra for a quadratic readout `Q`: every element is `Q`-null and
all products inside the submodule vanish.  Dimension is tracked through separate
rank hypotheses, and one- and two-dimensional versions can add them later. -/
structure NullSubalgebra (Q : A → ℝ) where
  carrier : Submodule ℝ A
  null' : ∀ ⦃x : A⦄, x ∈ carrier → Q x = 0
  product_zero' : ProductZeroOn carrier

namespace NullSubalgebra

variable {Q : A → ℝ}

/-- The quadratic null condition attached to a null subalgebra. -/
theorem null (U : NullSubalgebra (A := A) Q) {x : A} (hx : x ∈ U.carrier) :
    Q x = 0 :=
  U.null' hx

/-- Multiplication vanishes on a null subalgebra. -/
theorem product_zero (U : NullSubalgebra (A := A) Q) {x y : A}
    (hx : x ∈ U.carrier) (hy : y ∈ U.carrier) : x * y = 0 :=
  U.product_zero' hx hy

end NullSubalgebra

/-- Incidence of null subalgebras: the point-subspace lies on the line-subspace
when it is contained in it.  One-dimensional points and two-dimensional lines
are obtained by adding dimension hypotheses to the two arguments. -/
def NullIncident {Q : A → ℝ} (P L : NullSubalgebra (A := A) Q) : Prop :=
  P.carrier ≤ L.carrier

@[simp] theorem nullIncident_iff {Q : A → ℝ} (P L : NullSubalgebra (A := A) Q) :
    NullIncident P L ↔ P.carrier ≤ L.carrier :=
  Iff.rfl

/-- A linear automorphism preserving multiplication and a quadratic readout.
This is the theorem-safe abstraction of the `Aut(𝕆')` action used in the blog. -/
structure QuadraticMulAut (Q : A → ℝ) where
  toLinearEquiv : A ≃ₗ[ℝ] A
  map_mul' : ∀ x y : A, toLinearEquiv (x * y) = toLinearEquiv x * toLinearEquiv y
  map_zero_mul' : toLinearEquiv (0 : A) = 0
  preserve_Q' : ∀ x : A, Q (toLinearEquiv x) = Q x

namespace QuadraticMulAut

variable {Q : A → ℝ}

instance : CoeFun (QuadraticMulAut (A := A) Q) (fun _ => A → A) where
  coe g := g.toLinearEquiv

@[simp] theorem map_mul (g : QuadraticMulAut (A := A) Q) (x y : A) :
    g (x * y) = g x * g y :=
  g.map_mul' x y

@[simp] theorem map_zero (g : QuadraticMulAut (A := A) Q) : g (0 : A) = 0 :=
  g.map_zero_mul'

@[simp] theorem preserve_Q (g : QuadraticMulAut (A := A) Q) (x : A) :
    Q (g x) = Q x :=
  g.preserve_Q' x

/-- Image of a null subalgebra under a multiplication- and quadratic-form-
preserving linear automorphism. -/
def mapNullSubalgebra (g : QuadraticMulAut (A := A) Q)
    (U : NullSubalgebra (A := A) Q) : NullSubalgebra (A := A) Q where
  carrier := U.carrier.map g.toLinearEquiv.toLinearMap
  null' := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using (g.preserve_Q x).trans (U.null hx)
  product_zero' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    calc
      g.toLinearEquiv x * g.toLinearEquiv y = g.toLinearEquiv (x * y) := by
        exact (g.map_mul x y).symm
      _ = g.toLinearEquiv 0 := by rw [U.product_zero hx hy]
      _ = 0 := g.map_zero

@[simp] theorem mem_mapNullSubalgebra_iff (g : QuadraticMulAut (A := A) Q)
    (U : NullSubalgebra (A := A) Q) (z : A) :
    z ∈ (g.mapNullSubalgebra U).carrier ↔ ∃ x ∈ U.carrier, g x = z :=
  Iff.rfl

/-- Incidence is preserved by the induced action on null subalgebras. -/
theorem preserves_null_incidence (g : QuadraticMulAut (A := A) Q)
    {P L : NullSubalgebra (A := A) Q} (h : NullIncident P L) :
    NullIncident (g.mapNullSubalgebra P) (g.mapNullSubalgebra L) := by
  rintro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

end QuadraticMulAut

/-! ## Link to the existing explicit `(2,3,5)` distribution owner -/

/-- Alias for the existing explicit Sagerschnig distribution model.  This is the
coordinate `(2,3,5)` distribution surface already formalized in the repository;
the present file uses it as an owner bridge to the rolling-ball/G₂ lane. -/
abbrev sagerschnig235Distribution :=
  InfoGeometry.Lie.SagerschnigS2S3Distribution.sagerschnigDistribution

/-- Readback of the explicit Sagerschnig distribution formula through the
rolling-ball bridge namespace. -/
theorem sagerschnig235Distribution_formula
    (p : InfoGeometry.Lie.SagerschnigS2S3Distribution.S2xS3Point)
    (q : InfoGeometry.Lie.SagerschnigS2S3Distribution.S2xS3Tangent) :
    q ∈ sagerschnig235Distribution p ↔
      q ∈ InfoGeometry.Lie.SagerschnigS2S3Distribution.sagerschnigDistribution p := by
  rfl

end InfoGeometry.Lie.G2RollingBall

import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.Cl11LorentzAction
/-!
# InfoGeometry.Canonical.HestenesQVandermondeShadow

Finite operator-deformed collision shadow for the Hestenes/Lorentz lane.

This file is the honest operator replacement for the earlier scalar
`q`-Vandermonde proxy:

* the deformation parameter is a real linear operator `Q`,
* the two-node deformed factor is the vector difference `x - Q y`,
* collision means exact operator-locked equality `x = Q y`,
* the preserved quantity is a proof-carrying Lorentz/split quadratic readout,
  not the Euclidean norm,
* Euclidean norm preservation is isolated as an extra rotation-only subcase.

It does **not** claim a Clifford product theorem or a full noncommutative
Vandermonde determinant.  This is a finite operator-deformed collision owner.
-/

namespace InfoGeometry.Canonical.HestenesQVandermondeShadow

section TwoNode

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two-node operator-deformed collision chart. -/
@[rep_depth thermo]
structure TwoNodeHestenesChart (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  Q : E →ₗ[ℝ] E
  x : E
  y : E
  quadratic : E → ℝ
  quadraticInvariant : ∀ v : E, quadratic (Q v) = quadratic v

namespace TwoNodeHestenesChart

variable (C : TwoNodeHestenesChart E)

/-- The operator-deformed two-node collision factor. -/
@[rep_depth thermo]
def factor : E :=
  C.x - C.Q C.y

/-- Exact operator-deformed collision locus. -/
@[rep_depth thermo]
theorem factor_eq_zero_iff :
    C.factor = 0 ↔ C.x = C.Q C.y := by
  unfold factor
  constructor <;> intro h
  · simpa using sub_eq_zero.mp h
  · simp [h]

/-- Away from operator-deformed collision, the factor is nonzero. -/
@[rep_depth thermo]
theorem factor_ne_zero_iff :
    C.factor ≠ 0 ↔ C.x ≠ C.Q C.y := by
  exact not_congr C.factor_eq_zero_iff

/--
On the collision locus, the Lorentz/split quadratic readout is preserved between
the locked nodes.
-/
@[rep_depth thermo]
theorem quadratic_eq_of_collision
    (hcol : C.factor = 0) :
    C.quadratic C.x = C.quadratic C.y := by
  have hx : C.x = C.Q C.y := (C.factor_eq_zero_iff).1 hcol
  rw [hx, C.quadraticInvariant]

/--
Rotation-only subcase: if the deformation also preserves the ambient norm, the
locked nodes have equal Euclidean norm.
-/
@[rep_depth thermo]
theorem norm_eq_of_collision_of_normInvariant
    (hNorm : ∀ v : E, ‖C.Q v‖ = ‖v‖) (hcol : C.factor = 0) :
    ‖C.x‖ = ‖C.y‖ := by
  have hx : C.x = C.Q C.y := (C.factor_eq_zero_iff).1 hcol
  rw [hx, hNorm]

/-- Combined packet for the two-node Hestenes/Lorentz collision lane. -/
@[rep_depth thermo]
theorem two_node_hestenes_packet :
    (C.factor = 0 ↔ C.x = C.Q C.y)
    ∧ (C.factor ≠ 0 ↔ C.x ≠ C.Q C.y)
    ∧ ((C.factor = 0) → C.quadratic C.x = C.quadratic C.y) := by
  exact ⟨C.factor_eq_zero_iff, C.factor_ne_zero_iff, C.quadratic_eq_of_collision⟩

end TwoNodeHestenesChart

end TwoNode

section A2

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Three-node finite operator-deformed `A₂`-style chart. -/
@[rep_depth thermo]
structure A2HestenesChart (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  Q : E →ₗ[ℝ] E
  x : E
  y : E
  z : E
  quadratic : E → ℝ
  quadraticInvariant : ∀ v : E, quadratic (Q v) = quadratic v

namespace A2HestenesChart

variable (C : A2HestenesChart E)

/-- The three pairwise operator-deformed collision factors. -/
@[rep_depth thermo]
def factorYX : E := C.y - C.Q C.x

@[rep_depth thermo]
def factorZX : E := C.z - C.Q C.x

@[rep_depth thermo]
def factorZY : E := C.z - C.Q C.y

/-- Finite collision locus: one of the three deformed factors vanishes. -/
@[rep_depth thermo]
def Collision : Prop :=
  C.factorYX = 0 ∨ C.factorZX = 0 ∨ C.factorZY = 0

/--
On the finite collision locus, at least one Lorentz/split quadratic equality is
forced by the deformation invariance.
-/
@[rep_depth thermo]
theorem exists_quadratic_locked_pair_of_collision
    (hcol : C.Collision) :
    C.quadratic C.y = C.quadratic C.x
      ∨ C.quadratic C.z = C.quadratic C.x
      ∨ C.quadratic C.z = C.quadratic C.y := by
  rcases hcol with hyx | hzx | hzy
  · left
    have hyx' : C.y = C.Q C.x := by
      simpa [factorYX] using (sub_eq_zero.mp hyx)
    rw [hyx', C.quadraticInvariant]
  · right
    left
    have hzx' : C.z = C.Q C.x := by
      simpa [factorZX] using (sub_eq_zero.mp hzx)
    rw [hzx', C.quadraticInvariant]
  · right
    right
    have hzy' : C.z = C.Q C.y := by
      simpa [factorZY] using (sub_eq_zero.mp hzy)
    rw [hzy', C.quadraticInvariant]

/-- Optional rotation subcase for the finite three-node lane. -/
@[rep_depth thermo]
theorem exists_norm_locked_pair_of_collision_of_normInvariant
    (hNorm : ∀ v : E, ‖C.Q v‖ = ‖v‖) (hcol : C.Collision) :
    ‖C.y‖ = ‖C.x‖ ∨ ‖C.z‖ = ‖C.x‖ ∨ ‖C.z‖ = ‖C.y‖ := by
  rcases hcol with hyx | hzx | hzy
  · left
    have hyx' : C.y = C.Q C.x := by
      simpa [factorYX] using (sub_eq_zero.mp hyx)
    rw [hyx', hNorm]
  · right
    left
    have hzx' : C.z = C.Q C.x := by
      simpa [factorZX] using (sub_eq_zero.mp hzx)
    rw [hzx', hNorm]
  · right
    right
    have hzy' : C.z = C.Q C.y := by
      simpa [factorZY] using (sub_eq_zero.mp hzy)
    rw [hzy', hNorm]

/-- Combined packet for the finite operator-deformed `A₂` lane. -/
@[rep_depth thermo]
theorem a2_hestenes_packet :
    (C.Collision →
      C.quadratic C.y = C.quadratic C.x
        ∨ C.quadratic C.z = C.quadratic C.x
        ∨ C.quadratic C.z = C.quadratic C.y) := by
  intro hcol
  exact C.exists_quadratic_locked_pair_of_collision hcol

end A2HestenesChart

end A2

end InfoGeometry.Canonical.HestenesQVandermondeShadow

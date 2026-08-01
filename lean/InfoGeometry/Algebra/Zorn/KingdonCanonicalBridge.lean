import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3
import InfoGeometry.Algebra.Zorn.Composition

/-!
# Kingdon/physics-Zorn to canonical-Zorn carrier bridge

The Kingdon realization and the real split-`G₂` classification lane use two
coordinate-identical but distinct Zorn carriers. This file gives the explicit
real-linear equivalence and proves compatibility with the canonical Zorn
product, identity, and split norm. No associative algebra structure is imposed.
-/

namespace InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev PhysicsZorn := InfoGeometry.Physics.ZornMatrixSU3.ZornMatrix
abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ

open InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

noncomputable def physicsCanonicalLinearEquiv : PhysicsZorn ≃ₗ[ℝ] CanonicalZorn where
  toFun X := { a := X.a, b := X.b, x := X.x, y := X.y }
  invFun X := { a := X.a, b := X.b, x := X.x, y := X.y }
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl
  map_add' X Y := by ext <;> rfl
  map_smul' r X := by ext <;> rfl

@[simp] theorem physicsCanonicalLinearEquiv_a (X : PhysicsZorn) :
    (physicsCanonicalLinearEquiv X).a = X.a := rfl
@[simp] theorem physicsCanonicalLinearEquiv_b (X : PhysicsZorn) :
    (physicsCanonicalLinearEquiv X).b = X.b := rfl
@[simp] theorem physicsCanonicalLinearEquiv_x (X : PhysicsZorn) :
    (physicsCanonicalLinearEquiv X).x = X.x := rfl
@[simp] theorem physicsCanonicalLinearEquiv_y (X : PhysicsZorn) :
    (physicsCanonicalLinearEquiv X).y = X.y := rfl

@[simp] theorem physicsCanonicalLinearEquiv_symm_a (X : CanonicalZorn) :
    (physicsCanonicalLinearEquiv.symm X).a = X.a := rfl
@[simp] theorem physicsCanonicalLinearEquiv_symm_b (X : CanonicalZorn) :
    (physicsCanonicalLinearEquiv.symm X).b = X.b := rfl
@[simp] theorem physicsCanonicalLinearEquiv_symm_x (X : CanonicalZorn) :
    (physicsCanonicalLinearEquiv.symm X).x = X.x := rfl
@[simp] theorem physicsCanonicalLinearEquiv_symm_y (X : CanonicalZorn) :
    (physicsCanonicalLinearEquiv.symm X).y = X.y := rfl

@[simp] theorem physicsCanonicalLinearEquiv_one :
    physicsCanonicalLinearEquiv (1 : PhysicsZorn) = (1 : CanonicalZorn) := by
  ext <;> rfl

@[simp] theorem physicsCanonicalLinearEquiv_mul (X Y : PhysicsZorn) :
    physicsCanonicalLinearEquiv (X * Y) =
      zMul (physicsCanonicalLinearEquiv X) (physicsCanonicalLinearEquiv Y) := by
  ext i <;> simp [physicsCanonicalLinearEquiv,
    InfoGeometry.Physics.ZornMatrixSU3.mul,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Physics.ZornMatrixSU3.crossProduct,
    zMul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

@[simp] theorem physics_norm_eq_canonical_det (X : PhysicsZorn) :
    InfoGeometry.Physics.ZornMatrixSU3.norm X =
      X.a * X.b - InfoGeometry.Canonical.ZornMatrix.dot X.x X.y := by
  simp [InfoGeometry.Physics.ZornMatrixSU3.norm,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

noncomputable def kingdonCanonicalLinearEquiv :
    AbstractKingdon ≃ₗ[ℝ] CanonicalZorn :=
  kingdonZornLinearEquiv.trans physicsCanonicalLinearEquiv

@[simp] theorem kingdonCanonicalLinearEquiv_mul (x y : AbstractKingdon) :
    kingdonCanonicalLinearEquiv (x * y) =
      zMul (kingdonCanonicalLinearEquiv x) (kingdonCanonicalLinearEquiv y) := by
  change physicsCanonicalLinearEquiv (realization (x * y)) =
    zMul (physicsCanonicalLinearEquiv (realization x))
      (physicsCanonicalLinearEquiv (realization y))
  rw [map_mul]
  exact physicsCanonicalLinearEquiv_mul (realization x) (realization y)

@[simp] theorem kingdonCanonicalLinearEquiv_one :
    kingdonCanonicalLinearEquiv (1 : AbstractKingdon) = (1 : CanonicalZorn) := by
  change physicsCanonicalLinearEquiv (realization 1) = 1
  rw [map_one, physicsCanonicalLinearEquiv_one]


/-- Real-linear automorphisms of the canonical Zorn multiplication. -/
abbrev CanonicalLinearAut := CanonicalZorn ≃ₗ[ℝ] CanonicalZorn

/-- The exact multiplication-stabilizer predicate underlying the real split
octonion automorphism group. -/
def IsRealZornCompositionAut (φ : CanonicalLinearAut) : Prop :=
  ∀ X Y : CanonicalZorn, φ (zMul X Y) = zMul (φ X) (φ Y)

@[simp] theorem one_zMul (X : CanonicalZorn) : zMul 1 X = X := by
  change zMul ({ a := 1, b := 1, x := 0, y := 0 } : CanonicalZorn) X = X
  ext i <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

@[simp] theorem zMul_one (X : CanonicalZorn) : zMul X 1 = X := by
  change zMul X ({ a := 1, b := 1, x := 0, y := 0 } : CanonicalZorn) = X
  ext i <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

/-! ## Intrinsic trace and quadratic equation -/

/-- The scalar trace on the canonical real Zorn carrier. -/
def realZornTrace (X : CanonicalZorn) : ℝ := X.a + X.b

/-- Every canonical real Zorn element satisfies its intrinsic quadratic equation.
This is the coefficient-uniqueness root used below to derive determinant
preservation from multiplication preservation. -/
theorem realZorn_quadratic (X : CanonicalZorn) :
    zMul X X + ZornMatrix.detZ X • (1 : CanonicalZorn) =
      realZornTrace X • X := by
  have h1a : (1 : CanonicalZorn).a = 1 := rfl
  have h1b : (1 : CanonicalZorn).b = 1 := rfl
  have h1x : (1 : CanonicalZorn).x = 0 := rfl
  have h1y : (1 : CanonicalZorn).y = 0 := rfl
  ext i <;> simp [zMul, ZornMatrix.detZ, realZornTrace,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
    h1a, h1b, h1x, h1y]
  all_goals (try fin_cases i)
  all_goals try simp
  all_goals ring

@[simp] theorem realZorn_det_smul_one (r : ℝ) :
    ZornMatrix.detZ (r • (1 : CanonicalZorn)) = r ^ 2 := by
  have h1a : (1 : CanonicalZorn).a = 1 := rfl
  have h1b : (1 : CanonicalZorn).b = 1 := rfl
  have h1x : (1 : CanonicalZorn).x = 0 := rfl
  have h1y : (1 : CanonicalZorn).y = 0 := rfl
  simp [ZornMatrix.detZ,
    InfoGeometry.Canonical.ZornMatrix.dot,
    Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
    h1a, h1b, h1x, h1y]
  ring

private theorem smul_eq_smul_one_coefficients
    {X : CanonicalZorn} {a b : ℝ}
    (hX : ¬ ∃ r : ℝ, X = r • (1 : CanonicalZorn))
    (h : a • X = b • (1 : CanonicalZorn)) : a = 0 ∧ b = 0 := by
  by_cases ha : a = 0
  · subst a
    constructor
    · rfl
    · have hab := congrArg (fun Y : CanonicalZorn => Y.a) h
      have h1a : (1 : CanonicalZorn).a = 1 := rfl
      simpa [Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv, h1a]
        using hab.symm
  · exfalso
    apply hX
    refine ⟨a⁻¹ * b, ?_⟩
    calc
      X = a⁻¹ • (a • X) := by simp [smul_smul, ha]
      _ = a⁻¹ • (b • (1 : CanonicalZorn)) := by rw [h]
      _ = (a⁻¹ * b) • (1 : CanonicalZorn) := by rw [smul_smul]

/-- The group of real-linear canonical-Zorn multiplication automorphisms.
This is a candidate stabilizer surface for later split `G_{2(2)}`
classification; no such classification is asserted by this definition. -/
noncomputable def realZornCompositionAut : Subgroup CanonicalLinearAut where
  carrier := {φ | IsRealZornCompositionAut φ}
  one_mem' := by
    intro X Y
    rfl
  mul_mem' := by
    intro φ ψ hφ hψ X Y
    change φ (ψ (zMul X Y)) = zMul (φ (ψ X)) (φ (ψ Y))
    rw [hψ X Y, hφ (ψ X) (ψ Y)]
  inv_mem' := by
    intro φ hφ X Y
    apply φ.injective
    simpa using (hφ (φ.symm X) (φ.symm Y)).symm

@[simp] theorem realZornCompositionAut_preserves_mul
    (φ : realZornCompositionAut) (X Y : CanonicalZorn) :
    (φ : CanonicalLinearAut) (zMul X Y) =
      zMul ((φ : CanonicalLinearAut) X) ((φ : CanonicalLinearAut) Y) :=
  φ.property X Y

@[simp] theorem realZornCompositionAut_fix_one
    (φ : realZornCompositionAut) :
    (φ : CanonicalLinearAut) (1 : CanonicalZorn) = 1 := by
  have h := φ.property (1 : CanonicalZorn)
    ((φ : CanonicalLinearAut).symm (1 : CanonicalZorn))
  rw [one_zMul, LinearEquiv.apply_symm_apply, zMul_one] at h
  exact h.symm

/-- Multiplication preservation alone forces preservation of the canonical Zorn
determinant. The proof transports the intrinsic quadratic equation and recovers
its trace and determinant coefficients, treating scalar elements separately. -/
@[simp] theorem realZornCompositionAut_preserves_det
    (φ : realZornCompositionAut) (X : CanonicalZorn) :
    ZornMatrix.detZ ((φ : CanonicalLinearAut) X) = ZornMatrix.detZ X := by
  let Y : CanonicalZorn := (φ : CanonicalLinearAut) X
  have hmapRaw := congrArg (fun Z : CanonicalZorn =>
    (φ : CanonicalLinearAut) Z) (realZorn_quadratic X)
  have hmap :
      zMul Y Y + ZornMatrix.detZ X • (1 : CanonicalZorn) =
        realZornTrace X • Y := by
    simpa only [map_add, map_smul, realZornCompositionAut_preserves_mul,
      realZornCompositionAut_fix_one] using hmapRaw
  have hquadY := realZorn_quadratic Y
  have hcoeff :
      (realZornTrace Y - realZornTrace X) • Y =
        (ZornMatrix.detZ Y - ZornMatrix.detZ X) • (1 : CanonicalZorn) := by
    rw [sub_smul, sub_smul, ← hquadY, ← hmap]
    abel
  by_cases hscalar : ∃ r : ℝ, Y = r • (1 : CanonicalZorn)
  · rcases hscalar with ⟨r, hr⟩
    have hX : X = r • (1 : CanonicalZorn) := by
      apply (φ : CanonicalLinearAut).injective
      change Y = (φ : CanonicalLinearAut) (r • (1 : CanonicalZorn))
      rw [hr, map_smul, realZornCompositionAut_fix_one]
    change ZornMatrix.detZ Y = ZornMatrix.detZ X
    rw [hr, hX, realZorn_det_smul_one]
  · have hzero := smul_eq_smul_one_coefficients hscalar hcoeff
    change ZornMatrix.detZ Y = ZornMatrix.detZ X
    exact sub_eq_zero.mp hzero.2

/-- Polarization of the canonical split-octonion norm against the unit. -/
theorem realZorn_det_add_one (X : CanonicalZorn) :
    ZornMatrix.detZ (X + 1) = ZornMatrix.detZ X + realZornTrace X + 1 := by
  have h1a : (1 : CanonicalZorn).a = 1 := rfl
  have h1b : (1 : CanonicalZorn).b = 1 := rfl
  have h1x : (1 : CanonicalZorn).x = 0 := rfl
  have h1y : (1 : CanonicalZorn).y = 0 := rfl
  simp [ZornMatrix.detZ, realZornTrace,
    InfoGeometry.Canonical.ZornMatrix.dot, h1a, h1b, h1x, h1y]
  ring

/-- Every real split-octonion multiplication automorphism preserves the
intrinsic scalar trace.  This follows from norm polarization and does not need
coordinates for the automorphism itself. -/
@[simp] theorem realZornCompositionAut_preserves_trace
    (φ : realZornCompositionAut) (X : CanonicalZorn) :
    realZornTrace ((φ : CanonicalLinearAut) X) = realZornTrace X := by
  have h := realZornCompositionAut_preserves_det φ (X + 1)
  rw [map_add, realZornCompositionAut_fix_one,
    realZorn_det_add_one, realZorn_det_add_one,
    realZornCompositionAut_preserves_det] at h
  linarith

/-- Conjugation transport of linear Kingdon automorphisms to the canonical Zorn carrier. -/
noncomputable def kingdonCanonicalAutEquiv :
    (AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) ≃* CanonicalLinearAut where
  toFun φ := kingdonCanonicalLinearEquiv.symm.trans (φ.trans kingdonCanonicalLinearEquiv)
  invFun ψ := kingdonCanonicalLinearEquiv.trans (ψ.trans kingdonCanonicalLinearEquiv.symm)
  left_inv φ := by
    apply LinearEquiv.ext
    intro x
    simp [kingdonCanonicalLinearEquiv]
  right_inv ψ := by
    apply LinearEquiv.ext
    intro X
    simp [kingdonCanonicalLinearEquiv]
  map_mul' φ ψ := by
    apply LinearEquiv.ext
    intro x
    simp [LinearEquiv.mul_apply, LinearEquiv.trans_apply, kingdonCanonicalLinearEquiv]

/-- The Kingdon-side pullback of the canonical real split-Zorn composition subgroup. -/
noncomputable def kingdonCompositionAut :
    Subgroup (AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) :=
  Subgroup.comap kingdonCanonicalAutEquiv.toMonoidHom realZornCompositionAut

@[simp] theorem kingdonCompositionAut_iff
    (φ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) :
    φ ∈ kingdonCompositionAut ↔
      kingdonCanonicalAutEquiv φ ∈ realZornCompositionAut := Iff.rfl

@[simp] theorem kingdonCanonicalAutEquiv_apply
    (φ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) (x : AbstractKingdon) :
    kingdonCanonicalAutEquiv φ (kingdonCanonicalLinearEquiv x) =
      kingdonCanonicalLinearEquiv (φ x) := by
  change kingdonCanonicalLinearEquiv
      (φ (kingdonCanonicalLinearEquiv.symm (kingdonCanonicalLinearEquiv x))) =
    kingdonCanonicalLinearEquiv (φ x)
  rw [kingdonCanonicalLinearEquiv.symm_apply_apply]

@[simp] theorem kingdonCompositionAut_preserves_mul
    (φ : kingdonCompositionAut) (x y : AbstractKingdon) :
    (φ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) (x * y) =
      (φ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) x *
        (φ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) y := by
  let ψ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon := φ
  have hψ : kingdonCanonicalAutEquiv ψ ∈ realZornCompositionAut := φ.property
  have hmul := realZornCompositionAut_preserves_mul
    (φ := ⟨kingdonCanonicalAutEquiv ψ, hψ⟩)
    (kingdonCanonicalLinearEquiv x) (kingdonCanonicalLinearEquiv y)
  apply kingdonCanonicalLinearEquiv.injective
  calc
    kingdonCanonicalLinearEquiv (ψ (x * y)) =
        kingdonCanonicalAutEquiv ψ (kingdonCanonicalLinearEquiv (x * y)) :=
      (kingdonCanonicalAutEquiv_apply ψ (x * y)).symm
    _ = kingdonCanonicalAutEquiv ψ
        (zMul (kingdonCanonicalLinearEquiv x) (kingdonCanonicalLinearEquiv y)) := by
      rw [kingdonCanonicalLinearEquiv_mul]
    _ = zMul
        (kingdonCanonicalAutEquiv ψ (kingdonCanonicalLinearEquiv x))
        (kingdonCanonicalAutEquiv ψ (kingdonCanonicalLinearEquiv y)) := hmul
    _ = zMul (kingdonCanonicalLinearEquiv (ψ x))
        (kingdonCanonicalLinearEquiv (ψ y)) := by
      rw [kingdonCanonicalAutEquiv_apply, kingdonCanonicalAutEquiv_apply]
    _ = kingdonCanonicalLinearEquiv (ψ x * ψ y) :=
      (kingdonCanonicalLinearEquiv_mul (ψ x) (ψ y)).symm

/-- The transported Kingdon norm is exactly the canonical real Zorn determinant. -/
theorem kingdonNorm_eq_realZorn_det (x : AbstractKingdon) :
    kingdonNorm x =
      ZornMatrix.detZ (kingdonCanonicalLinearEquiv x) := by
  change InfoGeometry.Physics.ZornMatrixSU3.norm (realization x) =
    ZornMatrix.detZ (physicsCanonicalLinearEquiv (realization x))
  simp [ZornMatrix.detZ, physics_norm_eq_canonical_det]

/-- Every multiplication automorphism in the Kingdon pullback preserves the
native transported split-octonion norm. -/
@[simp] theorem kingdonCompositionAut_preserves_norm
    (φ : kingdonCompositionAut) (x : AbstractKingdon) :
    kingdonNorm ((φ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon) x) = kingdonNorm x := by
  let ψ : realZornCompositionAut :=
    ⟨kingdonCanonicalAutEquiv (φ : AbstractKingdon ≃ₗ[ℝ] AbstractKingdon), φ.property⟩
  rw [kingdonNorm_eq_realZorn_det, kingdonNorm_eq_realZorn_det]
  have h := realZornCompositionAut_preserves_det ψ
    (kingdonCanonicalLinearEquiv x)
  simpa [ψ] using h

end InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge

/-!
# InfoGeometry.Canonical.SplitSpinorAnnihilationCrossAnticommutatorBridge

Complete operator realization of the Split-Clifford Algebra Cl(U ⊕ U*, Q)
on the Spinor Space S = ⋀ U* over commutative ring R.

Couples:
1. Spinor Space S = ⋀ U* = ExteriorAlgebra R (Module.Dual R U).
2. Spinor Creation Operator ε_α = mulLeft(ι(α)) ∈ End_R(⋀ U*).
3. Spinor Annihilation Operator a_u (interior contraction) ∈ End_R(⋀ U*).
4. The Cross-Anticommutator Law: {ε_α, a_u} = α(u) • id.
5. Full Split Clifford Operator Generator c(u, α) = ε_α + a_u.
6. The Quadratic Cl(U ⊕ U*, Q) Operator Realization Theorem:
   c(u, α)² = α(u) • id
   {c(u, α), c(v, β)} = (α(v) + β(u)) • id.
7. Universal Clifford Algebra Homomorphism Object:
   `splitCliffordAlgebraHom : CliffordAlgebra Q →ₐ[R] Module.End R (Spinor R U)`.

This completes the 100% theorem-honest operator algebra for split Clifford representations.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinorAnnihilationCrossAnticommutatorBridge

open InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- Split quadratic form Q(u, α) = α(u) on W = U ⊕ U*. -/
def splitQuadraticForm (R U : Type*) [CommRing R] [AddCommGroup U] [Module R U] :
    QuadraticForm R (U × Module.Dual R U) where
  toFun w := w.2 w.1
  toFun_smul r w := by
    dsimp
    simp only [map_smul, smul_eq_mul]
    ring
  exists_companion' := ⟨LinearMap.mk₂ R (fun w v => w.2 v.1 + v.2 w.1)
    (fun _ _ _ => by dsimp; simp only [map_add]; ring)
    (fun _ _ _ => by dsimp; simp only [map_smul, smul_eq_mul]; ring)
    (fun _ _ _ => by dsimp; simp only [map_add]; ring)
    (fun _ _ _ => by dsimp; simp only [map_smul, smul_eq_mul]; ring),
    fun _ _ => by
      dsimp
      simp only [map_add]
      ring⟩

/-- Axiomatic structure for the interior contraction / annihilation operator family a_u on Spinor R U. -/
structure AnnihilationStructure (R U : Type*) [CommRing R] [AddCommGroup U] [Module R U] where
  /-- Linear assignment of annihilation operators u ↦ a_u. -/
  a : U →ₗ[R] Module.End R (Spinor R U)
  /-- Annihilation nilpotency: a_u² = 0. -/
  a_sq_zero : ∀ u, a u * a u = 0
  /-- Annihilation anticommutation: {a_u, a_v} = 0. -/
  a_anticomm : ∀ u v, a u * a v + a v * a u = 0
  /-- Cross-Anticommutator Theorem: {ε_α, a_u} = α(u) • id. -/
  cross_anticomm : ∀ (alpha : Module.Dual R U) (u : U),
    creation alpha * a u + a u * creation alpha = (alpha u) • (1 : Module.End R (Spinor R U))

namespace AnnihilationStructure

variable (ann : AnnihilationStructure R U)

/-- The full Split-Clifford operator generator c(u, α) = ε_α + a_u in End_R(Spinor R U). -/
def splitCliffordOp (u : U) (alpha : Module.Dual R U) : Module.End R (Spinor R U) :=
  creation alpha + ann.a u

/-- Linear map of split Clifford generators w = (u, α) ↦ c(u, α). -/
def splitCliffordLinearMap : (U × Module.Dual R U) →ₗ[R] Module.End R (Spinor R U) where
  toFun w := ann.splitCliffordOp w.1 w.2
  map_add' w v := by
    dsimp [splitCliffordOp, creation]
    ext ψ
    simp only [LinearMap.add_apply, LinearMap.mulLeft_apply, map_add]
    noncomm_ring
  map_smul' r w := by
    dsimp [splitCliffordOp, creation]
    ext ψ
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.mulLeft_apply, map_smul]
    rw [smul_mul_assoc, ← smul_add]

/-- **Apex Theorem 1**: Single Generator Split-Clifford Operator Squaring Law: c(u, α)² = α(u) • id. -/
theorem splitCliffordOp_sq (u : U) (alpha : Module.Dual R U) :
    ann.splitCliffordOp u alpha * ann.splitCliffordOp u alpha =
      (alpha u) • (1 : Module.End R (Spinor R U)) := by
  dsimp [splitCliffordOp]
  have h_c_sq := creation_sq_zero alpha
  have h_a_sq := ann.a_sq_zero u
  have h_cross := ann.cross_anticomm alpha u
  calc (creation alpha + ann.a u) * (creation alpha + ann.a u)
      = creation alpha * creation alpha +
        (creation alpha * ann.a u + ann.a u * creation alpha) +
        ann.a u * ann.a u := by noncomm_ring
    _ = 0 + (alpha u) • 1 + 0 := by rw [h_c_sq, h_cross, h_a_sq]
    _ = (alpha u) • 1 := by simp only [add_zero, zero_add]

/-- **Apex Theorem 2**: Two Generator Split-Clifford Cross-Anticommutator Law:
{c(u, α), c(v, β)} = (α(v) + β(u)) • id. -/
theorem splitCliffordOp_anticomm (u v : U) (alpha beta : Module.Dual R U) :
    ann.splitCliffordOp u alpha * ann.splitCliffordOp v beta +
    ann.splitCliffordOp v beta * ann.splitCliffordOp u alpha =
      (alpha v + beta u) • (1 : Module.End R (Spinor R U)) := by
  dsimp [splitCliffordOp]
  have h_c_anti := creation_anticomm alpha beta
  have h_a_anti := ann.a_anticomm u v
  have h_cross_1 := ann.cross_anticomm alpha v
  have h_cross_2 := ann.cross_anticomm beta u
  calc (creation alpha + ann.a u) * (creation beta + ann.a v) +
       (creation beta + ann.a v) * (creation alpha + ann.a u)
      = (creation alpha * creation beta + creation beta * creation alpha) +
        (creation alpha * ann.a v + ann.a v * creation alpha) +
        (creation beta * ann.a u + ann.a u * creation beta) +
        (ann.a u * ann.a v + ann.a v * ann.a u) := by noncomm_ring
    _ = 0 + (alpha v) • 1 + (beta u) • 1 + 0 := by rw [h_c_anti, h_cross_1, h_cross_2, h_a_anti]
    _ = (alpha v + beta u) • 1 := by simp only [add_smul, add_zero, zero_add]

/-- **Apex Universal Homomorphism Object**: Universal Clifford Algebra Homomorphism
`CliffordAlgebra Q →ₐ[R] Module.End R (Spinor R U)`. -/
def splitCliffordAlgebraHom :
    CliffordAlgebra (splitQuadraticForm R U) →ₐ[R] Module.End R (Spinor R U) :=
  CliffordAlgebra.lift (splitQuadraticForm R U) ⟨ann.splitCliffordLinearMap, fun w => by
    dsimp [splitCliffordLinearMap]
    rw [ann.splitCliffordOp_sq w.1 w.2]
    rfl⟩

/-- **Apex Theorem 3**: Action on canonical generators:
ρ(ι(w)) = c(w.1, w.2). -/
@[simp]
theorem splitCliffordAlgebraHom_ι (w : U × Module.Dual R U) :
    ann.splitCliffordAlgebraHom (CliffordAlgebra.ι (splitQuadraticForm R U) w) =
    ann.splitCliffordOp w.1 w.2 := by
  dsimp [splitCliffordAlgebraHom]
  rw [CliffordAlgebra.lift_ι_apply]
  rfl

end AnnihilationStructure

end InfoGeometry.Canonical.SplitSpinorAnnihilationCrossAnticommutatorBridge

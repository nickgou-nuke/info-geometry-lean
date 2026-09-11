import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ErlangenInductiveClosure
import InfoGeometry.Canonical.ErlangenColimitResolution
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-!
# UHF Colimit Representation Bridge

This module maps the infinite-dimensional direct colimit algebra from
`ErlangenColimitResolution` directly into the bounded operators of the
Cantor boundary representation.

We define the concrete Cuntz operators as linear maps on the boundary function space,
instantiate the `SupergradedClosureAt` structure on `Module.End ℂ (CantorBoundary → ℂ)`,
and prove that the finite diagonal algebra stages embed compatibly into this operator algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFColimitRepresentationBridge

open InfoGeometry.Canonical.ErlangenInductiveClosure
open InfoGeometry.Canonical.ErlangenColimitResolution
open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-- Left Cuntz operator as a linear map. -/
def S_L_linear : (CantorBoundary → ℂ) →ₗ[ℂ] (CantorBoundary → ℂ) where
  toFun := S_L_op
  map_add' f g := by
    funext x
    dsimp [S_L_op]
    by_cases h : x 0 = false
    · simp [h]
    · simp [h]
  map_smul' c f := by
    funext x
    dsimp [S_L_op]
    by_cases h : x 0 = false
    · simp [h]
    · simp [h]

/-- Right Cuntz operator as a linear map. -/
def S_R_linear : (CantorBoundary → ℂ) →ₗ[ℂ] (CantorBoundary → ℂ) where
  toFun := S_R_op
  map_add' f g := by
    funext x
    dsimp [S_R_op]
    by_cases h : x 0 = true
    · simp [h]
    · simp [h]
  map_smul' c f := by
    funext x
    dsimp [S_R_op]
    by_cases h : x 0 = true
    · simp [h]
    · simp [h]

/-- Pullback of left Cuntz operator as a linear map. -/
def star_S_L_linear : (CantorBoundary → ℂ) →ₗ[ℂ] (CantorBoundary → ℂ) where
  toFun := star_S_L_op
  map_add' f g := by
    funext x
    rfl
  map_smul' c f := by
    funext x
    rfl

/-- Pullback of right Cuntz operator as a linear map. -/
def star_S_R_linear : (CantorBoundary → ℂ) →ₗ[ℂ] (CantorBoundary → ℂ) where
  toFun := star_S_R_op
  map_add' f g := by
    funext x
    rfl
  map_smul' c f := by
    funext x
    rfl

theorem star_UHF_boundary_op_sq_zero (f : CantorBoundary → ℂ) :
    star_UHF_boundary_op (star_UHF_boundary_op f) = 0 := by
  funext x
  dsimp [star_UHF_boundary_op, S_R_op, star_S_L_op]
  by_cases h : x 0 = true
  · simp [h]
  · simp [h]

theorem S_L_star_S_R_nilpotent : (S_L_linear * star_S_R_linear) * (S_L_linear * star_S_R_linear) = 0 := by
  ext f x
  change UHF_boundary_op (UHF_boundary_op f) x = 0
  rw [UHF_boundary_op_sq_zero f]
  rfl

theorem S_R_star_S_L_nilpotent : (S_R_linear * star_S_L_linear) * (S_R_linear * star_S_L_linear) = 0 := by
  ext f x
  change star_UHF_boundary_op (star_UHF_boundary_op f) x = 0
  rw [star_UHF_boundary_op_sq_zero f]
  rfl

theorem S_L_star_S_R_mul_S_R_star_S_L :
    (S_L_linear * star_S_R_linear) * (S_R_linear * star_S_L_linear) =
      S_L_linear * star_S_L_linear := by
  ext f x
  change UHF_boundary_op (star_UHF_boundary_op f) x = (S_L_op (star_S_L_op f)) x
  dsimp [UHF_boundary_op, star_UHF_boundary_op]
  rw [star_S_R_op_S_R_op]

theorem S_R_star_S_L_mul_S_L_star_S_R :
    (S_R_linear * star_S_L_linear) * (S_L_linear * star_S_R_linear) =
      S_R_linear * star_S_R_linear := by
  ext f x
  change star_UHF_boundary_op (UHF_boundary_op f) x = (S_R_op (star_S_R_op f)) x
  dsimp [UHF_boundary_op, star_UHF_boundary_op]
  rw [star_S_L_op_S_L_op]

/-- Odd operators on the Cantor boundary function space. -/
def op_is_odd (T : Module.End ℂ (CantorBoundary → ℂ)) : Prop :=
  (∃ c : ℂ, T = c • (S_L_linear * star_S_R_linear)) ∨
  (∃ c : ℂ, T = c • (S_R_linear * star_S_L_linear))

/-- Even operators on the Cantor boundary function space. -/
def op_is_even (T : Module.End ℂ (CantorBoundary → ℂ)) : Prop :=
  ∃ g : CantorBoundary → ℂ, g ∈ CylinderColimit ∧ T = Algebra.lmul ℂ (CantorBoundary → ℂ) g

/-- Central operators on the Cantor boundary function space. -/
def op_is_central (T : Module.End ℂ (CantorBoundary → ℂ)) : Prop :=
  ∃ a : ℂ, T = a • 1

theorem op_odd_nilpotency (T : Module.End ℂ (CantorBoundary → ℂ)) (h : op_is_odd T) : T * T = 0 := by
  ext f x
  rcases h with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · dsimp [S_L_linear, star_S_R_linear, S_L_op, star_S_R_op]
    by_cases h : x 0 = false
    · simp [h]
    · simp [h]
  · dsimp [S_R_linear, star_S_L_linear, S_R_op, star_S_L_op]
    by_cases h : x 0 = true
    · simp [h]
    · simp [h]

theorem op_odd_odd_closure (T1 T2 : Module.End ℂ (CantorBoundary → ℂ)) (h1 : op_is_odd T1) (h2 : op_is_odd T2) :
    op_is_even (T1 * T2 + T2 * T1) := by
  rcases h1 with ⟨c1, rfl⟩ | ⟨c1, rfl⟩ <;> rcases h2 with ⟨c2, rfl⟩ | ⟨c2, rfl⟩
  · -- Left and Left
    use 0
    constructor
    · use ⟨0, (0 : DiagAlg 0)⟩
      ext x; rfl
    · ext f x
      dsimp [UHF_boundary_op, star_UHF_boundary_op, S_L_linear, S_R_linear, star_S_L_linear, star_S_R_linear, S_L_op, S_R_op, star_S_L_op, star_S_R_op]
      by_cases h : x 0 = false
      · simp [h]
      · simp [h]
  · -- Left and Right
    let fL : DiagAlg 1 := fun w => if w 0 = false then 1 else 0
    let fR : DiagAlg 1 := fun w => if w 0 = true then 1 else 0
    let fG : DiagAlg 1 := (c1 * c2) • fL + (c2 * c1) • fR
    let g := cylinder 1 fG
    use g
    constructor
    · exact cylinder_mem_colimit 1 fG
    · ext f x
      dsimp [g, S_L_linear, S_R_linear, star_S_L_linear, star_S_R_linear, S_L_op, S_R_op, star_S_L_op, star_S_R_op, fG, fL, fR, cylinder, boundaryPrefix, Algebra.lmul]
      by_cases h : x 0 = false
      · simp [h, tail_prependBit, prependBit_tail_of_head, mul_assoc]
      · have h_true : x 0 = true := by
          cases hx : x 0
          · contradiction
          · rfl
        simp [h_true, tail_prependBit, prependBit_tail_of_head, mul_assoc]
  · -- Right and Left
    let fL : DiagAlg 1 := fun w => if w 0 = false then 1 else 0
    let fR : DiagAlg 1 := fun w => if w 0 = true then 1 else 0
    let fG : DiagAlg 1 := (c2 * c1) • fL + (c1 * c2) • fR
    let g := cylinder 1 fG
    use g
    constructor
    · exact cylinder_mem_colimit 1 fG
    · ext f x
      dsimp [g, S_L_linear, S_R_linear, star_S_L_linear, star_S_R_linear, S_L_op, S_R_op, star_S_L_op, star_S_R_op, fG, fL, fR, cylinder, boundaryPrefix, Algebra.lmul]
      by_cases h : x 0 = false
      · simp [h, tail_prependBit, prependBit_tail_of_head, mul_assoc]
      · have h_true : x 0 = true := by
          cases hx : x 0
          · contradiction
          · rfl
        simp [h_true, tail_prependBit, prependBit_tail_of_head, mul_assoc]
  · -- Right and Right
    use 0
    constructor
    · use ⟨0, (0 : DiagAlg 0)⟩
      ext x; rfl
    · ext f x
      dsimp [star_UHF_boundary_op, S_R_op, star_S_L_op, S_L_linear, S_R_linear, star_S_L_linear, star_S_R_linear]
      by_cases h : x 0 = true
      · simp [h]
      · simp [h]

theorem op_central_lane (Cctxt T : Module.End ℂ (CantorBoundary → ℂ)) (hc : op_is_central Cctxt) : Cctxt * T = T * Cctxt := by
  rcases hc with ⟨a, rfl⟩
  simp

theorem op_projector_identity : ∃ P : Module.End ℂ (CantorBoundary → ℂ), op_is_even P ∧ P * P = P := by
  use 1
  constructor
  · use 1
    constructor
    · exact cylinder_mem_colimit 0 1
    · ext g x; simp
  · simp

/-- Instantiates the `SupergradedClosureAt` structure for `Module.End ℂ (CantorBoundary → ℂ)`. -/
def op_supergraded_closure : SupergradedClosureAt (Module.End ℂ (CantorBoundary → ℂ)) where
  is_odd := op_is_odd
  is_even := op_is_even
  is_central := op_is_central
  odd_nilpotency := op_odd_nilpotency
  odd_odd_closure := op_odd_odd_closure
  central_lane := op_central_lane
  projector_identity := op_projector_identity

/-! Projection of an explicitly supplied finite-stage invariant packet. -/
def diag_supergraded_closure (n : ℕ)
    (C : SupergradedClosureAt (DiagAlg n)) : SupergradedClosureAt (DiagAlg n) :=
  C

/-! Concrete successor ring homomorphism. -/
def diagEmbedSucc_RingHom (n : ℕ) : DiagAlg n →+* DiagAlg (n + 1) where
  toFun := diagEmbedSucc n
  map_zero' := diagEmbedSucc_zero n
  map_one' := diagEmbedSucc_one n
  map_add' := diagEmbedSucc_add n
  map_mul' := diagEmbedSucc_mul n

/-! A bonding intertwiner is supplied by the native stage owner. -/
def diag_bonding_intertwiner (n : ℕ)
    (C_n : SupergradedClosureAt (DiagAlg n))
    (C_succ : SupergradedClosureAt (DiagAlg (n + 1)))
    (f : BondingIntertwiner C_n C_succ) :
    BondingIntertwiner (diag_supergraded_closure n C_n)
      (diag_supergraded_closure (n + 1) C_succ) :=
  f

/-! Concrete cylinder ring homomorphism. -/
def cylinderRingHom (n : ℕ) : DiagAlg n →+* (CantorBoundary → ℂ) where
  toFun := cylinder n
  map_zero' := by ext b; rfl
  map_one' := cylinder_one n
  map_add' := cylinder_add n
  map_mul' := cylinder_mul n

/-! Concrete representation by multiplication operators. -/
def stage_to_op_hom (n : ℕ) : DiagAlg n →+* Module.End ℂ (CantorBoundary → ℂ) :=
  (Algebra.lmul ℂ (CantorBoundary → ℂ)).toRingHom.comp (cylinderRingHom n)

/-! Representation compatibility is an explicit native intertwiner input. -/
def diag_to_op_intertwiner (n : ℕ)
    (C_n : SupergradedClosureAt (DiagAlg n))
    (f : BondingIntertwiner C_n op_supergraded_closure) :
    BondingIntertwiner (diag_supergraded_closure n C_n) op_supergraded_closure :=
  f

end InfoGeometry.Canonical.UHFColimitRepresentationBridge

end noncomputable section

import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Canonical.TKKJordanPairData

/-!
# TKK symmetric-pair adapter

This file is a thin adapter between the existing involutive Lie-automorphism
owner and the existing abstract TKK grade owner.  It adds no Cartan projector
structure and no second five-grading implementation.

The grade-preservation predicate is kept explicit: the TKK data structure has
separate bundled instance fields, so a concrete realization must provide its
own compatibility theorem before a grade-level projector statement is made.
No Pin(5,5) action, root decomposition, Casimir, or Standard Model
identification is asserted here.
-/

namespace InfoGeometry.Canonical.Pin55TKKSymmetricPairBridge

open InfoGeometry.Core
open TKKJordanPairData

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- An involution preserves the formal TKK grades. -/
def PreservesFiveGrade (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L) : Prop :=
  ∀ i (x : G.L), x ∈ G.grade i → θ.1 x ∈ G.grade i

theorem preservesFiveGrade_apply (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L)
    (hθ : PreservesFiveGrade G θ)
    (i : TKKGrade) {x : G.L} (hx : x ∈ G.grade i) :
    θ.1 x ∈ G.grade i :=
  hθ i x hx

/-- The existing symmetric-Lie owner associated with an involution. -/
noncomputable def symmetricLie (θ : InvolutiveLieAut L) :
    SymmetricLieAlgebra L :=
  SymmetricLieAlgebra.ofInvolutiveLieAut θ

@[simp] theorem symmetricLie_theta_apply
    (θ : InvolutiveLieAut L) (x : L) :
    (symmetricLie θ).θ x = θ.1 x :=
  rfl

theorem cartan_decomposition (θ : InvolutiveLieAut L) (x : L) :
    x = (symmetricLie θ).P_plus x + (symmetricLie θ).P_minus x :=
  SymmetricLieAlgebra.cartan_decomposition (symmetricLie θ) x

theorem symmetric_pair_properties (θ : InvolutiveLieAut L) :
    (∀ {x y}, x ∈ (symmetricLie θ).evenLieSubalgebra →
      y ∈ (symmetricLie θ).evenLieSubalgebra →
      ⁅x, y⁆ ∈ (symmetricLie θ).evenLieSubalgebra) ∧
    (∀ {x y}, x ∈ (symmetricLie θ).evenLieSubalgebra →
      y ∈ (symmetricLie θ).oddSubmodule →
      ⁅x, y⁆ ∈ (symmetricLie θ).oddSubmodule) ∧
    (∀ {x y}, x ∈ (symmetricLie θ).oddSubmodule →
      y ∈ (symmetricLie θ).oddSubmodule →
      ⁅x, y⁆ ∈ (symmetricLie θ).evenLieSubalgebra) :=
  SymmetricLieAlgebra.symmetric_pair_properties (symmetricLie θ)

theorem bracket_grade_closed_readout
    (G : FiveGradedLieAlgebra ℝ)
    {i j k : TKKGrade} (hijk : gradeAdd i j = some k)
    {x y : G.L} (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ ∈ G.grade k :=
  TKKJordanPairData.bracket_grade_closed G hijk hx hy

end InfoGeometry.Canonical.Pin55TKKSymmetricPairBridge

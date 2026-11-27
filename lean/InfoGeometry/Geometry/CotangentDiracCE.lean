/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Cochain
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-! # Cotangent graph integrability and the native CE differential
The graph is `LinearMap.graph` and the differential is Mathlib's actual `d₂₃`.
Scalar coefficients use `TrivialLieModule`; no new conflicting scalar action
is installed. These are Lie-algebraic statements, without smooth integration. -/

namespace InfoGeometry.Geometry.CotangentDiracCE
open LieModule.Cohomology
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

abbrev Scalar (R L : Type*) := TrivialLieModule R L R
abbrev Covector (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] :=
  L →ₗ[R] Scalar R L
abbrev Cotangent (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] :=
  L × Covector R L

/-- The cotangent semidirect bracket, equal to the pointwise Dorfman bracket. -/
def cotangentBracket (a b : Cotangent R L) : Cotangent R L :=
  (⁅a.1, b.1⁆, ⁅a.1, b.2⁆ - ⁅b.1, a.2⁆)

@[simp] theorem cotangentBracket_fst (a b : Cotangent R L) :
    (cotangentBracket a b).1 = ⁅a.1, b.1⁆ := rfl

@[simp] theorem cotangentBracket_snd_apply (a b : Cotangent R L) (z : L) :
    (cotangentBracket a b).2 z = -b.2 ⁅a.1, z⁆ + a.2 ⁅b.1, z⁆ := by
  simp [cotangentBracket, LieHom.lie_apply, trivial_lie_zero, sub_neg_eq_add]

theorem cotangentBracket_dorfman (a b : Cotangent R L) (z : L) :
    (cotangentBracket a b).2 z =
      ⁅a.1, b.2⁆ z - d₁₂ R L (Scalar R L) a.2 b.1 z := by
  simp [cotangentBracket, LieHom.lie_apply, trivial_lie_zero]

theorem cotangentBracket_self (a : Cotangent R L) : cotangentBracket a a = 0 := by
  simp [cotangentBracket]

def neutralPairing (a b : Cotangent R L) : Scalar R L := a.2 b.1 + b.2 a.1

theorem graph_isotropic (B : twoCochain R L (Scalar R L)) (x y : L) :
    neutralPairing (x, B x) (y, B y) = 0 := by
  dsimp [neutralPairing]
  rw [← twoCochain_skew B x y, add_neg_cancel]

/-- The graph equals its neutral orthogonal complement. In particular its
isotropy is maximal, without a finite-dimensionality assumption. -/
theorem mem_graph_iff_neutral_orthogonal
    (B : twoCochain R L (Scalar R L)) (a : Cotangent R L) :
    a ∈ B.val.graph ↔ ∀ x : L, neutralPairing a (x, B x) = 0 := by
  rw [LinearMap.mem_graph_iff]
  constructor
  · intro ha x
    change a.2 x + B x a.1 = 0
    rw [ha]
    exact graph_isotropic B a.1 x
  · intro h
    apply LinearMap.ext
    intro x
    have hx := h x
    change a.2 x + B x a.1 = 0 at hx
    rw [← twoCochain_skew B a.1 x] at hx
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, twoCochain_val_apply] using hx

/-- The graph bracket defect is exactly contraction of the native CE differential. -/
theorem graph_bracket_defect (B : twoCochain R L (Scalar R L)) (x y z : L) :
    (cotangentBracket (x, B x) (y, B y)).2 z - B ⁅x, y⁆ z =
      d₂₃ R L (Scalar R L) B x y z := by
  rw [cotangentBracket_snd_apply, d₂₃_apply]
  simp only [trivial_lie_zero, zero_sub, neg_zero, add_zero]
  rw [← twoCochain_skew B y ⁅x, z⁆, ← twoCochain_skew B x ⁅y, z⁆]
  abel

def GraphBracketClosed (B : twoCochain R L (Scalar R L)) : Prop :=
  ∀ a ∈ B.val.graph, ∀ b ∈ B.val.graph, cotangentBracket a b ∈ B.val.graph

theorem graphBracketClosed_iff_dCE_eq_zero (B : twoCochain R L (Scalar R L)) :
    GraphBracketClosed B ↔ d₂₃ R L (Scalar R L) B = 0 := by
  constructor
  · intro h
    ext x y z
    have hc := h (x, B x) (by simp [LinearMap.mem_graph_iff])
      (y, B y) (by simp [LinearMap.mem_graph_iff])
    rw [LinearMap.mem_graph_iff] at hc
    have hz := congrArg (fun f : Covector R L => f z) hc
    rw [← graph_bracket_defect]
    exact sub_eq_zero.mpr hz
  · intro h a ha b hb
    rw [LinearMap.mem_graph_iff] at ha hb ⊢
    rcases a with ⟨x, ξ⟩
    rcases b with ⟨y, η⟩
    dsimp at ha hb
    subst ξ
    subst η
    ext z
    apply sub_eq_zero.mp
    simp only [cotangentBracket_fst, twoCochain_val_apply]
    rw [graph_bracket_defect, h]
    rfl

/-- An actual linear B-transform automorphism. -/
def bTransform (B : twoCochain R L (Scalar R L)) :
    Cotangent R L ≃ₗ[R] Cotangent R L where
  toFun a := (a.1, a.2 + B a.1)
  invFun a := (a.1, a.2 - B a.1)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  map_add' a b := by ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' r a := by ext <;> simp

@[simp] theorem bTransform_apply (B : twoCochain R L (Scalar R L))
    (a : Cotangent R L) : bTransform B a = (a.1, a.2 + B a.1) := rfl

theorem bTransform_preserves_pairing (B : twoCochain R L (Scalar R L))
    (a b : Cotangent R L) :
    neutralPairing (bTransform B a) (bTransform B b) = neutralPairing a b := by
  simp only [neutralPairing, bTransform_apply, LinearMap.add_apply]
  rw [← twoCochain_skew B a.1 b.1]
  abel

/-- B-transform compatibility fails by precisely the CE three-form. -/
theorem bTransform_bracket_defect (B : twoCochain R L (Scalar R L))
    (a b : Cotangent R L) (z : L) :
    (cotangentBracket (bTransform B a) (bTransform B b)).2 z -
      (bTransform B (cotangentBracket a b)).2 z =
      d₂₃ R L (Scalar R L) B a.1 b.1 z := by
  rw [← graph_bracket_defect]
  simp only [cotangentBracket_snd_apply, bTransform_apply,
    LinearMap.add_apply, cotangentBracket_fst]
  abel

theorem bTransform_preserves_bracket_iff (B : twoCochain R L (Scalar R L)) :
    (∀ a b, cotangentBracket (bTransform B a) (bTransform B b) =
      bTransform B (cotangentBracket a b)) ↔ d₂₃ R L (Scalar R L) B = 0 := by
  constructor
  · intro h
    ext x y z
    have hz := congrArg (fun a : Cotangent R L => a.2 z) (h (x, 0) (y, 0))
    rw [← bTransform_bracket_defect B (x, 0) (y, 0) z]
    exact sub_eq_zero.mpr hz
  · intro h a b
    apply Prod.ext
    · rfl
    · ext z
      apply sub_eq_zero.mp
      rw [bTransform_bracket_defect, h]
      rfl

/-- The displayed cotangent bracket satisfies all native Lie-ring laws.
The structure is explicit, avoiding a competing global product bracket. -/
@[instance_reducible]
def cotangentLieRing : LieRing (Cotangent R L) where
  toAddCommGroup := inferInstance
  bracket := cotangentBracket
  add_lie a b c := by
    apply Prod.ext
    · exact add_lie a.1 b.1 c.1
    · simp only [cotangentBracket, Prod.fst_add, Prod.snd_add, add_lie, lie_add]
      abel
  lie_add a b c := by
    apply Prod.ext
    · exact lie_add a.1 b.1 c.1
    · simp only [cotangentBracket, Prod.fst_add, Prod.snd_add, add_lie, lie_add]
      abel
  lie_self := cotangentBracket_self
  leibniz_lie a b c := by
    apply Prod.ext
    · exact leibniz_lie a.1 b.1 c.1
    · simp only [cotangentBracket, Prod.snd_add, lie_sub, lie_lie]
      abel

/-- The cotangent semidirect Lie algebra on the original product module. -/
@[instance_reducible]
def cotangentLieAlgebra :
    letI := cotangentLieRing (R := R) (L := L)
    LieAlgebra R (Cotangent R L) := by
  letI := cotangentLieRing (R := R) (L := L)
  exact
    { toModule := inferInstance
      lie_smul := fun r a b => by
        apply Prod.ext
        · exact lie_smul r a.1 b.1
        · change ⁅a.1, r • b.2⁆ - ⁅r • b.1, a.2⁆ =
            r • (⁅a.1, b.2⁆ - ⁅b.1, a.2⁆)
          rw [lie_smul, smul_lie, smul_sub] }

/-- A closed CE two-cochain produces an actual native Lie subalgebra graph. -/
def graphLieSubalgebra (B : twoCochain R L (Scalar R L))
    (hB : d₂₃ R L (Scalar R L) B = 0) :
    letI := cotangentLieRing (R := R) (L := L)
    letI := cotangentLieAlgebra (R := R) (L := L)
    LieSubalgebra R (Cotangent R L) := by
  letI := cotangentLieRing (R := R) (L := L)
  letI := cotangentLieAlgebra (R := R) (L := L)
  exact
    { B.val.graph with
      lie_mem' := fun ha hb => (graphBracketClosed_iff_dCE_eq_zero B).mpr hB _ ha _ hb }

/-- The B-transform of a closed native CE two-cochain is a Lie equivalence. -/
def bTransformLieEquiv (B : twoCochain R L (Scalar R L))
    (hB : d₂₃ R L (Scalar R L) B = 0) :
    letI := cotangentLieRing (R := R) (L := L)
    letI := cotangentLieAlgebra (R := R) (L := L)
    Cotangent R L ≃ₗ⁅R⁆ Cotangent R L := by
  letI := cotangentLieRing (R := R) (L := L)
  letI := cotangentLieAlgebra (R := R) (L := L)
  exact
    { bTransform B with
      map_lie' := fun {a b} => ((bTransform_preserves_bracket_iff B).mpr hB a b).symm }

end InfoGeometry.Geometry.CotangentDiracCE

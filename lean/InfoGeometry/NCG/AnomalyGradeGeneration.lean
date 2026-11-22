/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.ZornCommutator
import InfoGeometry.NCG.PeirceGradingOperator
import InfoGeometry.NCG.TrialitySingletLieDerivation
import InfoGeometry.NCG.CausalPoset
import Mathlib.Tactic

/-!
# Peirce Components of Associator and Jacobiator Defects

This file records exact Peirce-component readouts for the repository's native
nonassociative `OpZornMatrix A` carrier. Every element, including an
associator or Jacobiator, decomposes into two diagonal corners and two
off-diagonal corners. This decomposition alone does **not** imply that a
nonzero defect has a nonzero off-diagonal component.

The file proves the native ordered `skewCross` product and associator formulas
for specified homogeneous inputs, the universal four-component decomposition,
and the criterion that a Jacobiator is diagonal exactly when both of its
off-diagonal components vanish. The Jacobiator–associator identity and the
sector-specific Jacobi/associativity results are owned by the imported modules.

All results use the actual `OpZornMatrix A` multiplication over `[Ring A]`;
this carrier is nonassociative in general. No alternate Zorn multiplication or
commutative/scalar surrogate is introduced. A nonzero defect is not asserted
to generate a particular grade without a theorem identifying its component
and proving that component nonzero. -/

namespace InfoGeometry.NCG.AnomalyGradeGeneration

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator
open InfoGeometry.NCG.PeirceGradingOperator
open InfoGeometry.NCG.TrialitySingletLieDerivation
open InfoGeometry.NCG.CausalPoset

/-- The noncommutative vector triple-product identity.  The scalar
contractions act on the indicated side, so the proof uses the ordered
coefficient products and associativity of `A`, but never commutativity. -/
theorem noncommutative_bac_cab
    (u w v : OpVec3 A) :
    OpVec3.leftScale (OpVec3.dot u w) v -
        OpVec3.rightScale u (OpVec3.dot w v) =
      OpVec3.naiveCross (OpVec3.naiveCross u w) v -
        OpVec3.naiveCross u (OpVec3.naiveCross w v) := by
  ext <;>
    simp [OpVec3.dot, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- Peirce corner block extraction of any operator X:
  P₊·X·P₊ (P₊-corner), P₋·X·P₋ (P₋-corner),
  P₊·X·P₋ (off-diagonal +), P₋·X·P₊ (off-diagonal -). -/
def peirce_pp (X : OpZornMatrix A) : OpZornMatrix A := P_plus * X * P_plus
def peirce_mm (X : OpZornMatrix A) : OpZornMatrix A := P_minus * X * P_minus
def peirce_pm (X : OpZornMatrix A) : OpZornMatrix A := P_plus * X * P_minus
def peirce_mp (X : OpZornMatrix A) : OpZornMatrix A := P_minus * X * P_plus

/-- The two off-diagonal Peirce grades, using the repository's actual Zorn
carrier and ordered coefficient operations. -/
def fockRaise (u : OpVec3 A) : OpZornMatrix A := ⟨0, u, 0, 0⟩
def fockLower (w : OpVec3 A) : OpZornMatrix A := ⟨0, 0, w, 0⟩

/-- The particle-hole coordinate exchange on the existing Zorn carrier. It
swaps the two diagonal coordinates and the two off-diagonal Peirce coordinates. -/
def particleHoleReflect (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.b, X.w, X.v, X.a⟩

/-- Particle-hole exchange is an involution on the Zorn carrier. -/
@[simp] theorem particleHoleReflect_involutive (X : OpZornMatrix A) :
    particleHoleReflect (particleHoleReflect X) = X := by
  cases X
  rfl

/-- The reflection exchanges the two off-diagonal Peirce embeddings. -/
@[simp] theorem particleHoleReflect_fockRaise (u : OpVec3 A) :
    particleHoleReflect (fockRaise u) = fockLower u := rfl

@[simp] theorem particleHoleReflect_fockLower (w : OpVec3 A) :
    particleHoleReflect (fockLower w) = fockRaise w := rfl

/-- P₊·X·P₊ = ⟨X.a, 0, 0, 0⟩: only the P₊-scalar survives. -/
@[simp] theorem peirce_pp_eq (X : OpZornMatrix A) :
    peirce_pp X = ⟨X.a, 0, 0, 0⟩ := by
  ext <;>
  simp [peirce_pp, P_plus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- P₋·X·P₋ = ⟨0, 0, 0, X.b⟩: only the P₋-scalar survives. -/
@[simp] theorem peirce_mm_eq (X : OpZornMatrix A) :
    peirce_mm X = ⟨0, 0, 0, X.b⟩ := by
  ext <;>
  simp [peirce_mm, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- P₊·X·P₋ = ⟨0, X.v, 0, 0⟩: the upper off-diagonal block. -/
@[simp] theorem peirce_pm_eq (X : OpZornMatrix A) :
    peirce_pm X = ⟨0, X.v, 0, 0⟩ := by
  ext <;>
  simp [peirce_pm, P_plus, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- P₋·X·P₊ = ⟨0, 0, X.w, 0⟩: the lower off-diagonal block. -/
@[simp] theorem peirce_mp_eq (X : OpZornMatrix A) :
    peirce_mp X = ⟨0, 0, X.w, 0⟩ := by
  ext <;>
  simp [peirce_mp, P_plus, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- Peirce decomposition of any operator into four component readouts:
  `X = P₊·X·P₊ + P₋·X·P₋ + P₊·X·P₋ + P₋·X·P₊`.
This is a coordinate decomposition; it makes no nonvanishing claim about any
component of a particular defect. -/
theorem peirce_decomposition (X : OpZornMatrix A) :
    X = peirce_pp X + peirce_mm X + peirce_pm X + peirce_mp X := by
  rw [peirce_pp_eq, peirce_mm_eq, peirce_pm_eq, peirce_mp_eq]
  ext <;>
  simp [P_plus, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale,
    OpZornMatrix.add_a, OpZornMatrix.add_b, OpZornMatrix.add_v, OpZornMatrix.add_w] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- A nonzero operator, in particular a nonzero associator or Jacobiator
defect, has at least one nonzero Peirce component. This does not assert that
the component is off-diagonal or belongs to any prescribed grade. -/
theorem nonzero_has_nonzero_peirce_component (X : OpZornMatrix A) :
    X ≠ 0 ↔ peirce_pp X ≠ 0 ∨ peirce_mm X ≠ 0 ∨
      peirce_pm X ≠ 0 ∨ peirce_mp X ≠ 0 := by
  constructor
  · intro hX
    by_contra h
    push_neg at h
    rcases h with ⟨hpp, hmm, hpm, hmp⟩
    apply hX
    calc
      X = peirce_pp X + peirce_mm X + peirce_pm X + peirce_mp X :=
        peirce_decomposition X
      _ = 0 := by rw [hpp, hmm, hpm, hmp]; simp
  · rintro (hpp | hmm | hpm | hmp) hX
    · apply hpp
      rw [peirce_pp_eq, hX]
      rfl
    · apply hmm
      rw [peirce_mm_eq, hX]
      rfl
    · apply hpm
      rw [peirce_pm_eq, hX]
      rfl
    · apply hmp
      rw [peirce_mp_eq, hX]
      rfl

/-!
## Product and associator anomalies

The coefficient-valued cross operation in this owner is `skewCross`, not the
naive coordinate cross product. The identities below therefore record the
actual image of each anomaly in the opposite Peirce grade, without assuming
commutativity of `A`.
-/

/-- Same-grade products need not vanish: their exact defect is the
`skewCross` element in the opposite odd Peirce grade. -/
theorem odd_product_anomaly_generates_opposite_grade
    (u₁ u₂ w₁ w₂ : OpVec3 A) :
    fockRaise u₁ * fockRaise u₂ = fockLower (OpVec3.skewCross u₁ u₂) ∧
    fockLower w₁ * fockLower w₂ = -fockRaise (OpVec3.skewCross w₁ w₂) := by
  constructor <;>
    ext <;>
    simp [fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The upper odd-grade embedding is injective, so its image is zero exactly
when its vector coordinate is zero. -/
theorem fockRaise_eq_zero_iff (u : OpVec3 A) : fockRaise u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun X : OpZornMatrix A => X.v) h
    simpa [fockRaise] using hv
  · rintro rfl
    rfl

/-- The lower odd-grade embedding has the corresponding exact support
criterion. -/
theorem fockLower_eq_zero_iff (w : OpVec3 A) : fockLower w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have hw := congrArg (fun X : OpZornMatrix A => X.w) h
    simpa [fockLower] using hw
  · rintro rfl
    rfl

/-- A same-grade product anomaly is nonzero exactly when its opposite-grade
`skewCross` component is nonzero. No nonvanishing claim is made for arbitrary
inputs or coefficient rings. -/
theorem odd_product_anomaly_nonzero_iff
    (u₁ u₂ w₁ w₂ : OpVec3 A) :
    (fockRaise u₁ * fockRaise u₂ ≠ 0 ↔
      OpVec3.skewCross u₁ u₂ ≠ 0) ∧
    (fockLower w₁ * fockLower w₂ ≠ 0 ↔
      OpVec3.skewCross w₁ w₂ ≠ 0) := by
  rcases odd_product_anomaly_generates_opposite_grade u₁ u₂ w₁ w₂ with
    ⟨hUpper, hLower⟩
  constructor
  · rw [hUpper]
    exact (fockLower_eq_zero_iff (OpVec3.skewCross u₁ u₂)).not
  · rw [hLower]
    simpa using (fockRaise_eq_zero_iff (OpVec3.skewCross w₁ w₂)).not

/-- Swapping the arguments of the coordinate cross product leaves exactly
the coefficient commutators. This is the ordered noncommutative braiding
defect; it need not vanish over a noncommutative coefficient ring. -/
theorem naive_cross_braiding_defect_eq_commutators (p q : OpVec3 A) :
    OpVec3.naiveCross p q + OpVec3.naiveCross q p =
      ⟨p.y * q.z - q.z * p.y - (p.z * q.y - q.y * p.z),
       p.z * q.x - q.x * p.z - (p.x * q.z - q.z * p.x),
       p.x * q.y - q.y * p.x - (p.y * q.x - q.x * p.y)⟩ := by
  ext <;>
    simp [OpVec3.naiveCross] <;>
    noncomm_ring

/-- The naive cross-product braiding defect vanishes exactly when its three
displayed coefficient commutators vanish. This identifies the precise
commutativity condition needed for the swapped cross products to cancel. -/
theorem naive_cross_braiding_defect_eq_zero_iff (p q : OpVec3 A) :
    OpVec3.naiveCross p q + OpVec3.naiveCross q p = 0 ↔
      (p.y * q.z - q.z * p.y = p.z * q.y - q.y * p.z) ∧
      (p.z * q.x - q.x * p.z = p.x * q.z - q.z * p.x) ∧
      (p.x * q.y - q.y * p.x = p.y * q.x - q.x * p.y) := by
  rw [naive_cross_braiding_defect_eq_commutators]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hx := congrArg OpVec3.x h
      exact sub_eq_zero.mp (by simpa using hx)
    · have hy := congrArg OpVec3.y h
      exact sub_eq_zero.mp (by simpa using hy)
    · have hz := congrArg OpVec3.z h
      exact sub_eq_zero.mp (by simpa using hz)
  · rintro ⟨hx, hy, hz⟩
    ext <;> simp [hx, hy, hz]

/-- Three upper odd-grade elements have an associator entirely in the two
diagonal Peirce corners. Signs reflect the owner multiplication
`a = a₁a₂ - dot(v₁,w₂)`, `b = -dot(w₁,v₂) + b₁b₂`. -/
theorem triple_raise_associator_corner_anomaly (u₁ u₂ u₃ : OpVec3 A) :
    opAssociator (fockRaise u₁) (fockRaise u₂) (fockRaise u₃) =
      peirce_pp ⟨OpVec3.dot u₁ (OpVec3.skewCross u₂ u₃), 0, 0, 0⟩ +
      peirce_mm ⟨0, 0, 0, -OpVec3.dot (OpVec3.skewCross u₁ u₂) u₃⟩ := by
  ext <;>
    simp [opAssociator, peirce_pp_eq, peirce_mm_eq,
      fockRaise, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The three-raising associator vanishes exactly when both ordered diagonal
Peirce coefficients vanish. This strengthens the component formula to a
complete vanishing criterion without identifying the two contractions or
assuming that either one is nonzero. -/
theorem triple_raise_associator_eq_zero_iff (u₁ u₂ u₃ : OpVec3 A) :
    opAssociator (fockRaise u₁) (fockRaise u₂) (fockRaise u₃) = 0 ↔
      OpVec3.dot u₁ (OpVec3.skewCross u₂ u₃) = 0 ∧
        OpVec3.dot (OpVec3.skewCross u₁ u₂) u₃ = 0 := by
  rw [triple_raise_associator_corner_anomaly]
  constructor
  · intro h
    have ha := congrArg (fun X : OpZornMatrix A => X.a) h
    have hb := congrArg (fun X : OpZornMatrix A => X.b) h
    simp [peirce_pp_eq, peirce_mm_eq] at ha hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    ext <;> simp [peirce_pp_eq, peirce_mm_eq, ha, hb]

/-- The lower odd-grade triple has the complementary ordered corner formula.
It is stated independently because the two ordered contractions need not be
identified in a noncommutative coefficient ring. -/
theorem triple_lower_associator_corner_anomaly (w₁ w₂ w₃ : OpVec3 A) :
    opAssociator (fockLower w₁) (fockLower w₂) (fockLower w₃) =
      peirce_pp ⟨OpVec3.dot (OpVec3.skewCross w₁ w₂) w₃, 0, 0, 0⟩ +
      peirce_mm ⟨0, 0, 0, -OpVec3.dot w₁ (OpVec3.skewCross w₂ w₃)⟩ := by
  ext <;>
    simp [opAssociator, peirce_pp_eq, peirce_mm_eq,
      fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The three-lowering associator vanishes exactly when both ordered diagonal
Peirce coefficients vanish. The two tests retain their distinct contraction
orders, as required over a noncommutative coefficient ring. -/
theorem triple_lower_associator_eq_zero_iff (w₁ w₂ w₃ : OpVec3 A) :
    opAssociator (fockLower w₁) (fockLower w₂) (fockLower w₃) = 0 ↔
      OpVec3.dot (OpVec3.skewCross w₁ w₂) w₃ = 0 ∧
        OpVec3.dot w₁ (OpVec3.skewCross w₂ w₃) = 0 := by
  rw [triple_lower_associator_corner_anomaly]
  constructor
  · intro h
    have ha := congrArg (fun X : OpZornMatrix A => X.a) h
    have hb := congrArg (fun X : OpZornMatrix A => X.b) h
    simp [peirce_pp_eq, peirce_mm_eq] at ha hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    ext <;> simp [peirce_pp_eq, peirce_mm_eq, ha, hb]

/-- A mixed associator of two upper odd-grade elements and one lower one lands
in the upper odd grade. This is the ordered double-`skewCross` anomaly. -/
theorem mixed_raise_associator_grade_anomaly (u₁ u₂ w : OpVec3 A) :
    opAssociator (fockRaise u₁) (fockRaise u₂) (fockLower w) =
      fockRaise (-(OpVec3.skewCross (OpVec3.skewCross u₁ u₂) w)) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- With one upper and two lower inputs, the associator is the ordered
iterated `skewCross` in the lower Peirce grade. -/
theorem raise_lower_lower_associator_exact (u : OpVec3 A) (w₁ w₂ : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w₁) (fockLower w₂) =
      fockLower (OpVec3.skewCross u (OpVec3.skewCross w₁ w₂)) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- A lower-upper-lower triple has an exact lower-grade contraction formula;
the two scalar actions retain their original sides. -/
theorem lower_raise_lower_associator_exact (w₁ : OpVec3 A) (u : OpVec3 A)
    (w₂ : OpVec3 A) :
    opAssociator (fockLower w₁) (fockRaise u) (fockLower w₂) =
      fockLower
        (OpVec3.leftScale (-(OpVec3.dot w₁ u)) w₂ -
          OpVec3.rightScale w₁ (-(OpVec3.dot u w₂))) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- A lower-lower-upper triple has an exact lower-grade formula with the
ordered double cross term and right coefficient action. -/
theorem lower_lower_raise_associator_exact (w₁ w₂ : OpVec3 A) (u : OpVec3 A) :
    opAssociator (fockLower w₁) (fockLower w₂) (fockRaise u) =
      fockLower (-OpVec3.skewCross (OpVec3.skewCross w₁ w₂) u) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- A lower-upper-upper triple has the corresponding exact upper-grade
iterated `skewCross` formula. -/
theorem lower_raise_raise_associator_exact (w : OpVec3 A) (u₁ u₂ : OpVec3 A) :
    opAssociator (fockLower w) (fockRaise u₁) (fockRaise u₂) =
      fockRaise (OpVec3.skewCross w (OpVec3.skewCross u₁ u₂)) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The four mixed associators vanish exactly when their ordered vector
residuals vanish.  Together with the exact formulas above, this identifies
the full vanishing locus without assuming that any particular residual is
nonzero. -/
theorem mixed_associator_zero_iff_ordered_residuals
    (u w₁ w₂ : OpVec3 A) (v : OpVec3 A) :
    (opAssociator (fockRaise u) (fockLower w₁) (fockLower w₂) = 0 ↔
      OpVec3.skewCross u (OpVec3.skewCross w₁ w₂) = 0) ∧
    (opAssociator (fockLower w₁) (fockRaise u) (fockLower w₂) = 0 ↔
      OpVec3.leftScale (-(OpVec3.dot w₁ u)) w₂ -
        OpVec3.rightScale w₁ (-(OpVec3.dot u w₂)) = 0) ∧
    (opAssociator (fockLower w₁) (fockLower w₂) (fockRaise v) = 0 ↔
      -OpVec3.skewCross (OpVec3.skewCross w₁ w₂) v = 0) ∧
    (opAssociator (fockLower w₁) (fockRaise u) (fockRaise w₂) = 0 ↔
      OpVec3.skewCross w₁ (OpVec3.skewCross u w₂) = 0) := by
  constructor
  · rw [raise_lower_lower_associator_exact]
    exact fockLower_eq_zero_iff _
  constructor
  · rw [lower_raise_lower_associator_exact]
    exact fockLower_eq_zero_iff _
  constructor
  · rw [lower_lower_raise_associator_exact]
    exact fockLower_eq_zero_iff _
  · rw [lower_raise_raise_associator_exact]
    exact fockRaise_eq_zero_iff _

/-- The other particle-hole-particle ordering has an exact contraction
formula.  The two scalar actions remain on their original sides; in a
noncommutative coefficient ring they cannot be interchanged. -/
theorem raise_lower_raise_associator_exact (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) =
      fockRaise (-OpVec3.leftScale (OpVec3.dot u w) v +
        OpVec3.rightScale u (OpVec3.dot w v)) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The two mixed-grade orderings omitted from
`mixed_associator_zero_iff_ordered_residuals` also have exact vanishing
criteria. Together the two theorems cover all six words containing both
Peirce grades, retaining the ordered residuals over a noncommutative ring. -/
theorem remaining_mixed_associator_zero_iff_ordered_residuals
    (u₁ u₂ w v : OpVec3 A) :
    (opAssociator (fockRaise u₁) (fockRaise u₂) (fockLower w) = 0 ↔
      -OpVec3.skewCross (OpVec3.skewCross u₁ u₂) w = 0) ∧
    (opAssociator (fockRaise u₁) (fockLower w) (fockRaise v) = 0 ↔
      -OpVec3.leftScale (OpVec3.dot u₁ w) v +
        OpVec3.rightScale u₁ (OpVec3.dot w v) = 0) := by
  constructor
  · rw [mixed_raise_associator_grade_anomaly]
    exact fockRaise_eq_zero_iff _
  · rw [raise_lower_raise_associator_exact]
    exact fockRaise_eq_zero_iff _

/-- Exact residual for the three particle-hole/particle associators after
exchanging the upper and lower Peirce sectors in the two reflected terms.
The result is stated with the repository's actual `skewCross`; it does not
assert cancellation. -/
theorem reflected_associator_sum_exact (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u) (fockRaise w) (fockLower v) +
      opAssociator (fockLower u) (fockRaise w) (fockRaise v) =
    fockRaise
      (-OpVec3.leftScale (OpVec3.dot u w) v +
        OpVec3.rightScale u (OpVec3.dot w v) -
        OpVec3.skewCross (OpVec3.skewCross u w) v +
        OpVec3.skewCross u (OpVec3.skewCross w v)) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The ordered triple-product associator for the unsymmetrized cross
operation. -/
def naiveCrossAssociator (u w v : OpVec3 A) : OpVec3 A :=
  OpVec3.naiveCross (OpVec3.naiveCross u w) v -
    OpVec3.naiveCross u (OpVec3.naiveCross w v)

/-- The corresponding associator for the repository's skew-symmetrized
operator cross product. -/
def skewCrossAssociator (u w v : OpVec3 A) : OpVec3 A :=
  OpVec3.skewCross (OpVec3.skewCross u w) v -
    OpVec3.skewCross u (OpVec3.skewCross w v)

/-- Factor the reflected-cut defect into the sum of the naive and skew-cross
associators.  The noncommutative BAC--CAB identity converts the contraction
part exactly; the remaining skew-cross term is retained as a separate grade
correction instead of being assumed to cancel. -/
theorem reflected_associator_sum_eq_neg_cross_associator_sum
    (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u) (fockRaise w) (fockLower v) +
      opAssociator (fockLower u) (fockRaise w) (fockRaise v) =
    fockRaise (-(naiveCrossAssociator u w v + skewCrossAssociator u w v)) := by
  rw [reflected_associator_sum_exact]
  apply congrArg fockRaise
  ext <;>
    simp [naiveCrossAssociator, skewCrossAssociator,
      OpVec3.dot, OpVec3.naiveCross, OpVec3.skewCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The reflected-cut identity expressed using the actual particle-hole
operator on `OpZornMatrix A`. Its residual is the negative sum of the naive
and native skew-cross associators. Thus the reflection does not by itself
make the obstruction vanish; its exact vanishing condition is recorded below. -/
theorem particleHole_reflected_associator_residual
    (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u)
        (particleHoleReflect (fockLower w))
        (particleHoleReflect (fockRaise v)) +
      opAssociator (particleHoleReflect (fockRaise u))
        (particleHoleReflect (fockLower w)) (fockRaise v) =
      fockRaise (-(naiveCrossAssociator u w v + skewCrossAssociator u w v)) := by
  simpa using reflected_associator_sum_eq_neg_cross_associator_sum u w v

/-- The particle-hole reflected associator sum vanishes exactly when the
naive and native skew-cross associator corrections cancel. This is the exact
cut-elimination criterion on the noncommutative coefficient carrier. -/
theorem particleHole_reflected_associator_sum_eq_zero_iff
    (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u)
        (particleHoleReflect (fockLower w))
        (particleHoleReflect (fockRaise v)) +
      opAssociator (particleHoleReflect (fockRaise u))
        (particleHoleReflect (fockLower w)) (fockRaise v) = 0 ↔
      naiveCrossAssociator u w v + skewCrossAssociator u w v = 0 := by
  rw [particleHole_reflected_associator_residual, fockRaise_eq_zero_iff]
  constructor
  · intro h
    have hx := congrArg OpVec3.x h
    have hy := congrArg OpVec3.y h
    have hz := congrArg OpVec3.z h
    ext
    · exact neg_eq_zero.mp hx
    · exact neg_eq_zero.mp hy
    · exact neg_eq_zero.mp hz
  · intro h
    rw [h]
    ext <;> simp [OpVec3.neg_x, OpVec3.neg_y, OpVec3.neg_z]

/-- The reflected three-associator cancellation criterion in factored form.
The noncommutative BAC--CAB contribution is already accounted for by
`naiveCrossAssociator`; cancellation holds exactly when its sum with the
native `skewCrossAssociator` correction vanishes. -/
theorem reflected_associator_sum_eq_zero_iff_cross_associators
    (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u) (fockRaise w) (fockLower v) +
      opAssociator (fockLower u) (fockRaise w) (fockRaise v) = 0 ↔
    naiveCrossAssociator u w v + skewCrossAssociator u w v = 0 := by
  rw [reflected_associator_sum_eq_neg_cross_associator_sum]
  rw [fockRaise_eq_zero_iff]
  constructor
  · intro h
    have hx := congrArg OpVec3.x h
    have hy := congrArg OpVec3.y h
    have hz := congrArg OpVec3.z h
    ext
    · exact neg_eq_zero.mp (by simpa using hx)
    · exact neg_eq_zero.mp (by simpa using hy)
    · exact neg_eq_zero.mp (by simpa using hz)
  · intro h
    rw [h]
    ext <;> simp [OpVec3.neg_x, OpVec3.neg_y, OpVec3.neg_z]

/-- The proposed reflected cancellation holds precisely when its native
`skewCross` residual vanishes. This is an iff, not a universal cancellation
claim. -/
theorem reflected_associator_sum_eq_zero_iff (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u) (fockRaise w) (fockLower v) +
      opAssociator (fockLower u) (fockRaise w) (fockRaise v) = 0 ↔
    -OpVec3.leftScale (OpVec3.dot u w) v +
      OpVec3.rightScale u (OpVec3.dot w v) -
      OpVec3.skewCross (OpVec3.skewCross u w) v +
      OpVec3.skewCross u (OpVec3.skewCross w v) = 0 := by
  rw [reflected_associator_sum_exact]
  exact fockRaise_eq_zero_iff _

/-- The Jacobiator's Peirce corner blocks are even-grade components. -/
theorem jacobiator_peirce_corners_even
    (X Y Z : OpZornMatrix A) :
    peirce_pp (zornJacobiator X Y Z) = P_plus * zornJacobiator X Y Z * P_plus ∧
    peirce_mm (zornJacobiator X Y Z) = P_minus * zornJacobiator X Y Z * P_minus := by
  refine ⟨rfl, rfl⟩

/-- The Jacobiator's off-diagonal Peirce components are η-odd:
  `η·J₊₋·η = -J₊₋` and `η·J₋₊·η = -J₋₊`.
This identifies their parity, not their nonvanishing. -/
theorem jacobiator_peirce_offdiag_odd
    (X Y Z : OpZornMatrix A) :
    peirce_pm (zornJacobiator X Y Z) = P_plus * zornJacobiator X Y Z * P_minus ∧
    peirce_mp (zornJacobiator X Y Z) = P_minus * zornJacobiator X Y Z * P_plus ∧
    eta_grading * peirce_pm (zornJacobiator X Y Z) * eta_grading =
      -peirce_pm (zornJacobiator X Y Z) ∧
    eta_grading * peirce_mp (zornJacobiator X Y Z) * eta_grading =
      -peirce_mp (zornJacobiator X Y Z) := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
  simp [peirce_pm_eq, peirce_mp_eq] <;>
  ext <;>
  simp [peirce_pp_eq, peirce_mm_eq, peirce_pm_eq, peirce_mp_eq,
    eta_grading, instMulOpZornMatrix, instNegOpZornMatrix,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- On the x-axis sector, the owner-proved Jacobi identity implies that all
four Peirce components vanish. This theorem supplies the sector inputs itself;
it does not assume the Jacobiator is zero. -/
theorem jacobiator_vanishes_on_xaxis_all_peirce_blocks
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    peirce_pp (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 ∧
    peirce_mm (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 ∧
    peirce_pm (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 ∧
    peirce_mp (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 := by
  rw [zornJacobiator_vanishes_on_quatSubalgX]
  simp [peirce_pp, peirce_mm, peirce_pm, peirce_mp]

/-- The associator's Peirce corner blocks are even-grade components. -/
theorem associator_peirce_corners_even
    (X Y Z : OpZornMatrix A) :
    peirce_pp (opAssociator X Y Z) = P_plus * opAssociator X Y Z * P_plus ∧
    peirce_mm (opAssociator X Y Z) = P_minus * opAssociator X Y Z * P_minus := by
  refine ⟨rfl, rfl⟩

/-- The associator's off-diagonal Peirce components are η-odd:
  `η·Ass₊₋·η = -Ass₊₋` and `η·Ass₋₊·η = -Ass₋₊`.
This identifies their parity, not their nonvanishing. -/
theorem associator_peirce_offdiag_odd
    (X Y Z : OpZornMatrix A) :
    peirce_pm (opAssociator X Y Z) = P_plus * opAssociator X Y Z * P_minus ∧
    peirce_mp (opAssociator X Y Z) = P_minus * opAssociator X Y Z * P_plus ∧
    eta_grading * peirce_pm (opAssociator X Y Z) * eta_grading =
      -peirce_pm (opAssociator X Y Z) ∧
    eta_grading * peirce_mp (opAssociator X Y Z) * eta_grading =
      -peirce_mp (opAssociator X Y Z) := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
  simp [peirce_pm_eq, peirce_mp_eq] <;>
  ext <;>
  simp [peirce_pp_eq, peirce_mm_eq, peirce_pm_eq, peirce_mp_eq,
    eta_grading, instMulOpZornMatrix, instNegOpZornMatrix,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- On the triality-singlet sector, the owner-proved associativity theorem
implies that all four Peirce components vanish. The inputs are quantified
explicitly; associator-vanishing is not assumed as a premise. -/
theorem associator_vanishes_on_singlet_all_peirce_blocks
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) :
    peirce_pp (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 ∧
    peirce_mm (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 ∧
    peirce_pm (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 ∧
    peirce_mp (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 := by
  rw [opAssociator_zornSinglet_eq_zero]
  simp [peirce_pp, peirce_mm, peirce_pm, peirce_mp]

/-- The universal Jacobiator component formula: the Jacobiator decomposes into
  Peirce grade blocks:
    J(X,Y,Z) = J₊₊ + J₋₋ + J₊₋ + J₋₊
  where J₊₊ = P₊·J·P₊ and J₋₋ = P₋·J·P₋ are diagonal corner readouts,
  and J₊₋ = P₊·J·P₋ and J₋₊ = P₋·J·P₊ are off-diagonal readouts.
  On the x-axis sector, all four blocks vanish (Jacobi holds there). For a
  general triple this decomposition alone says nothing about which blocks are
  nonzero, and does not assert that a block generates a grade. -/
theorem jacobiator_peirce_grade_decomposition
    (X Y Z : OpZornMatrix A) :
    zornJacobiator X Y Z =
      peirce_pp (zornJacobiator X Y Z) +
      peirce_mm (zornJacobiator X Y Z) +
      peirce_pm (zornJacobiator X Y Z) +
      peirce_mp (zornJacobiator X Y Z) := by
  have h₁ := peirce_decomposition (zornJacobiator X Y Z)
  simpa [peirce_pp, peirce_mm, peirce_pm, peirce_mp] using h₁
  <;> abel

/-- The commutator Jacobi identity on a fixed triple holds exactly when each
of its four Peirce components vanishes.  This is the vanishing criterion
associated to `jacobiator_peirce_grade_decomposition`; it makes no claim that
any component is nonzero for a general triple. -/
theorem jacobiator_eq_zero_iff_all_peirce_components_eq_zero
    (X Y Z : OpZornMatrix A) :
    zornJacobiator X Y Z = 0 ↔
      peirce_pp (zornJacobiator X Y Z) = 0 ∧
      peirce_mm (zornJacobiator X Y Z) = 0 ∧
      peirce_pm (zornJacobiator X Y Z) = 0 ∧
      peirce_mp (zornJacobiator X Y Z) = 0 := by
  constructor
  · intro h
    rw [h]
    simp [peirce_pp, peirce_mm, peirce_pm, peirce_mp]
  · rintro ⟨hpp, hmm, hpm, hmp⟩
    have h := jacobiator_peirce_grade_decomposition X Y Z
    rw [hpp, hmm, hpm, hmp] at h
    simpa using h

/-- Each Peirce grade of the Jacobiator is the same signed six-term
alternating sum of the corresponding associator grades. This is the
grade-resolved form of the universal Jacobiator--associator identity; it does
not assert that any individual grade is nonzero. -/
theorem jacobiator_peirce_components_eq_alternating_associator_components
    (X Y Z : OpZornMatrix A) :
    peirce_pp (zornJacobiator X Y Z) =
        peirce_pp (opAssociator X Y Z) + peirce_pp (opAssociator Y Z X) +
          peirce_pp (opAssociator Z X Y) - peirce_pp (opAssociator Y X Z) -
            peirce_pp (opAssociator Z Y X) - peirce_pp (opAssociator X Z Y) ∧
    peirce_mm (zornJacobiator X Y Z) =
        peirce_mm (opAssociator X Y Z) + peirce_mm (opAssociator Y Z X) +
          peirce_mm (opAssociator Z X Y) - peirce_mm (opAssociator Y X Z) -
            peirce_mm (opAssociator Z Y X) - peirce_mm (opAssociator X Z Y) ∧
    peirce_pm (zornJacobiator X Y Z) =
        peirce_pm (opAssociator X Y Z) + peirce_pm (opAssociator Y Z X) +
          peirce_pm (opAssociator Z X Y) - peirce_pm (opAssociator Y X Z) -
            peirce_pm (opAssociator Z Y X) - peirce_pm (opAssociator X Z Y) ∧
    peirce_mp (zornJacobiator X Y Z) =
        peirce_mp (opAssociator X Y Z) + peirce_mp (opAssociator Y Z X) +
          peirce_mp (opAssociator Z X Y) - peirce_mp (opAssociator Y X Z) -
            peirce_mp (opAssociator Z Y X) - peirce_mp (opAssociator X Z Y) := by
  have hj := zornJacobiator_eq_alternating_associator X Y Z
  constructor
  · rw [hj]
    simp only [peirce_pp, opZorn_mul_add, opZorn_add_mul,
      opZorn_mul_sub, opZorn_sub_mul]
  constructor
  · rw [hj]
    simp only [peirce_mm, opZorn_mul_add, opZorn_add_mul,
      opZorn_mul_sub, opZorn_sub_mul]
  constructor
  · rw [hj]
    simp only [peirce_pm, opZorn_mul_add, opZorn_add_mul,
      opZorn_mul_sub, opZorn_sub_mul]
  · rw [hj]
    simp only [peirce_mp, opZorn_mul_add, opZorn_add_mul,
      opZorn_mul_sub, opZorn_sub_mul]

/-- The universal associator component formula: the associator decomposes into
  Peirce grade blocks:
    Ass(X,Y,Z) = Ass₊₊ + Ass₋₋ + Ass₊₋ + Ass₋₊
  where Ass₊₊ = P₊·Ass·P₊ and Ass₋₋ = P₋·Ass·P₋ are diagonal corner readouts,
  and Ass₊₋ = P₊·Ass·P₋ and Ass₋₊ = P₋·Ass·P₊ are off-diagonal readouts.
  On the zornSinglet sector, all four blocks vanish (associativity holds there).
  For a general triple this decomposition alone says nothing about which blocks
  are nonzero, and does not assert that a block generates a grade. -/
theorem associator_peirce_grade_decomposition
    (X Y Z : OpZornMatrix A) :
    opAssociator X Y Z =
      peirce_pp (opAssociator X Y Z) +
      peirce_mm (opAssociator X Y Z) +
      peirce_pm (opAssociator X Y Z) +
      peirce_mp (opAssociator X Y Z) := by
  have h₁ := peirce_decomposition (opAssociator X Y Z)
  simpa [peirce_pp, peirce_mm, peirce_pm, peirce_mp] using h₁
  <;> abel

/-- The associator vanishes exactly when all four of its Peirce components
vanish. This is the componentwise criterion corresponding to
`associator_peirce_grade_decomposition`; it does not assume associativity of
the ambient Zorn product. -/
theorem associator_eq_zero_iff_all_peirce_components_eq_zero
    (X Y Z : OpZornMatrix A) :
    opAssociator X Y Z = 0 ↔
      peirce_pp (opAssociator X Y Z) = 0 ∧
      peirce_mm (opAssociator X Y Z) = 0 ∧
      peirce_pm (opAssociator X Y Z) = 0 ∧
      peirce_mp (opAssociator X Y Z) = 0 := by
  constructor
  · intro h
    rw [h]
    simp [peirce_pp, peirce_mm, peirce_pm, peirce_mp]
  · rintro ⟨hpp, hmm, hpm, hmp⟩
    have h := associator_peirce_grade_decomposition X Y Z
    rw [hpp, hmm, hpm, hmp] at h
    simpa using h

/-- An element is supported in the diagonal Peirce corners exactly when
both off-diagonal components vanish. The converse uses their disjoint
coordinate support. This is a component criterion, not a claim that every
nonzero element or defect has a nonzero off-diagonal component. -/
theorem peirce_diagonal_iff_offdiag_vanish (T : OpZornMatrix A) :
    T = peirce_pp T + peirce_mm T ↔ peirce_pm T = 0 ∧ peirce_mp T = 0 := by
  constructor
  · intro hdiag
    have hv := congrArg (fun S : OpZornMatrix A => S.v) hdiag
    have hw := congrArg (fun S : OpZornMatrix A => S.w) hdiag
    simp only [peirce_pp_eq, peirce_mm_eq, add_v, add_w] at hv hw
    have hv0 : T.v = 0 := by
      ext
      · simpa using congrArg OpVec3.x hv
      · simpa using congrArg OpVec3.y hv
      · simpa using congrArg OpVec3.z hv
    have hw0 : T.w = 0 := by
      ext
      · simpa using congrArg OpVec3.x hw
      · simpa using congrArg OpVec3.y hw
      · simpa using congrArg OpVec3.z hw
    constructor
    · rw [peirce_pm_eq, hv0]
      rfl
    · rw [peirce_mp_eq, hw0]
      rfl
  · rintro ⟨hpm, hmp⟩
    calc
      T = peirce_pp T + peirce_mm T + peirce_pm T + peirce_mp T :=
        peirce_decomposition T
      _ = peirce_pp T + peirce_mm T := by rw [hpm, hmp]; simp

/-- A Jacobiator is diagonal exactly when its two off-diagonal Peirce
components vanish. This makes no claim that every nonzero Jacobiator has an
off-diagonal component. -/
theorem jacobiator_diagonal_iff_offdiag_vanish (X Y Z : OpZornMatrix A) :
    zornJacobiator X Y Z =
        peirce_pp (zornJacobiator X Y Z) + peirce_mm (zornJacobiator X Y Z) ↔
      peirce_pm (zornJacobiator X Y Z) = 0 ∧
        peirce_mp (zornJacobiator X Y Z) = 0 :=
  peirce_diagonal_iff_offdiag_vanish (zornJacobiator X Y Z)

/-- The same diagonal-support criterion applies to the associator defect. -/
theorem associator_diagonal_iff_offdiag_vanish (X Y Z : OpZornMatrix A) :
    opAssociator X Y Z =
        peirce_pp (opAssociator X Y Z) + peirce_mm (opAssociator X Y Z) ↔
      peirce_pm (opAssociator X Y Z) = 0 ∧
        peirce_mp (opAssociator X Y Z) = 0 :=
  peirce_diagonal_iff_offdiag_vanish (opAssociator X Y Z)

/-- Pentagon coherence for the reassociation defect on the actual Zorn
operator carrier. This is a distributive identity, not associativity: the
five associators record the two paths through the reassociation pentagon. -/
theorem associator_pentagon_identity (W X Y Z : OpZornMatrix A) :
    W * opAssociator X Y Z -
        opAssociator (W * X) Y Z +
        opAssociator W (X * Y) Z -
        opAssociator W X (Y * Z) +
        opAssociator W X Y * Z = 0 := by
  simp only [opAssociator, sub_mul, mul_sub]
  abel

end InfoGeometry.NCG.AnomalyGradeGeneration

namespace InfoGeometry.NCG.AnomalyGradeGeneration.ReflectedAssociatorMatrixWitness

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.AnomalyGradeGeneration

/-- A genuinely noncommutative coefficient algebra for a concrete residual
witness. -/
abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

def coeffA : Coeff := !![0, 1; 0, 0]
def coeffB : Coeff := !![0, 1; 1, 0]

def vectorU : OpVec3 Coeff := ⟨coeffA, 0, 0⟩
def vectorW : OpVec3 Coeff := ⟨0, coeffB, 0⟩
def vectorV : OpVec3 Coeff := ⟨0, 1, 0⟩

/-- The coefficient matrices used in the witness do not commute. -/
theorem coeffA_mul_coeffB_ne_coeffB_mul_coeffA :
    coeffA * coeffB ≠ coeffB * coeffA := by
  norm_num [coeffA, coeffB, Matrix.mul_apply, Fin.sum_univ_two]

/-- The cross-product swap defect is genuinely nonzero for these matrix
coefficients, so its commutator formula is not merely a formal rewriting. -/
theorem naive_cross_braiding_defect_nonzero :
    OpVec3.naiveCross vectorU vectorW +
      OpVec3.naiveCross vectorW vectorU ≠ 0 := by
  intro h
  have hz := congrArg (fun u : OpVec3 Coeff => u.z) h
  apply coeffA_mul_coeffB_ne_coeffB_mul_coeffA
  have hz' : coeffA * coeffB - coeffB * coeffA = 0 := by
    simpa [OpVec3.naiveCross, vectorU, vectorW, sub_eq_add_neg] using hz
  exact sub_eq_zero.mp hz'

/-- The proposed three-term reflected cancellation is not universal for the
repository's actual Zorn product: its residual is nonzero on explicit
noncommuting matrix coefficients. -/
theorem reflected_associator_sum_ne_zero :
    opAssociator (fockRaise vectorU) (fockLower vectorW) (fockRaise vectorV) +
      opAssociator (fockRaise vectorU) (fockRaise vectorW) (fockLower vectorV) +
      opAssociator (fockLower vectorU) (fockRaise vectorW) (fockRaise vectorV) ≠ 0 := by
  rw [reflected_associator_sum_exact]
  intro h
  have hx := congrArg (fun X : OpZornMatrix Coeff => X.v.x) h
  have h00 := congrArg (fun M : Coeff => M 0 0) hx
  norm_num [fockRaise, OpVec3.leftScale, OpVec3.rightScale,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    vectorU, vectorW, vectorV, coeffA, coeffB,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.NCG.AnomalyGradeGeneration.ReflectedAssociatorMatrixWitness

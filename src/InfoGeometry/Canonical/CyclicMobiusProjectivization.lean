/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Circle
import InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge
import InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset

/-!
# Projectivization of the finite Peirce circle coordinates

This file constructs a map from the real projective line of coordinate pairs to
the projectivization of the concrete `2 × 2` Peirce state matrices. It proves
that the existing quadratic homogeneous state descends under nonzero scalar
rescaling and identifies the three standard representatives. It does not assert
a topological identification with `S¹`.
-/

open scoped LinearAlgebra.Projectivization Matrix ComplexConjugate

namespace InfoGeometry.Canonical.CyclicMobiusProjectivization

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The upper-sheet Peirce idempotent. -/
def peirceP : Mat2 := !![1, 0; 0, 0]

/-- The sheet-swap matrix. -/
def peirceSwap : Mat2 := !![0, 1; 1, 0]

/-- The two Peirce generators do not commute, so the matrix carrier here is
being used with its actual noncommutative multiplication. -/
theorem peirceP_mul_swap_ne_swap_mul_peirceP :
    peirceP * peirceSwap ≠ peirceSwap * peirceP := by
  intro h
  have h01 := congrArg (fun A : Mat2 => A 0 1) h
  norm_num [peirceP, peirceSwap, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The homogeneous state from the cyclic Möbius owner at the standard matrix pair. -/
def state (u v : ℝ) : Mat2 :=
  InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState
    peirceP peirceSwap u v

/-- Entrywise form of the homogeneous Peirce state matrix. -/
theorem state_matrix (u v : ℝ) : state u v = !![u ^ 2, u * v; u * v, v ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [state,
      InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
      peirceP, peirceSwap]

/-- Rescaling the homogeneous coordinates by `t` rescales the state by `t²`. -/
theorem state_smul (t u v : ℝ) : state (t * u) (t * v) = t ^ 2 • state u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [state,
      InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
      peirceP, peirceSwap] <;> ring

/-- A nonzero coordinate pair gives a nonzero homogeneous state matrix. -/
theorem state_ne_zero {u v : ℝ} (h : (u, v) ≠ (0, 0)) : state u v ≠ 0 := by
  intro hs
  have h00 := congrArg (fun M : Mat2 => M 0 0) hs
  have h11 := congrArg (fun M : Mat2 => M 1 1) hs
  have hu2 : u ^ 2 = 0 := by
    simpa [state,
      InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
      peirceP, peirceSwap] using h00
  have hv2 : v ^ 2 = 0 := by
    simpa [state,
      InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
      peirceP, peirceSwap] using h11
  apply h
  have hu' : u * u = 0 := by nlinarith [hu2]
  have hv' : v * v = 0 := by nlinarith [hv2]
  have hu : u = 0 := mul_self_eq_zero.mp hu'
  have hv : v = 0 := mul_self_eq_zero.mp hv'
  exact Prod.ext hu hv

/-- Every Peirce state lies on the determinant-zero conic in matrix space. -/
theorem state_det_zero (u v : ℝ) : Matrix.det (state u v) = 0 := by
  rw [Matrix.det_fin_two]
  simp [state,
    InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
    peirceP, peirceSwap]
  ring

/-- Division-free homogeneous idempotency law for the Peirce state: before
normalizing by `u² + v²`, its square is that scalar times itself. This is the
polynomial statement that remains meaningful even when the normalizing scalar
is not invertible. -/
theorem state_mul_state (u v : ℝ) :
    state u v * state u v = (u ^ 2 + v ^ 2) • state u v := by
  rw [state_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Swap the two homogeneous coordinates; projectively this is the inversion
chart change `[u:v] ↦ [v:u]`. -/
def coordinateSwap : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v i := v (Equiv.swap 0 1 i)
  map_add' v w := by
    ext i
    simp
  map_smul' c v := by
    ext i
    simp

@[simp]
theorem coordinateSwap_zero (v : Fin 2 → ℝ) : coordinateSwap v 0 = v 1 := by
  simp [coordinateSwap]

@[simp]
theorem coordinateSwap_one (v : Fin 2 → ℝ) : coordinateSwap v 1 = v 0 := by
  simp [coordinateSwap]

theorem coordinateSwap_injective : Function.Injective coordinateSwap := by
  intro v w h
  funext i
  have hi := congrFun h (Equiv.swap 0 1 i)
  simpa [coordinateSwap] using hi

/-- Conjugation by the sheet swap implements the reciprocal chart swap on
Peirce state matrices. -/
def conjugatePeirceSwap : Mat2 →ₗ[ℝ] Mat2 where
  toFun A := peirceSwap * A * peirceSwap
  map_add' A B := by
    simp [mul_add, add_mul, Matrix.mul_assoc]
  map_smul' c A := by
    simp [Matrix.mul_assoc]

@[simp]
theorem peirceSwap_sq : peirceSwap * peirceSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceSwap]

theorem conjugatePeirceSwap_injective : Function.Injective conjugatePeirceSwap := by
  intro A B h
  have hleft := congrArg (fun M : Mat2 => peirceSwap * M) h
  have hleft' : A * peirceSwap = B * peirceSwap := by
    calc
      A * peirceSwap = (peirceSwap * peirceSwap) * (A * peirceSwap) := by
        rw [peirceSwap_sq, one_mul]
      _ = peirceSwap * (peirceSwap * A * peirceSwap) := by noncomm_ring
      _ = peirceSwap * (peirceSwap * B * peirceSwap) := hleft
      _ = (peirceSwap * peirceSwap) * (B * peirceSwap) := by noncomm_ring
      _ = B * peirceSwap := by rw [peirceSwap_sq, one_mul]
  have hright := congrArg (fun M : Mat2 => M * peirceSwap) hleft'
  calc
    A = (A * peirceSwap) * peirceSwap := by rw [mul_assoc, peirceSwap_sq, mul_one]
    _ = (B * peirceSwap) * peirceSwap := hright
    _ = B := by rw [mul_assoc, peirceSwap_sq, mul_one]

theorem conjugatePeirceSwap_state (u v : ℝ) :
    conjugatePeirceSwap (state u v) = state v u := by
  rw [state_matrix, state_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugatePeirceSwap, peirceSwap]
  <;> ring

/-- The coordinate transposition induces the reciprocal-chart involution on
the real projective line. -/
noncomputable def coordinateSwapProjective : ℙ ℝ (Fin 2 → ℝ) → ℙ ℝ (Fin 2 → ℝ) :=
  Projectivization.map coordinateSwap coordinateSwap_injective

/-- Coordinate transposition is an involution on the projective coordinate line. -/
theorem coordinateSwapProjective_involutive (q : ℙ ℝ (Fin 2 → ℝ)) :
    coordinateSwapProjective (coordinateSwapProjective q) = q := by
  induction q using Projectivization.ind with
  | h v hv =>
    simp only [coordinateSwapProjective, Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨1, ?_⟩
    ext i
    fin_cases i <;> simp [coordinateSwap]

/-- Conjugation by the sheet swap induces an involution on projective matrix
rays. -/
noncomputable def conjugatePeirceSwapProjective : ℙ ℝ Mat2 → ℙ ℝ Mat2 :=
  Projectivization.map conjugatePeirceSwap conjugatePeirceSwap_injective

/-- Sheet-swap conjugation is an involution on projective matrix rays. -/
theorem conjugatePeirceSwapProjective_involutive (q : ℙ ℝ Mat2) :
    conjugatePeirceSwapProjective (conjugatePeirceSwapProjective q) = q := by
  induction q using Projectivization.ind with
  | h A hA =>
    simp only [conjugatePeirceSwapProjective, Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨1, ?_⟩
    change 1 • A = peirceSwap * (peirceSwap * A * peirceSwap) * peirceSwap
    rw [one_smul]
    calc
      A = (peirceSwap * peirceSwap) * A * (peirceSwap * peirceSwap) := by
        rw [peirceSwap_sq]
        simp
      _ = peirceSwap * (peirceSwap * A * peirceSwap) * peirceSwap := by noncomm_ring

private noncomputable def stateProjectiveRep (x : {v : Fin 2 → ℝ // v ≠ 0}) :
    ℙ ℝ Mat2 :=
  Projectivization.mk ℝ (state (x.1 0) (x.1 1)) (state_ne_zero (by
    intro hx
    apply x.2
    funext i
    fin_cases i
    · exact congrArg Prod.fst hx
    · exact congrArg Prod.snd hx))

private theorem stateProjectiveRep_rescale
    (a b : {v : Fin 2 → ℝ // v ≠ 0}) (t : ℝ)
    (h : a.1 = t • (b.1 : Fin 2 → ℝ)) :
    stateProjectiveRep a = stateProjectiveRep b := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨t ^ 2, ?_⟩
  change t ^ 2 • state (b.1 0) (b.1 1) = state (a.1 0) (a.1 1)
  rw [h]
  simpa [Pi.smul_apply] using (state_smul t (b.1 0) (b.1 1)).symm

/-- The quadratic Peirce state induces a map on the real projective line. -/
noncomputable def peirceProjectivization : ℙ ℝ (Fin 2 → ℝ) → ℙ ℝ Mat2 :=
  Projectivization.lift stateProjectiveRep stateProjectiveRep_rescale

@[simp]
theorem peirceProjectivization_mk (u v : ℝ) (h : (u, v) ≠ (0, 0)) :
    peirceProjectivization (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v)
      (by
        intro hv
        apply h
        have hu := congrFun hv 0
        have hv' := congrFun hv 1
        simp at hu hv'
        exact Prod.ext hu hv')) =
      Projectivization.mk ℝ (state u v) (state_ne_zero h) := by
  simp [peirceProjectivization, stateProjectiveRep]

/-- The projective Peirce parametrization intertwines coordinate inversion
with conjugation by the sheet-swap matrix. -/
theorem peirceProjectivization_coordinateSwap (q : ℙ ℝ (Fin 2 → ℝ)) :
    peirceProjectivization (coordinateSwapProjective q) =
      conjugatePeirceSwapProjective (peirceProjectivization q) := by
  induction q using Projectivization.ind with
  | h v hv =>
    simp only [coordinateSwapProjective, conjugatePeirceSwapProjective,
      Projectivization.map_mk, peirceProjectivization, Projectivization.lift_mk,
      stateProjectiveRep, coordinateSwap_zero, coordinateSwap_one,
      conjugatePeirceSwap_state]

/-- The normalized commutator-square variance of a coordinate representative.
The denominator is nonzero because the representative is a nonzero real pair. -/
private noncomputable def peirceVarianceRep (x : {v : Fin 2 → ℝ // v ≠ 0}) : ℝ :=
  4 * (x.1 0) ^ 2 * (x.1 1) ^ 2 /
    ((x.1 0) ^ 2 + (x.1 1) ^ 2) ^ 2

/-- The variance expression is unchanged by any projective rescaling. -/
private theorem peirceVarianceRep_rescale
    (a b : {v : Fin 2 → ℝ // v ≠ 0}) (t : ℝ)
    (h : a.1 = t • (b.1 : Fin 2 → ℝ)) :
    peirceVarianceRep a = peirceVarianceRep b := by
  have ht : t ≠ 0 := by
    intro ht0
    apply a.2
    rw [h, ht0]
    simp
  have hden : (b.1 0) ^ 2 + (b.1 1) ^ 2 ≠ 0 := by
    intro hzero
    have h0 : b.1 0 = 0 := by nlinarith [sq_nonneg (b.1 0), sq_nonneg (b.1 1)]
    have h1 : b.1 1 = 0 := by nlinarith [sq_nonneg (b.1 0), sq_nonneg (b.1 1)]
    apply b.2
    funext i
    fin_cases i <;> simp [h0, h1]
  have h0 : a.1 0 = t * b.1 0 := by
    have := congrFun h 0
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have h1 : a.1 1 = t * b.1 1 := by
    have := congrFun h 1
    simpa [Pi.smul_apply, smul_eq_mul] using this
  dsimp [peirceVarianceRep]
  rw [h0, h1]
  field_simp [ht, hden]

/-- The Fubini–Study variance descends to a well-defined function on the real
projective coordinate line. Its definition is algebraic and does not assert a
topological circle structure. -/
noncomputable def peirceProjectiveVariance : ℙ ℝ (Fin 2 → ℝ) → ℝ :=
  Projectivization.lift peirceVarianceRep peirceVarianceRep_rescale

/-- In an affine representative `(u,v)`, the descended variance has the usual
reciprocal-symmetric rational expression. -/
@[simp]
theorem peirceProjectiveVariance_mk (u v : ℝ) (h : (u, v) ≠ (0, 0)) :
    peirceProjectiveVariance
      (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v)
        (by
          intro hz
          apply h
          have hu := congrFun hz 0
          have hv := congrFun hz 1
          simp at hu hv
          exact Prod.ext hu hv)) =
      4 * u ^ 2 * v ^ 2 / (u ^ 2 + v ^ 2) ^ 2 := by
  simp [peirceProjectiveVariance, peirceVarianceRep]

/-- Reciprocal coordinate inversion preserves the projective variance. -/
theorem peirceProjectiveVariance_coordinateSwap (q : ℙ ℝ (Fin 2 → ℝ)) :
    peirceProjectiveVariance (coordinateSwapProjective q) =
      peirceProjectiveVariance q := by
  induction q using Projectivization.ind with
  | h v hv =>
    simp only [coordinateSwapProjective, Projectivization.map_mk,
      peirceProjectiveVariance, Projectivization.lift_mk, peirceVarianceRep,
      coordinateSwap_zero, coordinateSwap_one]
    ring

/-- The totalized rational Cayley formula on real coordinate pairs; its
projective interpretation is used only for nonzero homogeneous pairs. -/
noncomputable def cayleyComplex (u v : ℝ) : ℂ :=
  ⟨(u ^ 2 - v ^ 2) / (u ^ 2 + v ^ 2),
    (2 * u * v) / (u ^ 2 + v ^ 2)⟩

/-- Swapping the real projective coordinates changes the Cayley value by
`z ↦ -star z`, the algebraic antipodal inverse on the unit circle. -/
theorem cayleyComplex_coordinateSwap (u v : ℝ) :
    cayleyComplex v u = -(star (cayleyComplex u v)) := by
  apply Complex.ext <;> simp [cayleyComplex] <;> ring

/-- A nonzero real homogeneous pair determines a point of Mathlib's unit
circle via the rational Cayley coordinate. -/
private noncomputable def cayleyCircleRep
    (x : {v : Fin 2 → ℝ // v ≠ 0}) : Circle := by
  let u := x.1 0
  let v := x.1 1
  have hden : u ^ 2 + v ^ 2 ≠ 0 := by
    intro hz
    have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    apply x.2
    funext i
    fin_cases i
    · exact hu
    · exact hv
  have hnum : (u ^ 2 - v ^ 2) ^ 2 + (2 * u * v) ^ 2 =
      (u ^ 2 + v ^ 2) ^ 2 := by ring
  have hnormSq : Complex.normSq (cayleyComplex u v) = 1 := by
    rw [Complex.normSq_apply]
    dsimp [cayleyComplex]
    field_simp [hden]
    nlinarith [hnum]
  refine ⟨cayleyComplex u v, ?_⟩
  apply (mem_sphere_zero_iff_norm).2
  have hnorm := hnormSq
  rw [Complex.normSq_eq_norm_sq] at hnorm
  have hnonneg : 0 ≤ ‖cayleyComplex u v‖ := norm_nonneg _
  nlinarith

/-- The normalized Cayley coordinate is independent of the chosen nonzero
representative of a real projective point. -/
private theorem cayleyCircleRep_rescale
    (a b : {v : Fin 2 → ℝ // v ≠ 0}) (t : ℝ)
    (h : a.1 = t • (b.1 : Fin 2 → ℝ)) :
    cayleyCircleRep a = cayleyCircleRep b := by
  have ht : t ≠ 0 := by
    intro ht0
    apply a.2
    rw [h, ht0]
    simp
  have hden : (b.1 0) ^ 2 + (b.1 1) ^ 2 ≠ 0 := by
    intro hzero
    have h0 : b.1 0 = 0 := by
      nlinarith [sq_nonneg (b.1 0), sq_nonneg (b.1 1)]
    have h1 : b.1 1 = 0 := by
      nlinarith [sq_nonneg (b.1 0), sq_nonneg (b.1 1)]
    apply b.2
    funext i
    fin_cases i <;> assumption
  have h0 : a.1 0 = t * b.1 0 := by
    have h0 := congrFun h 0
    simpa [Pi.smul_apply, smul_eq_mul] using h0
  have h1 : a.1 1 = t * b.1 1 := by
    have h1 := congrFun h 1
    simpa [Pi.smul_apply, smul_eq_mul] using h1
  apply Circle.ext
  apply Complex.ext
  · dsimp [cayleyCircleRep, cayleyComplex]
    rw [h0, h1]
    field_simp [ht, hden]
  · dsimp [cayleyCircleRep, cayleyComplex]
    rw [h0, h1]
    field_simp [ht, hden]

/-- The real projective coordinate line admits a set map into Mathlib's
topological unit circle. This is an algebraically well-defined Cayley map;
continuity and winding are separate claims. -/
noncomputable def cayleyProjectiveCircle : ℙ ℝ (Fin 2 → ℝ) → Circle :=
  Projectivization.lift cayleyCircleRep cayleyCircleRep_rescale

/-- The Cayley map's complex value on a homogeneous coordinate representative. -/
@[simp]
theorem cayleyProjectiveCircle_mk (u v : ℝ) (h : (u, v) ≠ (0, 0)) :
    (cayleyProjectiveCircle
      (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) (by
        intro hz
        apply h
        have h0 := congrFun hz 0
        have h1 := congrFun hz 1
        simp at h0 h1
        exact Prod.ext h0 h1)) : ℂ) = cayleyComplex u v := by
  simp [cayleyProjectiveCircle, Projectivization.lift_mk, cayleyCircleRep,
    cayleyComplex]

/-- The affine representative of the homogeneous coordinate pair `(u,v)`. -/
noncomputable def coordinateRay (u v : ℝ) (h : (u, v) ≠ (0, 0)) :
    ℙ ℝ (Fin 2 → ℝ) :=
  Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) (by
    intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    simp at h0 h1
    exact h (Prod.ext h0 h1))

/-- The projective variance is exactly the commutator-square readout of the
normalized concrete Peirce state matrix. This connects the quotient-level
scalar invariant to the actual noncommutative `Mat₂(ℝ)` carrier; the
normalization is defined only because a nonzero real coordinate pair has
`u² + v² ≠ 0`. -/
theorem peirceProjectiveVariance_eq_normalized_matrix_commutator
    (u v : ℝ) (h : (u, v) ≠ (0, 0)) :
    peirceProjectiveVariance (coordinateRay u v h) • (1 : Mat2) =
      -(4 : ℝ) •
        ((InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.Pminus *
          InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.normalizedPeircePoint u v -
          InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.normalizedPeircePoint u v *
          InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.Pminus) ^ 2) := by
  have hden : u ^ 2 + v ^ 2 ≠ 0 := by
    intro hz
    apply h
    have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    exact Prod.ext hu hv
  have hprofile :
      4 * u ^ 2 * v ^ 2 / (u ^ 2 + v ^ 2) ^ 2 =
        4 * ((u * v) / (u ^ 2 + v ^ 2)) ^ 2 := by
    field_simp [hden]
  change peirceProjectiveVariance
      (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) _) •
      (1 : Mat2) = _
  rw [InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.normalizedPeircePoint_variance]
  rw [peirceProjectiveVariance_mk u v h]
  rw [hprofile]

@[simp]
theorem cayleyProjectiveCircle_coordinateRay (u v : ℝ) (h : (u, v) ≠ (0, 0)) :
    (cayleyProjectiveCircle (coordinateRay u v h) : ℂ) = cayleyComplex u v := by
  change (cayleyProjectiveCircle
    (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) _) : ℂ) = _
  rw [cayleyProjectiveCircle_mk u v h]

/-- The algebraic inverse chart from the unit circle to the real projective
coordinate line. Away from `-1` it uses `[1 + re(z) : im(z)]`; at `-1` it
uses the point at infinity `[0 : 1]`. -/
noncomputable def cayleyProjectiveCircleInv (z : Circle) : ℙ ℝ (Fin 2 → ℝ) :=
  if h : (z : ℂ).re = -1 then coordinateRay 0 1 (by norm_num)
  else coordinateRay (1 + (z : ℂ).re) (z : ℂ).im (by
    intro hp
    apply h
    have h0 := congrArg Prod.fst hp
    linarith)

/-- The projective Cayley map sends the two coordinate-axis rays to the
antipodal real points and the diagonal ray to the positive imaginary point. -/
theorem cayleyProjectiveCircle_three_anchors :
    (cayleyProjectiveCircle (coordinateRay 1 0 (by norm_num)) : ℂ) = 1 ∧
    (cayleyProjectiveCircle (coordinateRay 1 1 (by norm_num)) : ℂ) = Complex.I ∧
    (cayleyProjectiveCircle (coordinateRay 0 1 (by norm_num)) : ℂ) = -1 := by
  constructor
  · change (cayleyProjectiveCircle
      (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 1 else 0) _) : ℂ) = 1
    rw [cayleyProjectiveCircle_mk]
    · apply Complex.ext <;> norm_num [cayleyComplex]
    · norm_num

  constructor
  · change (cayleyProjectiveCircle
      (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 1 else 1) _) : ℂ) = Complex.I
    rw [cayleyProjectiveCircle_mk]
    · apply Complex.ext <;> norm_num [cayleyComplex]
    · norm_num
  · change (cayleyProjectiveCircle
      (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 0 else 1) _) : ℂ) = -1
    rw [cayleyProjectiveCircle_mk]
    · apply Complex.ext <;> norm_num [cayleyComplex]
    · norm_num

/-- The reciprocal-coordinate involution on the real projective line acts on
the Cayley circle by the antipodal map composed with inversion. -/
theorem cayleyProjectiveCircle_coordinateSwap (q : ℙ ℝ (Fin 2 → ℝ)) :
    cayleyProjectiveCircle (coordinateSwapProjective q) =
      -((cayleyProjectiveCircle q)⁻¹) := by
  induction q using Projectivization.ind with
  | h v hv =>
    have hcoord : (v 0, v 1) ≠ (0, 0) := by
      intro h
      apply hv
      funext i
      fin_cases i
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    have hcoordSwap : (v 1, v 0) ≠ (0, 0) := by
      intro h
      apply hv
      funext i
      fin_cases i
      · exact congrArg Prod.snd h
      · exact congrArg Prod.fst h
    have hvRay : Projectivization.mk ℝ v hv = coordinateRay (v 0) (v 1) hcoord := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
      refine ⟨1, ?_⟩
      ext i
      fin_cases i <;> simp
    have hswapRay :
        Projectivization.mk ℝ (coordinateSwap v) (coordinateSwap_injective.ne hv) =
          coordinateRay (v 1) (v 0) hcoordSwap := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
      refine ⟨1, ?_⟩
      ext i
      fin_cases i <;> simp
    apply Circle.ext
    simp only [coordinateSwapProjective, Projectivization.map_mk]
    rw [hswapRay, hvRay]
    change cayleyComplex (v 1) (v 0) =
      -(((cayleyProjectiveCircle (coordinateRay (v 0) (v 1) hcoord))⁻¹ : Circle) : ℂ)
    rw [Circle.coe_inv_eq_conj]
    rw [cayleyProjectiveCircle_coordinateRay]
    simpa only [Complex.star_def] using cayleyComplex_coordinateSwap (v 0) (v 1)

/-- The inverse chart followed by the Cayley map is the identity on Mathlib's
unit circle. This is a set-level equivalence statement; topology is separate. -/
theorem cayleyProjectiveCircle_leftInverse (z : Circle) :
    cayleyProjectiveCircle (cayleyProjectiveCircleInv z) = z := by
  by_cases hRe : (z : ℂ).re = -1
  · have hIm : (z : ℂ).im = 0 := by
      have hnorm : Complex.normSq (z : ℂ) = 1 := Circle.normSq_coe z
      rw [Complex.normSq_apply] at hnorm
      nlinarith
    have hz : (z : ℂ) = -1 := by
      apply Complex.ext <;> simp [hRe, hIm]
    rw [cayleyProjectiveCircleInv, dite_eq_left hRe]
    apply Circle.ext
    rw [cayleyProjectiveCircle_three_anchors.2.2]
    exact hz.symm
  · have hnorm : ((z : ℂ).re) ^ 2 + ((z : ℂ).im) ^ 2 = 1 := by
      have h := Circle.normSq_coe z
      rw [Complex.normSq_apply] at h
      simpa [pow_two] using h
    have hden : 1 + (z : ℂ).re ≠ 0 := by
      intro hzero
      apply hRe
      linarith
    have hpair : (1 + (z : ℂ).re, (z : ℂ).im) ≠ (0, 0) := by
      intro hp
      apply hRe
      have h0 := congrArg Prod.fst hp
      linarith
    have hdenEq :
        (1 + (z : ℂ).re) ^ 2 + (z : ℂ).im ^ 2 = 2 * (1 + (z : ℂ).re) := by
      nlinarith [hnorm]
    rw [cayleyProjectiveCircleInv, dite_eq_right hRe]
    apply Circle.ext
    change (cayleyProjectiveCircle
      (Projectivization.mk ℝ
        (fun i : Fin 2 => if i = 0 then 1 + (z : ℂ).re else (z : ℂ).im) _) : ℂ) =
      (z : ℂ)
    rw [cayleyProjectiveCircle_mk _ _ hpair]
    apply Complex.ext
    · dsimp [cayleyComplex]
      rw [hdenEq]
      field_simp [hden]
      nlinarith [hnorm]
    · dsimp [cayleyComplex]
      rw [hdenEq]
      field_simp [hden]

/-- The projective Cayley map is surjective onto Mathlib's unit circle; the
inverse witness is the explicit algebraic chart above. -/
theorem cayleyProjectiveCircle_surjective :
    Function.Surjective cayleyProjectiveCircle := by
  intro z
  exact ⟨cayleyProjectiveCircleInv z, cayleyProjectiveCircle_leftInverse z⟩

/-- The inverse chart also recovers each projective coordinate ray, so the
algebraic Cayley map is injective on projective points. -/
theorem cayleyProjectiveCircleInv_rightInverse (u v : ℝ)
    (h : (u, v) ≠ (0, 0)) :
    cayleyProjectiveCircleInv (cayleyProjectiveCircle (coordinateRay u v h)) =
      coordinateRay u v h := by
  have hden : u ^ 2 + v ^ 2 ≠ 0 := by
    intro hz
    apply h
    have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    exact Prod.ext hu hv
  have hval := cayleyProjectiveCircle_coordinateRay u v h
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro hv
      apply h
      exact Prod.ext hu hv
    have hRe :
        (cayleyProjectiveCircle (coordinateRay u v h) : ℂ).re = -1 := by
      rw [hval]
      simp [cayleyComplex, hu]
      field_simp [hden]
    rw [cayleyProjectiveCircleInv, dite_eq_left hRe]
    symm
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨v, ?_⟩
    ext i
    fin_cases i <;> simp [hu]
  · let c : ℝ := 2 * u / (u ^ 2 + v ^ 2)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact div_ne_zero (mul_ne_zero (by norm_num) hu) hden
    have hReCoord :
        1 + (cayleyProjectiveCircle (coordinateRay u v h) : ℂ).re = c * u := by
      rw [hval]
      dsimp [c, cayleyComplex]
      field_simp [hden]
      ring
    have hImCoord :
        (cayleyProjectiveCircle (coordinateRay u v h) : ℂ).im = c * v := by
      rw [hval]
      dsimp [c, cayleyComplex]
      field_simp [hden]
    have hnotPole :
        (cayleyProjectiveCircle (coordinateRay u v h) : ℂ).re ≠ -1 := by
      intro hpole
      rw [hpole] at hReCoord
      have hcu : c * u ≠ 0 := mul_ne_zero hc hu
      have : c * u = 0 := by simpa using hReCoord.symm
      exact hcu this
    have hpair :
        (1 + (cayleyProjectiveCircle (coordinateRay u v h) : ℂ).re,
          (cayleyProjectiveCircle (coordinateRay u v h) : ℂ).im) ≠ (0, 0) := by
      intro hp
      apply hnotPole
      have h0 := congrArg Prod.fst hp
      linarith
    rw [cayleyProjectiveCircleInv, dite_eq_right hnotPole]
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨c, ?_⟩
    ext i
    fin_cases i
    · simpa [coordinateRay] using hReCoord.symm
    · simpa [coordinateRay] using hImCoord.symm

/-- The inverse chart recovers every projective point, by reducing to a
nonzero homogeneous coordinate representative. -/
theorem cayleyProjectiveCircleInv_rightInverse_projective
    (q : ℙ ℝ (Fin 2 → ℝ)) :
    cayleyProjectiveCircleInv (cayleyProjectiveCircle q) = q := by
  induction q using Projectivization.ind with
  | h x hx =>
    have hpair : (x 0, x 1) ≠ (0, 0) := by
      intro h
      apply hx
      funext i
      fin_cases i
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    have hform :
        Projectivization.mk ℝ x hx = coordinateRay (x 0) (x 1) hpair := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
      refine ⟨1, ?_⟩
      ext i
      fin_cases i <;> simp
    rw [hform]
    exact cayleyProjectiveCircleInv_rightInverse (x 0) (x 1) hpair

/-- The projective Cayley map is injective, witnessed by its explicit inverse
chart. -/
theorem cayleyProjectiveCircle_injective :
    Function.Injective cayleyProjectiveCircle := by
  intro p q hpq
  have hinv := congrArg cayleyProjectiveCircleInv hpq
  rw [cayleyProjectiveCircleInv_rightInverse_projective p,
    cayleyProjectiveCircleInv_rightInverse_projective q] at hinv
  exact hinv

/-- The real projective coordinate line and Mathlib's unit circle are
equivalent as types under the explicit Cayley chart. This is not a claim of
homeomorphism or any winding classification. -/
noncomputable def cayleyProjectiveCircleEquiv :
    ℙ ℝ (Fin 2 → ℝ) ≃ Circle where
  toFun := cayleyProjectiveCircle
  invFun := cayleyProjectiveCircleInv
  left_inv := cayleyProjectiveCircleInv_rightInverse_projective
  right_inv := cayleyProjectiveCircle_leftInverse

/-- On the three standard projective representatives, the descended Peirce
variance has values `0, 1, 0`. The endpoints are distinct projective points;
the equality concerns this scalar invariant, not an identification of the
points or a topological limit at infinity. -/
theorem peirceProjectiveVariance_three_anchors :
    peirceProjectiveVariance (coordinateRay 1 0 (by norm_num)) = 0 ∧
    peirceProjectiveVariance (coordinateRay 1 1 (by norm_num)) = 1 ∧
    peirceProjectiveVariance (coordinateRay 0 1 (by norm_num)) = 0 := by
  constructor
  · change peirceProjectiveVariance
      (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 1 else 0) _) = 0
    rw [peirceProjectiveVariance_mk 1 0 (by norm_num)]
    norm_num
  · constructor
    · change peirceProjectiveVariance
        (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 1 else 1) _) = 1
      rw [peirceProjectiveVariance_mk 1 1 (by norm_num)]
      norm_num
    · change peirceProjectiveVariance
        (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 0 else 1) _) = 0
      rw [peirceProjectiveVariance_mk 0 1 (by norm_num)]
      norm_num

/-- On a nonzero real homogeneous representative, the normalized variance
vanishes exactly at the two coordinate-axis rays. -/
theorem peirceProjectiveVariance_eq_zero_iff (u v : ℝ)
    (h : (u, v) ≠ (0, 0)) :
    peirceProjectiveVariance (coordinateRay u v h) = 0 ↔ u = 0 ∨ v = 0 := by
  change peirceProjectiveVariance
    (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) _) = 0 ↔ _
  rw [peirceProjectiveVariance_mk u v h]
  have hden : u ^ 2 + v ^ 2 ≠ 0 := by
    intro hz
    apply h
    have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    exact Prod.ext hu hv
  constructor
  · intro hvar
    have hnum : 4 * u ^ 2 * v ^ 2 = 0 := by
      have hmul := hvar
      field_simp [pow_ne_zero 2 hden] at hmul
      nlinarith [hmul]
    have huv : u ^ 2 * v ^ 2 = 0 := by nlinarith [hnum]
    rcases mul_eq_zero.mp huv with hu | hv
    · left
      nlinarith [sq_nonneg u]
    · right
      nlinarith [sq_nonneg v]
  · rintro (rfl | rfl) <;> simp

/-- Exact deficit from the maximum normalized Peirce variance. The identity
exhibits the gap as a square and is the algebraic input to the maximum
characterization below. -/
theorem peirceProjectiveVariance_gap (u v : ℝ)
    (h : (u, v) ≠ (0, 0)) :
    1 - peirceProjectiveVariance (coordinateRay u v h) =
      (u ^ 2 - v ^ 2) ^ 2 / (u ^ 2 + v ^ 2) ^ 2 := by
  change 1 - peirceProjectiveVariance
    (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) _) = _
  rw [peirceProjectiveVariance_mk u v h]
  have hden : u ^ 2 + v ^ 2 ≠ 0 := by
    intro hz
    apply h
    have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    exact Prod.ext hu hv
  field_simp [pow_ne_zero 2 hden]
  ring

/-- The normalized projective variance is bounded above by `1` on every
nonzero real homogeneous representative. -/
theorem peirceProjectiveVariance_le_one (u v : ℝ)
    (h : (u, v) ≠ (0, 0)) :
    peirceProjectiveVariance (coordinateRay u v h) ≤ 1 := by
  have hgap := peirceProjectiveVariance_gap u v h
  have hnonneg : 0 ≤ (u ^ 2 - v ^ 2) ^ 2 / (u ^ 2 + v ^ 2) ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-- The normalized projective variance attains its maximum precisely on the
real rays with equal coordinate magnitudes. Thus the positive chart has
midpoint `z = 1`, while the distinct ray `z = -1` has the same maximal value. -/
theorem peirceProjectiveVariance_eq_one_iff (u v : ℝ)
    (h : (u, v) ≠ (0, 0)) :
    peirceProjectiveVariance (coordinateRay u v h) = 1 ↔ u ^ 2 = v ^ 2 := by
  change peirceProjectiveVariance
    (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) _) = 1 ↔ _
  have hgap := peirceProjectiveVariance_gap u v h
  change 1 - peirceProjectiveVariance
    (Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then u else v) _) = _ at hgap
  constructor
  · intro hvar
    have hzero : (u ^ 2 - v ^ 2) ^ 2 / (u ^ 2 + v ^ 2) ^ 2 = 0 := by
      rw [hvar] at hgap
      simpa using hgap.symm
    have hmul := hzero
    have hden : u ^ 2 + v ^ 2 ≠ 0 := by
      intro hz
      apply h
      have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
      have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
      exact Prod.ext hu hv
    field_simp [pow_ne_zero 2 hden] at hmul
    nlinarith [hmul]
  · intro hcoords
    rw [hcoords] at hgap
    simp at hgap
    linarith

/-- The quadratic Peirce projectivization separates real projective coordinate rays.

This is the injectivity half of the Veronese embedding statement. Its concrete
representatives satisfy the determinant-zero conic equation by `state_det_zero`. -/
theorem peirceProjectivization_injective : Function.Injective peirceProjectivization := by
  intro p q hpq
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw =>
      have hvCoord : (v 0, v 1) ≠ (0, 0) := by
        intro h
        apply hv
        funext i
        fin_cases i
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h
      have hwCoord : (w 0, w 1) ≠ (0, 0) := by
        intro h
        apply hw
        funext i
        fin_cases i
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h
      have hmat :
          Projectivization.mk ℝ (state (v 0) (v 1)) (state_ne_zero hvCoord) =
            Projectivization.mk ℝ (state (w 0) (w 1)) (state_ne_zero hwCoord) := by
        simpa [peirceProjectivization, stateProjectiveRep] using hpq
      obtain ⟨c, hc⟩ :=
        (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mp hmat
      have h00 := congrArg (fun M : Mat2 => M 0 0) hc
      have h01 := congrArg (fun M : Mat2 => M 0 1) hc
      have h11 := congrArg (fun M : Mat2 => M 1 1) hc
      simp [state,
        InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
        peirceP, peirceSwap] at h00 h01 h11
      have hc_ne : c ≠ 0 := by
        intro hc0
        have hstate : state (v 0) (v 1) = 0 := by
          calc
            state (v 0) (v 1) = c • state (w 0) (w 1) := hc.symm
            _ = 0 := by simp [hc0]
        exact (state_ne_zero hvCoord) hstate
      by_cases ha : w 0 = 0
      · have hb : w 1 ≠ 0 := by
          intro hb0
          apply hwCoord
          exact Prod.ext ha hb0
        have hu : v 0 = 0 := by
          have : (v 0) ^ 2 = 0 := by simpa [ha] using h00.symm
          nlinarith [this]
        have hvne : v 1 ≠ 0 := by
          intro hv0
          apply hc_ne
          have hcb : c * (w 1) ^ 2 = 0 := by simpa [hv0] using h11
          exact (mul_eq_zero.mp hcb).resolve_right (pow_ne_zero 2 hb)
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
        refine ⟨v 1 / w 1, ?_⟩
        funext i
        fin_cases i
        · simp [Pi.smul_apply, smul_eq_mul, ha, hu]
        · simp [Pi.smul_apply, smul_eq_mul]
          field_simp [hb]
      · have hu : v 0 ≠ 0 := by
          intro hu0
          have hca : c * (w 0) ^ 2 = 0 := by simpa [hu0] using h00
          have : (w 0) ^ 2 ≠ 0 := pow_ne_zero 2 ha
          exact hc_ne ((mul_eq_zero.mp hca).resolve_right this)
        have hcross : v 0 * w 1 = v 1 * w 0 := by
          have heq : v 0 * (v 1 * w 0) = v 0 * (v 0 * w 1) := by
            calc
              v 0 * (v 1 * w 0) = (c * (w 0 * w 1)) * w 0 := by
                rw [h01]
                ring
              _ = (c * w 0 ^ 2) * w 1 := by ring
              _ = (v 0 ^ 2) * w 1 := by rw [h00]
              _ = v 0 * (v 0 * w 1) := by ring
          exact (mul_left_cancel₀ hu heq).symm
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
        refine ⟨v 0 / w 0, ?_⟩
        funext i
        fin_cases i
        · simp [Pi.smul_apply, smul_eq_mul]
          field_simp [ha]
        · simp [Pi.smul_apply, smul_eq_mul]
          field_simp [ha]
          nlinarith [hcross]

/-- A projective matrix ray lies on the Peirce conic when it has a nonzero
symmetric representative with determinant zero. -/
def IsPeirceConicPoint (p : ℙ ℝ Mat2) : Prop :=
  ∃ A : Mat2, ∃ hA : A ≠ 0,
    p = Projectivization.mk ℝ A hA ∧ A 0 1 = A 1 0 ∧ Matrix.det A = 0

/-- The Peirce projectivization parametrizes exactly the real projective
determinant-zero conic of symmetric `2 × 2` matrices. -/
theorem peirceProjectivization_range_iff (p : ℙ ℝ Mat2) :
    (∃ q : ℙ ℝ (Fin 2 → ℝ), peirceProjectivization q = p) ↔
      IsPeirceConicPoint p := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using Projectivization.ind with
    | h v hv =>
      have hvCoord : (v 0, v 1) ≠ (0, 0) := by
        intro h
        apply hv
        funext i
        fin_cases i
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h
      refine ⟨state (v 0) (v 1), state_ne_zero hvCoord, ?_, ?_, state_det_zero _ _⟩
      · simpa [peirceProjectivization, stateProjectiveRep] using hq.symm
      · rw [state_matrix]
        rfl
  · rintro ⟨A, hA, hp, hsymm, hdet⟩
    let a : ℝ := A 0 0
    let b : ℝ := A 0 1
    let d : ℝ := A 1 1
    have hA_repr : A = !![a, b; b, d] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, d, hsymm]
    have hdet' : a * d - b * b = 0 := by
      simpa [a, b, d, hsymm, Matrix.det_fin_two] using hdet
    by_cases ha : a = 0
    · have hb : b = 0 := by
        rw [ha] at hdet'
        nlinarith [hdet']
      have hd : d ≠ 0 := by
        intro hd0
        apply hA
        rw [hA_repr]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb, hd0]
      let q : ℙ ℝ (Fin 2 → ℝ) :=
        Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 0 else 1)
          (by
            intro hzero
            have h := congrFun hzero 1
            simp at h)
      have hstate : d • state 0 1 = A := by
        rw [state_matrix, hA_repr]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb]
      have hprojective :
          Projectivization.mk ℝ A hA =
            Projectivization.mk ℝ (state 0 1) (state_ne_zero (by norm_num)) :=
        (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2 ⟨d, hstate⟩
      refine ⟨q, ?_⟩
      rw [hp]
      have hqmap : peirceProjectivization q =
          Projectivization.mk ℝ (state 0 1) (state_ne_zero (by norm_num)) := by
        dsimp [q]
        exact peirceProjectivization_mk 0 1 (by norm_num)
      rw [hqmap]
      exact hprojective.symm
    · have hstate : a • state 1 (b / a) = A := by
        have hda : a * d = b * b := by nlinarith [hdet']
        rw [state_matrix, hA_repr]
        ext i j
        fin_cases i <;> fin_cases j
        · simp
        · simp
          field_simp [ha]
        · simp
          field_simp [ha]
        · simp
          field_simp [ha]
          nlinarith [hda]
      have hprojective :
          Projectivization.mk ℝ A hA =
            Projectivization.mk ℝ (state 1 (b / a)) (state_ne_zero (by
              intro h
              exact one_ne_zero (congrArg Prod.fst h))) :=
        (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2 ⟨a, hstate⟩
      let q : ℙ ℝ (Fin 2 → ℝ) :=
        Projectivization.mk ℝ (fun i : Fin 2 => if i = 0 then 1 else b / a)
          (by
            intro hzero
            have h := congrFun hzero 0
            simp at h)
      refine ⟨q, ?_⟩
      rw [hp]
      have hqmap : peirceProjectivization q =
          Projectivization.mk ℝ (state 1 (b / a))
            (state_ne_zero (by intro h; exact one_ne_zero (congrArg Prod.fst h))) := by
        dsimp [q]
        exact peirceProjectivization_mk 1 (b / a) (by norm_num)
      rw [hqmap]
      exact hprojective.symm

/-- The real projective line is algebraically equivalent to the conic of
nonzero symmetric determinant-zero matrix rays parametrized by `state`.

This is an equivalence of projective sets. It carries no topological or
geometric-circle structure by itself. -/
noncomputable def peirceProjectivizationConicEquiv :
    ℙ ℝ (Fin 2 → ℝ) ≃ {p : ℙ ℝ Mat2 // IsPeirceConicPoint p} :=
  Equiv.ofBijective
    (fun q => ⟨peirceProjectivization q,
      (peirceProjectivization_range_iff _).mp ⟨q, rfl⟩⟩)
    ⟨by
      intro q r h
      apply peirceProjectivization_injective
      exact congrArg Subtype.val h,
      by
        intro p
        obtain ⟨q, hq⟩ := (peirceProjectivization_range_iff p.1).mpr p.2
        exact ⟨q, Subtype.ext hq⟩⟩

/-- The equivalence sends each coordinate ray to its Peirce state matrix ray. -/
@[simp]
theorem peirceProjectivizationConicEquiv_apply (q : ℙ ℝ (Fin 2 → ℝ)) :
    (peirceProjectivizationConicEquiv q).1 = peirceProjectivization q := rfl

@[simp]
theorem state_origin : state 1 0 = peirceP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [state,
      InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
      peirceP, peirceSwap]

@[simp]
theorem state_infinity : state 0 1 = 1 - peirceP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [state,
      InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
      peirceP, peirceSwap]

@[simp]
theorem state_equator : state 1 1 = 1 + peirceSwap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [state,
      InfoGeometry.Canonical.TensorPeirceAttentionNetworkAmariYangianPoset.homogProjectiveState,
      peirceP, peirceSwap]

/-- The two zero-variance anchors are distinct projective points. Equality of
their scalar variance values does not identify the primal and complementary
Peirce sheets. -/
theorem projective_origin_ne_infinity :
    coordinateRay 1 0 (by norm_num) ≠ coordinateRay 0 1 (by norm_num) := by
  intro h
  have hval :
      (cayleyProjectiveCircle (coordinateRay 1 0 (by norm_num)) : ℂ) =
        (cayleyProjectiveCircle (coordinateRay 0 1 (by norm_num)) : ℂ) :=
    congrArg (fun q => (cayleyProjectiveCircle q : ℂ)) h
  rw [cayleyProjectiveCircle_three_anchors.1,
    cayleyProjectiveCircle_three_anchors.2.2] at hval
  norm_num at hval

/-! ## Causal dependency poset for the verified projective archetypes

The two dependency branches are kept separate: the homogeneous state descends
to projective matrix rays, then the reciprocal chart law supports the variance
profile; independently, the projective Cayley map supports endpoint
separation. The order is the transitive closure of these dependencies, not a
total ranking of unrelated claims. -/

/-- The six verified stages of the real projective Peirce–Möbius construction. -/
inductive CyclicProjectiveStage : Type
  | homogeneousPeirceState
  | projectiveDescent
  | reciprocalChartSwap
  | varianceProfile
  | cayleyCircleEquivalence
  | endpointSeparation
  deriving DecidableEq, Repr, Inhabited

namespace CyclicProjectiveStage

/-- A topological height for the projective dependency DAG. Equal heights mark
independent base constructions. -/
def rank : CyclicProjectiveStage → ℕ
  | .homogeneousPeirceState => 0
  | .projectiveDescent => 1
  | .reciprocalChartSwap => 2
  | .varianceProfile => 3
  | .cayleyCircleEquivalence => 0
  | .endpointSeparation => 1

/-- Cover relations of the causal dependency poset. The variance and Cayley
branches are incomparable. -/
def causalEdge : CyclicProjectiveStage → CyclicProjectiveStage → Prop
  | .homogeneousPeirceState, .projectiveDescent => True
  | .projectiveDescent, .reciprocalChartSwap => True
  | .reciprocalChartSwap, .varianceProfile => True
  | .cayleyCircleEquivalence, .endpointSeparation => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge :=
  fun a b => by cases a <;> cases b <;> simp [causalEdge] <;> infer_instance

/-- Every cover edge strictly raises the DAG height. -/
theorem causalEdge_implies_rank_lt {a b : CyclicProjectiveStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

theorem transGen_causalEdge_lt_rank {a b : CyclicProjectiveStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_implies_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_implies_rank_lt hbc)

/-- The projective archetype dependency graph is acyclic. -/
theorem causalEdge_acyclic (a : CyclicProjectiveStage) :
    ¬ Relation.TransGen causalEdge a a :=
  fun h => Nat.lt_irrefl (rank a) (transGen_causalEdge_lt_rank h)

/-- The reflexive-transitive closure of the cover edges, written out as the
finite reachability relation so Lean can decide it without extra assumptions. -/
def causalLe : CyclicProjectiveStage → CyclicProjectiveStage → Prop
  | .homogeneousPeirceState, .homogeneousPeirceState => True
  | .homogeneousPeirceState, .projectiveDescent => True
  | .homogeneousPeirceState, .reciprocalChartSwap => True
  | .homogeneousPeirceState, .varianceProfile => True
  | .projectiveDescent, .projectiveDescent => True
  | .projectiveDescent, .reciprocalChartSwap => True
  | .projectiveDescent, .varianceProfile => True
  | .reciprocalChartSwap, .reciprocalChartSwap => True
  | .reciprocalChartSwap, .varianceProfile => True
  | .varianceProfile, .varianceProfile => True
  | .cayleyCircleEquivalence, .cayleyCircleEquivalence => True
  | .cayleyCircleEquivalence, .endpointSeparation => True
  | .endpointSeparation, .endpointSeparation => True
  | _, _ => False

instance instDecidableRelCausalLe : DecidableRel causalLe := by
  intro a b
  cases a <;> cases b <;> simp [causalLe] <;> infer_instance

instance instPartialOrder : PartialOrder CyclicProjectiveStage where
  le := causalLe
  le_refl a := by cases a <;> simp [causalLe]
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [causalLe]
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [causalLe]

/-- Each Hasse edge is included in the declared partial order. -/
theorem causalEdge_le {a b : CyclicProjectiveStage}
    (h : causalEdge a b) : causalLe a b := by
  cases a <;> cases b <;> simp [causalEdge, causalLe] at h ⊢

/-- The homogeneous-state and Cayley-equivalence stages lie on independent
branches of the partial order. -/
theorem homogeneousState_cayley_incomparable :
    ¬ causalLe .homogeneousPeirceState .cayleyCircleEquivalence ∧
    ¬ causalLe .cayleyCircleEquivalence .homogeneousPeirceState := by
  constructor <;> simp [causalLe]

end CyclicProjectiveStage

/-- Native proposition assigned to each projective Peirce–Möbius stage. -/
def cyclicProjectiveStageClaim : CyclicProjectiveStage → Prop
  | .homogeneousPeirceState =>
      (∀ u v : ℝ, state u v = !![u ^ 2, u * v; u * v, v ^ 2]) ∧
      (∀ u v : ℝ,
        state u v * state u v = (u ^ 2 + v ^ 2) • state u v)
  | .projectiveDescent =>
      ∀ (u v : ℝ) (h : (u, v) ≠ (0, 0)),
        peirceProjectivization (coordinateRay u v h) =
          Projectivization.mk ℝ (state u v) (state_ne_zero h)
  | .reciprocalChartSwap =>
      (∀ q, peirceProjectivization (coordinateSwapProjective q) =
        conjugatePeirceSwapProjective (peirceProjectivization q)) ∧
      (∀ q, coordinateSwapProjective (coordinateSwapProjective q) = q) ∧
      (∀ u v : ℝ, conjugatePeirceSwap (state u v) = state v u)
  | .varianceProfile =>
      (∀ q, peirceProjectiveVariance (coordinateSwapProjective q) =
        peirceProjectiveVariance q) ∧
      (peirceProjectiveVariance (coordinateRay 1 0 (by norm_num)) = 0 ∧
        peirceProjectiveVariance (coordinateRay 1 1 (by norm_num)) = 1 ∧
        peirceProjectiveVariance (coordinateRay 0 1 (by norm_num)) = 0)
  | .cayleyCircleEquivalence =>
      Function.Injective cayleyProjectiveCircle ∧
        Function.Surjective cayleyProjectiveCircle
  | .endpointSeparation =>
      coordinateRay 1 0 (by norm_num) ≠ coordinateRay 0 1 (by norm_num)

/-- Each projective archetype stage is discharged by its concrete owner theorem. -/
theorem cyclicProjectiveStageClaim_all (s : CyclicProjectiveStage) :
    cyclicProjectiveStageClaim s := by
  cases s with
  | homogeneousPeirceState =>
      exact ⟨fun u v => state_matrix u v, fun u v => state_mul_state u v⟩
  | projectiveDescent =>
      intro u v h
      exact peirceProjectivization_mk u v h
  | reciprocalChartSwap =>
      exact ⟨peirceProjectivization_coordinateSwap,
        coordinateSwapProjective_involutive,
        conjugatePeirceSwap_state⟩
  | varianceProfile =>
      exact ⟨peirceProjectiveVariance_coordinateSwap,
        peirceProjectiveVariance_three_anchors⟩
  | cayleyCircleEquivalence =>
      exact ⟨cayleyProjectiveCircle_injective, cayleyProjectiveCircle_surjective⟩
  | endpointSeparation => exact projective_origin_ne_infinity

/-- Closure of the projective Möbius archetypes established in this owner:
the variance is invariant under chart swap with anchors `(0,1,0)`, the two
endpoint rays are distinct, and the Cayley map is bijective as a set map. -/
theorem cyclicProjectiveMobius_archetype_closure
    (q : ℙ ℝ (Fin 2 → ℝ)) :
    peirceProjectiveVariance (coordinateSwapProjective q) =
      peirceProjectiveVariance q ∧
    (peirceProjectiveVariance (coordinateRay 1 0 (by norm_num)) = 0 ∧
      peirceProjectiveVariance (coordinateRay 1 1 (by norm_num)) = 1 ∧
      peirceProjectiveVariance (coordinateRay 0 1 (by norm_num)) = 0) ∧
    coordinateRay 1 0 (by norm_num) ≠ coordinateRay 0 1 (by norm_num) ∧
    Function.Injective cayleyProjectiveCircle ∧
    Function.Surjective cayleyProjectiveCircle := by
  exact ⟨peirceProjectiveVariance_coordinateSwap q,
    peirceProjectiveVariance_three_anchors,
    projective_origin_ne_infinity,
    cayleyProjectiveCircle_injective,
    cayleyProjectiveCircle_surjective⟩

end InfoGeometry.Canonical.CyclicMobiusProjectivization

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
import InfoGeometry.Twistor.PenroseNullProjector
import InfoGeometry.Geometry.NewmanPenroseNullTetrad
import InfoGeometry.Canonical.PenroseOnsagerYangCondensationPristineChain
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.MoorePenroseDrazinObstruction

/-!
# Constructive Bridge: Minkowski `(1,3)` Slice, Newman--Penrose Tetrad, Spinor Dyads, and Twistor Moore--Penrose Defect

Connects four previously separate Penrose and spacetime formalisms in `lean/InfoGeometry/`
by explicit linear maps, quadratic identities, and finite matrix block algebra:

1. **Minkowski `(1,3)` $\leftrightarrow$ Newman--Penrose Null Tetrad $\leftrightarrow$ Pauli Soldering**:
   Embeds `Minkowski13 := ℝ × (Fin 3 → ℝ)` into the complex Newman--Penrose carrier
   `NewmanPenrose.Carrier := Fin 4 → ℂ` and gives the explicit complex-linear isomorphism
   `npCarrierToSpacetimeMatrix : NewmanPenrose.Carrier ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ`
   identifying `lorentzBilinear x x = (-2 : ℂ) * Matrix.det (npCarrierToSpacetimeMatrix x)` and
   matching `paravectorToSolderingMatrix p` identically on real vectors.
2. **Penrose--Onsager--Yang Rank-1 Condensate Spinor Dyad $\leftrightarrow$ Null Flagpole**:
   Defines the Hopf/Bloch spinor-to-spacetime map `spinorToMinkowski13` on `Mode (Fin 2)`, proves
   `paravectorToSolderingMatrix (spinorToMinkowski13 χ) = rankOneKernel χ`, proves nullity on
   the `(5,5)` slice (`Q55 (minkowskiSlice (spinorToMinkowski13 χ)) = 0`), causal positivity,
   `U(1)` phase invariance, and explicit symplectic-mate Penrose incidence (`mulVec = 0`).
3. **Oblique Penrose Incidence Idempotent vs. Moore--Penrose Support Projector**:
   Realizes the Witt-frame oblique projector behind `PenroseNullProjector.incidenceProjection`
   as the `2 × 2` block matrix `fromBlocks 0 (-Complex.I • X) 0 1`, proves it is idempotent
   (`IsDrazinInverse P P 1`), constructs its closed-form Moore--Penrose inverse whenever
   `Xᴴ * X = (r : ℂ) • 1` with `0 ≤ r` (such as any spatial Pauli matrix `p.1 = 0`), proves
   exact vanishing `incidenceProjectorMismatch X r = 0 ↔ X = 0`, square-zero nilpotency, and
   non-normality (OpenGauss Trap T16 noncommutativity witness).
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge

open scoped Matrix ComplexOrder
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PerjesConventions
open InfoGeometry.Twistor.PenroseNullProjector
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Geometry.NewmanPenrose
open InfoGeometry.Quantum.PenroseOnsagerYang
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.MoorePenroseDrazinObstruction

/-! ## 1. Minkowski `(1,3)`, Newman--Penrose Carrier, and Pauli Soldering -/

/-- Canonical ℝ-linear embedding of `(1,3)` Minkowski vectors into the complex
Newman--Penrose four-vector carrier `Fin 4 → ℂ`. -/
def minkowski13ToNPCarrier :
    Minkowski13 →ₗ[ℝ] InfoGeometry.Geometry.NewmanPenrose.Carrier where
  toFun p := ![(p.1 : ℂ), (p.2 0 : ℂ), (p.2 1 : ℂ), (p.2 2 : ℂ)]
  map_add' p q := by
    ext i
    fin_cases i <;> simp [Pi.add_apply]
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply]

theorem minkowski13ToNPCarrier_injective : Function.Injective minkowski13ToNPCarrier := by
  intro p q hpq
  apply Prod.ext
  · have h0 := congrFun hpq 0
    exact Complex.ofReal_injective (by simpa [minkowski13ToNPCarrier] using h0)
  · funext i
    fin_cases i
    · have h1 := congrFun hpq 1
      exact Complex.ofReal_injective (by simpa [minkowski13ToNPCarrier] using h1)
    · have h2 := congrFun hpq 2
      exact Complex.ofReal_injective (by simpa [minkowski13ToNPCarrier] using h2)
    · have h3 := congrFun hpq 3
      exact Complex.ofReal_injective (by simpa [minkowski13ToNPCarrier] using h3)

/-- Complex-linear isomorphism identifying the complexified spacetime `NewmanPenrose.Carrier`
with `2 × 2` complex spinor matrices in the Pauli/Infeld--van der Waerden basis. -/
def npCarrierToSpacetimeMatrix :
    InfoGeometry.Geometry.NewmanPenrose.Carrier ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun x := !![x 0 + x 3, x 1 - Complex.I * x 2; x 1 + Complex.I * x 2, x 0 - x 3]
  invFun M :=
    ![(M 0 0 + M 1 1) / 2,
      (M 0 1 + M 1 0) / 2,
      Complex.I * (M 0 1 - M 1 0) / 2,
      (M 0 0 - M 1 1) / 2]
  left_inv x := by
    ext i
    fin_cases i <;> simp
    calc
      Complex.I * (x 1 - Complex.I * x 2 - (x 1 + Complex.I * x 2)) / 2
          = -(Complex.I * Complex.I) * x 2 := by ring
      _ = x 2 := by rw [Complex.I_mul_I]; ring
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · ring
    · calc
        (M 0 1 + M 1 0) / 2 - Complex.I * (Complex.I * (M 0 1 - M 1 0) / 2)
            = (M 0 1 + M 1 0) / 2 - (Complex.I * Complex.I) * (M 0 1 - M 1 0) / 2 := by ring
        _ = M 0 1 := by rw [Complex.I_mul_I]; ring
    · calc
        (M 0 1 + M 1 0) / 2 + Complex.I * (Complex.I * (M 0 1 - M 1 0) / 2)
            = (M 0 1 + M 1 0) / 2 + (Complex.I * Complex.I) * (M 0 1 - M 1 0) / 2 := by ring
        _ = M 1 0 := by rw [Complex.I_mul_I]; ring
    · ring
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Pi.add_apply] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring

/-- Expressing the `2 × 2` spinor spacetime matrix directly in Newman--Penrose tetrad
coordinates `npCoordinates x`. -/
theorem npCarrierToSpacetimeMatrix_eq_npCoordinates
    (x : InfoGeometry.Geometry.NewmanPenrose.Carrier) :
    npCarrierToSpacetimeMatrix x =
      !![(2 : ℂ) * npCoordinates x 0, npCoordinates x 2;
        npCoordinates x 3, (1 / 2 : ℂ) * npCoordinates x 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [npCarrierToSpacetimeMatrix, npCoordinates]
  ring

/-- On real Minkowski vectors, the Newman--Penrose spacetime matrix agrees identically with
the Pauli soldering matrix `paravectorToSolderingMatrix p`. -/
theorem npCarrierToSpacetimeMatrix_minkowski13 (p : Minkowski13) :
    npCarrierToSpacetimeMatrix (minkowski13ToNPCarrier p) =
      paravectorToSolderingMatrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [npCarrierToSpacetimeMatrix, minkowski13ToNPCarrier, paravectorToSolderingMatrix,
      minkowski13ToMinkowski4,
      InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
      InfoGeometry.Geometry.PauliParavectorBridge.toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix]

/-- Exact determinant-metric relation between the Newman--Penrose Lorentz form and the
`2 × 2` spacetime matrix determinant:
`lorentzBilinear x x = (-2 : ℂ) * det (npCarrierToSpacetimeMatrix x)`. -/
theorem lorentzBilinear_eq_neg_two_det
    (x : InfoGeometry.Geometry.NewmanPenrose.Carrier) :
    lorentzBilinear x x = (-2 : ℂ) * Matrix.det (npCarrierToSpacetimeMatrix x) := by
  simp only [lorentzBilinear, npCarrierToSpacetimeMatrix, LinearEquiv.coe_mk,
    Matrix.det_fin_two]
  calc
    2 * (-x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3)
        = (-2 : ℂ) * ((x 0 + x 3) * (x 0 - x 3) - (x 1 * x 1 - (Complex.I * Complex.I) * (x 2 * x 2))) := by
          rw [Complex.I_mul_I]; ring
    _ = (-2 : ℂ) * ((x 0 + x 3) * (x 0 - x 3) - (x 1 - Complex.I * x 2) * (x 1 + Complex.I * x 2)) := by
          ring

/-- Four-way equivalence of nullity across `Cl(5,5)` celestial slice, paravector form,
Newman--Penrose Lorentz form, and Pauli soldering determinant. -/
theorem minkowski13_four_way_null_equiv (p : Minkowski13) :
    InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) = 0 ↔
      paravectorQuadratic p = 0 ∧
      lorentzBilinear (minkowski13ToNPCarrier p) (minkowski13ToNPCarrier p) = 0 ∧
      Matrix.det (paravectorToSolderingMatrix p) = 0 := by
  have hq : InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice p) = paravectorQuadratic p := by
    rw [Q55_minkowskiSlice, paravectorQuadratic]
  have hdet_np :
      lorentzBilinear (minkowski13ToNPCarrier p) (minkowski13ToNPCarrier p) =
        (-2 : ℂ) * Matrix.det (paravectorToSolderingMatrix p) := by
    rw [lorentzBilinear_eq_neg_two_det, npCarrierToSpacetimeMatrix_minkowski13]
  constructor
  · intro h0
    have hp0 : paravectorQuadratic p = 0 := hq.symm.trans h0
    have hdet0 : Matrix.det (paravectorToSolderingMatrix p) = 0 :=
      (null_paravector_iff_det_zero p).mp hp0
    exact ⟨hp0, by rw [hdet_np, hdet0, mul_zero], hdet0⟩
  · rintro ⟨hp0, _, _⟩
    exact hq.trans hp0

/-! ## 2. Penrose--Onsager--Yang Condensate Dyad $\leftrightarrow$ Null Flagpole & Twistor Incidence -/

/-- The Hopf/Bloch flagpole map sending a two-component quantum condensate mode `χ : Mode (Fin 2)`
to the future-directed null `(1,3)` vector whose Pauli matrix is `χ ⊗ χ†`. -/
def spinorToMinkowski13 (χ : Mode (Fin 2)) : Minkowski13 :=
  ((Complex.normSq (χ 0) + Complex.normSq (χ 1)) / 2,
    ![(χ 0 * starRingEnd ℂ (χ 1)).re,
      -(χ 0 * starRingEnd ℂ (χ 1)).im,
      (Complex.normSq (χ 0) - Complex.normSq (χ 1)) / 2])

/-- **Fundamental Dyad-Soldering Identity**: The Pauli soldering matrix of `spinorToMinkowski13 χ`
equals identically the Penrose--Onsager--Yang `rankOneKernel χ`. -/
theorem paravectorToSolderingMatrix_spinorToMinkowski13 (χ : Mode (Fin 2)) :
    paravectorToSolderingMatrix (spinorToMinkowski13 χ) = rankOneKernel χ := by
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;>
      simp [paravectorToSolderingMatrix, spinorToMinkowski13, rankOneKernel,
        minkowski13ToMinkowski4, InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
        InfoGeometry.Geometry.PauliParavectorBridge.toPauliParavector,
        InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix,
        Complex.normSq_apply] <;>
      ring
  · apply Complex.ext <;>
      simp [paravectorToSolderingMatrix, spinorToMinkowski13, rankOneKernel,
        minkowski13ToMinkowski4, InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
        InfoGeometry.Geometry.PauliParavectorBridge.toPauliParavector,
        InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix]
  · apply Complex.ext <;>
      simp [paravectorToSolderingMatrix, spinorToMinkowski13, rankOneKernel,
        minkowski13ToMinkowski4, InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
        InfoGeometry.Geometry.PauliParavectorBridge.toPauliParavector,
        InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix] <;>
      ring
  · apply Complex.ext <;>
      simp [paravectorToSolderingMatrix, spinorToMinkowski13, rankOneKernel,
        minkowski13ToMinkowski4, InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
        InfoGeometry.Geometry.PauliParavectorBridge.toPauliParavector,
        InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix,
        Complex.normSq_apply] <;>
      ring

/-- Any Penrose--Onsager--Yang condensate spinor produces a future-causal null vector on
the `Q55` celestial slice whose time component equals `modeNormSq χ / 2`. -/
theorem spinorToMinkowski13_null_and_causal (χ : Mode (Fin 2)) :
    InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice (spinorToMinkowski13 χ)) = 0 ∧
      0 ≤ (spinorToMinkowski13 χ).1 ∧
      (spinorToMinkowski13 χ).1 = modeNormSq χ / 2 := by
  have htime : (spinorToMinkowski13 χ).1 = modeNormSq χ / 2 := by
    simp [spinorToMinkowski13, modeNormSq, Fin.sum_univ_two]
  have hnonneg : 0 ≤ (spinorToMinkowski13 χ).1 := by
    rw [htime]
    have hns : 0 ≤ modeNormSq χ := by
      unfold modeNormSq
      exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (χ i)
    linarith
  have hdet0 : Matrix.det (rankOneKernel χ) = 0 := by
    simp only [rankOneKernel, Matrix.det_fin_two]
    ring
  have hp0 : paravectorQuadratic (spinorToMinkowski13 χ) = 0 := by
    rw [null_paravector_iff_det_zero, paravectorToSolderingMatrix_spinorToMinkowski13]
    exact hdet0
  have hq0 : InfoGeometry.Clifford.Clifford55.Q55 (minkowskiSlice (spinorToMinkowski13 χ)) = 0 := by
    rw [Q55_minkowskiSlice, ← paravectorQuadratic]
    exact hp0
  exact ⟨hq0, hnonneg, htime⟩

/-- Global `U(1)` phase transformations leave the induced null flagpole vector invariant. -/
theorem spinorToMinkowski13_phase_invariant
    {u : ℂ} (hu : u * starRingEnd ℂ u = 1) (χ : Mode (Fin 2)) :
    spinorToMinkowski13 (scalarAction u χ) = spinorToMinkowski13 χ := by
  have hp : paravectorToSolderingMatrix (spinorToMinkowski13 (scalarAction u χ)) =
      paravectorToSolderingMatrix (spinorToMinkowski13 χ) := by
    rw [paravectorToSolderingMatrix_spinorToMinkowski13,
      paravectorToSolderingMatrix_spinorToMinkowski13,
      rankOneKernel_globalPhase_invariant hu χ]
  have hnp : minkowski13ToNPCarrier (spinorToMinkowski13 (scalarAction u χ)) =
      minkowski13ToNPCarrier (spinorToMinkowski13 χ) := by
    apply npCarrierToSpacetimeMatrix.injective
    rw [npCarrierToSpacetimeMatrix_minkowski13, npCarrierToSpacetimeMatrix_minkowski13]
    exact hp
  exact minkowski13ToNPCarrier_injective hnp

/-- Symplectic mate spinor orthogonal to `χ` under the rank-one Hermitian outer product. -/
def spinorSymplecticMate (χ : Mode (Fin 2)) : Spinor2 :=
  ![-starRingEnd ℂ (χ 1), starRingEnd ℂ (χ 0)]

theorem spinorSymplecticMate_ne_zero {χ : Mode (Fin 2)} (hχ : χ ≠ 0) :
    spinorSymplecticMate χ ≠ 0 := by
  intro hzero
  apply hχ
  ext i
  fin_cases i
  · have h1 := congrFun hzero 1
    change starRingEnd ℂ (χ 0) = 0 at h1
    rw [← map_zero (starRingEnd ℂ)] at h1
    exact (starRingEnd ℂ).injective h1
  · have h0 := congrFun hzero 0
    change -starRingEnd ℂ (χ 1) = 0 at h0
    have hconj1 : starRingEnd ℂ (χ 1) = 0 := neg_eq_zero.mp h0
    rw [← map_zero (starRingEnd ℂ)] at hconj1
    exact (starRingEnd ℂ).injective hconj1

theorem mulVec_rankOneKernel_spinorSymplecticMate (χ : Mode (Fin 2)) :
    Matrix.mulVec (rankOneKernel χ) (spinorSymplecticMate χ) = 0 := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rankOneKernel, spinorSymplecticMate] <;>
    ring

/-- The symplectic mate spinor supplies a nontrivial twistor incident at `(0, spinorSymplecticMate χ)`
on the lightcone point `spinorToMinkowski13 χ`. -/
theorem boundaryIncidence_spinorToMinkowski13_mate (χ : Mode (Fin 2)) :
    boundaryIncidenceLinearMap (spinorToMinkowski13 χ) (spinorSymplecticMate χ) =
      (0, spinorSymplecticMate χ) := by
  apply incident_boundary_kernel_spinor
  rw [paravectorToSolderingMatrix_spinorToMinkowski13]
  exact mulVec_rankOneKernel_spinorSymplecticMate χ

/-! ## 3. Oblique Penrose Incidence Projector vs. Moore--Penrose Support Projector -/

/-- Transport an element `Z : Twistor4 := Spinor2 × Spinor2` into `Fin 2 ⊕ Fin 2 → ℂ`. -/
def twistor4ToBlockVec (Z : Twistor4) : Fin 2 ⊕ Fin 2 → ℂ :=
  Sum.elim Z.1 Z.2

/-- Witt-frame `4 × 4` block matrix representing the oblique Penrose incidence projector
`Z ↦ paperIncidence X Z.2 = (-Complex.I • (X *ᵥ Z.2), Z.2)`. -/
def wittIncidenceBlockIdempotent (X : ComplexSpacetime) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 0 (-Complex.I • X) 0 1

/-- Action of `wittIncidenceBlockIdempotent X` on a Witt twistor equals `paperIncidence X Z.2`. -/
theorem wittIncidenceBlockIdempotent_mulVec (X : ComplexSpacetime) (Z : Twistor4) :
    wittIncidenceBlockIdempotent X *ᵥ twistor4ToBlockVec Z =
      twistor4ToBlockVec (paperIncidence X Z.2) := by
  ext i
  rcases i with i | i
  · fin_cases i <;>
      simp [wittIncidenceBlockIdempotent, twistor4ToBlockVec, paperIncidence_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      ring
  · fin_cases i <;>
      simp [wittIncidenceBlockIdempotent, twistor4ToBlockVec, paperIncidence_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Conjugating `incidenceProjection X` back into the Witt frame gives `wittIncidenceBlockIdempotent X`. -/
theorem witt_incidenceProjection_block_correspondence
    (X : ComplexSpacetime) (Z : Twistor4) :
    twistor4ToBlockVec (wittToDiagonal.symm (incidenceProjection X (wittToDiagonal Z))) =
      wittIncidenceBlockIdempotent X *ᵥ twistor4ToBlockVec Z := by
  rw [wittIncidenceBlockIdempotent_mulVec, incidenceProjection_apply, incidenceEmbedding_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- `wittIncidenceBlockIdempotent X` is strictly idempotent (`P * P = P`). -/
theorem wittIncidenceBlockIdempotent_sq (X : ComplexSpacetime) :
    wittIncidenceBlockIdempotent X * wittIncidenceBlockIdempotent X =
      wittIncidenceBlockIdempotent X := by
  unfold wittIncidenceBlockIdempotent
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Hence every `wittIncidenceBlockIdempotent X` is its own index-1 Drazin inverse. -/
theorem wittIncidenceBlockIdempotent_isDrazin (X : ComplexSpacetime) :
    IsDrazinInverse (wittIncidenceBlockIdempotent X) (wittIncidenceBlockIdempotent X) 1 :=
  IsDrazinInverse.of_idempotent (wittIncidenceBlockIdempotent_sq X)

/-- Explicit closed-form Euclidean Moore--Penrose inverse of `wittIncidenceBlockIdempotent X`
for any `X` satisfying `Xᴴ * X = (r : ℂ) • 1`. -/
def wittIncidenceBlockMPInverse (X : ComplexSpacetime) (r : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  let s : ℂ := ((1 + r : ℝ) : ℂ)⁻¹
  Matrix.fromBlocks 0 0 (s • (Complex.I • Xᴴ)) (s • 1)

lemma wittIncidenceBlockMPInverse_mul_self
    (X : ComplexSpacetime) (r : ℝ) (hr : 0 ≤ r)
    (hX : Xᴴ * X = (r : ℂ) • (1 : ComplexSpacetime)) :
    wittIncidenceBlockMPInverse X r * wittIncidenceBlockIdempotent X =
      Matrix.fromBlocks (0 : ComplexSpacetime) 0 0 1 := by
  have hpos : (1 + r : ℝ) ≠ 0 := by linarith [hr]
  have hc : ((1 + r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos
  let s : ℂ := ((1 + r : ℝ) : ℂ)⁻¹
  have hs_mul : s * ((1 + r : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hc
  unfold wittIncidenceBlockMPInverse wittIncidenceBlockIdempotent
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.mul_one]
  congr 1
  change s • (Complex.I • Xᴴ) * (-Complex.I • X) + s • (1 : ComplexSpacetime) = 1
  have hBB : (Complex.I • Xᴴ) * (-Complex.I • X) = (r : ℂ) • (1 : ComplexSpacetime) := by
    calc
      (Complex.I • Xᴴ) * (-Complex.I • X)
          = (Complex.I * -Complex.I) • (Xᴴ * X) := by
              simp [smul_smul]
      _ = (1 : ℂ) • (Xᴴ * X) := by
            have hi : Complex.I * -Complex.I = (1 : ℂ) := by
              calc
                Complex.I * -Complex.I = -(Complex.I * Complex.I) := by ring
                _ = -(-1) := by rw [Complex.I_mul_I]
                _ = 1 := by ring
            rw [hi]
      _ = (r : ℂ) • (1 : ComplexSpacetime) := by rw [one_smul, hX]
  calc
    s • (Complex.I • Xᴴ) * (-Complex.I • X) + s • (1 : ComplexSpacetime)
        = s • ((Complex.I • Xᴴ) * (-Complex.I • X)) + s • (1 : ComplexSpacetime) := by
            rw [Matrix.smul_mul]
    _ = s • ((r : ℂ) • (1 : ComplexSpacetime)) + s • (1 : ComplexSpacetime) := by rw [hBB]
    _ = s • ((r : ℂ) • (1 : ComplexSpacetime) + (1 : ComplexSpacetime)) := by rw [← smul_add]
    _ = s • (((r : ℂ) + 1) • (1 : ComplexSpacetime)) := by
          congr 1
          rw [add_smul, one_smul]
    _ = (s * ((1 + r : ℝ) : ℂ)) • (1 : ComplexSpacetime) := by
          rw [smul_smul]
          congr 2
          push_cast; ring
    _ = 1 := by rw [hs_mul, one_smul]

theorem isMoorePenroseInverse_wittIncidenceBlock
    (X : ComplexSpacetime) (r : ℝ) (hr : 0 ≤ r)
    (hX : Xᴴ * X = (r : ℂ) • (1 : ComplexSpacetime)) :
    IsMoorePenroseInverse (wittIncidenceBlockIdempotent X) (wittIncidenceBlockMPInverse X r) := by
  let s : ℂ := ((1 + r : ℝ) : ℂ)⁻¹
  have hs_conj : starRingEnd ℂ s = s := by
    simp only [s, ← Complex.ofReal_inv, Complex.conj_ofReal]
  have hMP_eq := wittIncidenceBlockMPInverse_mul_self X r hr hX
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · calc
      wittIncidenceBlockIdempotent X * wittIncidenceBlockMPInverse X r *
          wittIncidenceBlockIdempotent X
          = wittIncidenceBlockIdempotent X *
              (wittIncidenceBlockMPInverse X r * wittIncidenceBlockIdempotent X) := by
                rw [Matrix.mul_assoc]
      _ = Matrix.fromBlocks 0 (-Complex.I • X) 0 1 * Matrix.fromBlocks 0 0 0 1 := by
            rw [hMP_eq]; rfl
      _ = wittIncidenceBlockIdempotent X := by
            rw [Matrix.fromBlocks_multiply]
            simp [wittIncidenceBlockIdempotent]
  · calc
      wittIncidenceBlockMPInverse X r * wittIncidenceBlockIdempotent X *
          wittIncidenceBlockMPInverse X r
          = Matrix.fromBlocks 0 0 0 1 * wittIncidenceBlockMPInverse X r := by rw [hMP_eq]
      _ = wittIncidenceBlockMPInverse X r := by
            unfold wittIncidenceBlockMPInverse
            rw [Matrix.fromBlocks_multiply]
            simp
  · change (wittIncidenceBlockIdempotent X * wittIncidenceBlockMPInverse X r)ᴴ =
      wittIncidenceBlockIdempotent X * wittIncidenceBlockMPInverse X r
    unfold wittIncidenceBlockIdempotent wittIncidenceBlockMPInverse
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, zero_add, Matrix.one_mul]
    rw [Matrix.fromBlocks_conjTranspose]
    have hs_star : star s = s := hs_conj
    have hsi : -Complex.I * (s * Complex.I) = s := by
      calc
        -Complex.I * (s * Complex.I) = -(Complex.I * Complex.I) * s := by ring
        _ = -(-1) * s := by rw [Complex.I_mul_I]
        _ = s := by ring
    have h11_mul : (-Complex.I • X) * (s • (Complex.I • Xᴴ)) = s • (X * Xᴴ) := by
      calc
        (-Complex.I • X) * (s • (Complex.I • Xᴴ))
            = (-Complex.I * (s * Complex.I)) • (X * Xᴴ) := by
                simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
                congr 1
                ring
        _ = s • (X * Xᴴ) := by rw [hsi]
    have h11 :
        ((-Complex.I • X) * (s • (Complex.I • Xᴴ)))ᴴ =
          (-Complex.I • X) * (s • (Complex.I • Xᴴ)) := by
      rw [h11_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hs_star]
    have h12 : (s • (Complex.I • Xᴴ))ᴴ = (-Complex.I • X) * (s • (1 : ComplexSpacetime)) := by
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_smul, Matrix.mul_one]
      have hsc : star s = s := hs_star
      have hic : star Complex.I = -Complex.I := by simp
      rw [hsc, hic, smul_comm]
    have h21 : ((-Complex.I • X) * (s • (1 : ComplexSpacetime)))ᴴ = s • (Complex.I • Xᴴ) := by
      simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.conjTranspose_smul]
      have hsc : star s = s := hs_star
      have hnic : star (-Complex.I) = Complex.I := by simp
      rw [hsc, hnic, smul_comm]
    have h22 : (s • (1 : ComplexSpacetime))ᴴ = s • (1 : ComplexSpacetime) := by
      simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hs_star]
    change Matrix.fromBlocks
      ((-Complex.I • X) * (s • (Complex.I • Xᴴ)))ᴴ
      (s • (Complex.I • Xᴴ))ᴴ
      ((-Complex.I • X) * (s • (1 : ComplexSpacetime)))ᴴ
      (s • (1 : ComplexSpacetime))ᴴ =
      Matrix.fromBlocks
        ((-Complex.I • X) * (s • (Complex.I • Xᴴ)))
        ((-Complex.I • X) * (s • (1 : ComplexSpacetime)))
        (s • (Complex.I • Xᴴ))
        (s • (1 : ComplexSpacetime))
    rw [h11, h12, h21, h22]
  · rw [hMP_eq]
    change (Matrix.fromBlocks (0 : ComplexSpacetime) 0 0 1)ᴴ =
      Matrix.fromBlocks 0 0 0 1
    rw [Matrix.fromBlocks_conjTranspose]
    simp

/-- Projector mismatch `Δ = P_D - P_MP` between the Drazin (oblique) Penrose incidence
projector and its Euclidean Moore--Penrose support projector. -/
def incidenceProjectorMismatch (X : ComplexSpacetime) (r : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  projectorMismatch (wittIncidenceBlockIdempotent X)
    (wittIncidenceBlockIdempotent X) (wittIncidenceBlockMPInverse X r)

theorem incidenceProjectorMismatch_eq
    (X : ComplexSpacetime) (r : ℝ) (hr : 0 ≤ r)
    (hX : Xᴴ * X = (r : ℂ) • (1 : ComplexSpacetime)) :
    incidenceProjectorMismatch X r = Matrix.fromBlocks 0 (-Complex.I • X) 0 0 := by
  have hP2 := wittIncidenceBlockIdempotent_sq X
  have hMP_eq := wittIncidenceBlockMPInverse_mul_self X r hr hX
  unfold incidenceProjectorMismatch projectorMismatch spectralProjector metricProjector
    IsDrazinInverse.projection IsMoorePenroseInverse.leftProjector
  rw [hP2, hMP_eq]
  unfold wittIncidenceBlockIdempotent
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

/-- Exact vanishing criterion for the twistor incidence projector mismatch: `Δ = 0 ↔ X = 0`. -/
theorem incidenceProjectorMismatch_eq_zero_iff
    (X : ComplexSpacetime) (r : ℝ) (hr : 0 ≤ r)
    (hX : Xᴴ * X = (r : ℂ) • (1 : ComplexSpacetime)) :
    incidenceProjectorMismatch X r = 0 ↔ X = 0 := by
  rw [incidenceProjectorMismatch_eq X r hr hX]
  constructor
  · intro h
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ =>
      M (Sum.inl i) (Sum.inr j)) h
    simp at hij
    exact hij
  · rintro rfl
    simp

/-- The nonzero incidence mismatch is square-zero and cannot satisfy index-1 Drazin equations
together with any Moore--Penrose inverse (non-EP chiral/oblique defect). -/
theorem incidenceProjectorMismatch_nilpotent_and_obstruction
    (X : ComplexSpacetime) (r : ℝ) (hr : 0 ≤ r)
    (hX : Xᴴ * X = (r : ℂ) • (1 : ComplexSpacetime)) (hX0 : X ≠ 0) :
    incidenceProjectorMismatch X r * incidenceProjectorMismatch X r = 0 ∧
      incidenceProjectorMismatch X r ≠ 0 ∧
      ∀ b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ,
        IsMoorePenroseInverse (incidenceProjectorMismatch X r) b →
        ¬ IsDrazinInverse (incidenceProjectorMismatch X r) b 1 := by
  have heq := incidenceProjectorMismatch_eq X r hr hX
  have hsq : incidenceProjectorMismatch X r * incidenceProjectorMismatch X r = 0 := by
    rw [heq, Matrix.fromBlocks_multiply]
    simp
  have hne : incidenceProjectorMismatch X r ≠ 0 := by
    intro h0
    exact hX0 ((incidenceProjectorMismatch_eq_zero_iff X r hr hX).mp h0)
  refine ⟨hsq, hne, ?_⟩
  intro b hb
  exact square_zero_moore_penrose_not_drazin_index_one hb hsq hne

/-- Concrete spatial Pauli witness: every purely spatial vector `(0, v)` yields a Hermitian
Pauli matrix with `Xᴴ * X = (r : ℂ) • 1` where `r = ∑ i, v i ^ 2 ≥ 0`. -/
theorem spatial_pauli_sq_eq_smul (v : Fin 3 → ℝ) :
    let X := paravectorToSolderingMatrix (0, v)
    let r : ℝ := ∑ i : Fin 3, v i ^ 2
    0 ≤ r ∧ Xᴴ * X = (r : ℂ) • (1 : ComplexSpacetime) := by
  intro X r
  have hr : 0 ≤ r := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  refine ⟨hr, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, r, paravectorToSolderingMatrix, minkowski13ToMinkowski4,
      InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
      InfoGeometry.Geometry.PauliParavectorBridge.toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  · ring_nf; rw [Complex.I_sq]; ring
  · ring
  · ring
  · ring_nf; rw [Complex.I_sq]; ring

/-- OpenGauss Trap T16 Noncommutativity Witness: for `X = 1`, the oblique Penrose incidence
projector `P = wittIncidenceBlockIdempotent 1` fails to commute with its Euclidean adjoint
`Pᴴ` (`P * Pᴴ ≠ Pᴴ * P`). -/
theorem wittIncidenceBlockIdempotent_nonnormal_witness :
    let P := wittIncidenceBlockIdempotent (1 : ComplexSpacetime)
    P * Pᴴ ≠ Pᴴ * P := by
  intro P hcomm
  have h00 := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ =>
    M (Sum.inl 0) (Sum.inl 0)) hcomm
  simp [P, wittIncidenceBlockIdempotent, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_conjTranspose] at h00

end InfoGeometry.Twistor.PenroseMinkowskiTetradDyadBridge

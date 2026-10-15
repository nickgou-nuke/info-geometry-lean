import InfoGeometry.QuantumContext.PetzDataProcessingMonotonicity
import InfoGeometry.QuantumContext.ArakiPetzEntropyMonotonicity
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
import InfoGeometry.Canonical.MatrixStageInductiveLimit

/-!
# Petz polynomial compatibility with the matrix-stage direct limit

The Petz and pinching expressions are defined as ring polynomials. This file
transports those expressions along the repository's existing complex matrix
stage homomorphisms and into its quotient direct limit. It does not assert
positivity, complete positivity, trace preservation, or entropy monotonicity
for these expressions.
-/

namespace InfoGeometry.QuantumContext.PetzMatrixStageLimit

open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering

/-! ## The Stiefel defect in the faithful matrix-stage limit

The real Stiefel reconstruction in `PetzDataProcessingMonotonicity` is a
different construction from the generic ring-polynomial `petzRecoveryMap`.
Here we transport its actual defect matrix to the existing complex matrix
tower, rather than identify the two maps by terminology.
-/

/-- Encode a real `2 × 2` matrix in the existing complex `Stage 1` carrier. -/
def realMat2ToStage1 (M : Matrix (Fin 2) (Fin 2) ℝ) : Stage 1 :=
  embedMat2ToStage1 (M.map Complex.ofRealHom)

/-- The standard real-to-complex coefficient map is injective on `2 × 2`
matrices. -/
theorem map_ofReal_mat2_injective :
    Function.Injective (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.map Complex.ofRealHom) := by
  intro M N h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

/-- The existing finite-stage coordinate encoding is injective. -/
theorem embedMat2ToStage1_injective :
    Function.Injective (embedMat2ToStage1) := by
  intro M N h
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun h (bitword1Equiv.symm i)) (bitword1Equiv.symm j)
  simpa [embedMat2ToStage1] using hij

/-- Real matrices remain distinct after encoding in `Stage 1`. -/
theorem realMat2ToStage1_injective : Function.Injective realMat2ToStage1 := by
  intro M N h
  apply map_ofReal_mat2_injective
  apply embedMat2ToStage1_injective
  exact h

/-- The real Stiefel defect, represented as an element of the quotient
matrix-stage colimit. -/
def stiefelDefectInLimit (K L s : ℝ) : MatrixStageLimit :=
  canonicalStageHom 1 (realMat2ToStage1 (defectMatrix K L s))

/-- Faithful colimit trace detects vanishing of the embedded Stiefel defect,
which under the Stiefel constraint and nonzero scale is equivalent to zero
future leakage. This is a trace-kernel statement about the encoded defect; it
does not identify the generic Petz polynomial with the Stiefel reconstruction. -/
theorem stiefel_colimit_trace_defect_zero_iff (K L s : ℝ)
    (hSt : K ^ 2 + L ^ 2 = 1) (hs : s ≠ 0) :
    limitTrace (star (stiefelDefectInLimit K L s) *
      stiefelDefectInLimit K L s) = 0 ↔ L = 0 := by
  rw [limitTrace_star_mul_self_eq_zero_iff]
  constructor
  · intro h
    have hStage : realMat2ToStage1 (defectMatrix K L s) = 0 := by
      apply canonicalStageHom_injective 1
      simpa [stiefelDefectInLimit] using h
    have hDefect : defectMatrix K L s = 0 := by
      apply realMat2ToStage1_injective
      exact hStage
    apply (petz_stiefel_saturation_iff_zero_future K L s hSt hs).mp
    exact sub_eq_zero.mp hDefect
  · intro hL
    have hReconstruction : reconstructState K L s = compressedState s :=
      (petz_stiefel_saturation_iff_zero_future K L s hSt hs).mpr hL
    have hDefect : defectMatrix K L s = 0 := sub_eq_zero.mpr hReconstruction
    have hStage : realMat2ToStage1 (defectMatrix K L s) = 0 := by
      rw [hDefect]
      change embedMat2ToStage1 (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0
      ext v w
      simp [embedMat2ToStage1]
    have hLimit : stiefelDefectInLimit K L s = 0 := by
      change canonicalStageHom 1 (realMat2ToStage1 (defectMatrix K L s)) = 0
      rw [hStage]
      simp
    exact hLimit

/-- Causal pinching commutes with every finite stage map in the matrix tower. -/
theorem causalChannel_stageMorphism {m n : ℕ} (h : m ≤ n)
    (P X : Stage m) :
    stageMorphism m n h (causalChannel P X) =
      causalChannel (stageMorphism m n h P) (stageMorphism m n h X) := by
  exact map_causalChannel (stageMorphism m n h).toAlgHom.toRingHom P X

/-- The Petz polynomial commutes with every finite stage map in the matrix tower. -/
theorem petzRecoveryMap_stageMorphism {m n : ℕ} (h : m ≤ n)
    (P sigma sigmaInv omega : Stage m) :
    stageMorphism m n h (petzRecoveryMap P sigma sigmaInv omega) =
      petzRecoveryMap (stageMorphism m n h P) (stageMorphism m n h sigma)
        (stageMorphism m n h sigmaInv) (stageMorphism m n h omega) := by
  exact map_petzRecoveryMap (stageMorphism m n h).toAlgHom.toRingHom
    P sigma sigmaInv omega

/-- Pinching is compatible with the canonical inclusion into the quotient limit. -/
theorem causalChannel_canonicalStageHom (n : ℕ) (P X : Stage n) :
    canonicalStageHom n (causalChannel P X) =
      causalChannel (canonicalStageHom n P) (canonicalStageHom n X) := by
  exact map_causalChannel (canonicalStageHom n).toAlgHom.toRingHom P X

/-- The Petz polynomial is compatible with the canonical inclusion into the quotient limit. -/
theorem petzRecoveryMap_canonicalStageHom (n : ℕ)
    (P sigma sigmaInv omega : Stage n) :
    canonicalStageHom n (petzRecoveryMap P sigma sigmaInv omega) =
      petzRecoveryMap (canonicalStageHom n P) (canonicalStageHom n sigma)
        (canonicalStageHom n sigmaInv) (canonicalStageHom n omega) := by
  exact map_petzRecoveryMap (canonicalStageHom n).toAlgHom.toRingHom
    P sigma sigmaInv omega

/-- Pinching of independently staged representatives can be computed after
transporting both inputs to any common upper stage. -/
theorem causalChannel_mixedStage_readback
    {mP mX k : ℕ} (hP : mP ≤ k) (hX : mX ≤ k)
    (P : Stage mP) (X : Stage mX) :
    causalChannel (canonicalStageHom mP P) (canonicalStageHom mX X) =
      canonicalStageHom k
        (causalChannel (stageMorphism mP k hP P) (stageMorphism mX k hX X)) := by
  have hP' : canonicalStageHom k (stageMorphism mP k hP P) = canonicalStageHom mP P := by
    exact congrArg (fun f : Stage mP →⋆ₐ[ℂ] MatrixStageLimit => f P)
      (canonicalStageHom_comp hP)
  have hX' : canonicalStageHom k (stageMorphism mX k hX X) = canonicalStageHom mX X := by
    exact congrArg (fun f : Stage mX →⋆ₐ[ℂ] MatrixStageLimit => f X)
      (canonicalStageHom_comp hX)
  calc
    causalChannel (canonicalStageHom mP P) (canonicalStageHom mX X) =
        causalChannel (canonicalStageHom k (stageMorphism mP k hP P))
          (canonicalStageHom k (stageMorphism mX k hX X)) := by rw [← hP', ← hX']
    _ = canonicalStageHom k
        (causalChannel (stageMorphism mP k hP P) (stageMorphism mX k hX X)) :=
          (causalChannel_canonicalStageHom k _ _).symm

/-- Petz recovery of four independently staged representatives can be computed
after transporting all four inputs to any common upper stage. -/
theorem petzRecoveryMap_mixedStage_readback
    {mP mS mI mW k : ℕ}
    (hP : mP ≤ k) (hS : mS ≤ k) (hI : mI ≤ k) (hW : mW ≤ k)
    (P : Stage mP) (sigma : Stage mS) (sigmaInv : Stage mI) (omega : Stage mW) :
    petzRecoveryMap (canonicalStageHom mP P) (canonicalStageHom mS sigma)
        (canonicalStageHom mI sigmaInv) (canonicalStageHom mW omega) =
      canonicalStageHom k
        (petzRecoveryMap (stageMorphism mP k hP P) (stageMorphism mS k hS sigma)
          (stageMorphism mI k hI sigmaInv) (stageMorphism mW k hW omega)) := by
  have hP' : canonicalStageHom k (stageMorphism mP k hP P) = canonicalStageHom mP P := by
    exact congrArg (fun f : Stage mP →⋆ₐ[ℂ] MatrixStageLimit => f P)
      (canonicalStageHom_comp hP)
  have hS' : canonicalStageHom k (stageMorphism mS k hS sigma) = canonicalStageHom mS sigma := by
    exact congrArg (fun f : Stage mS →⋆ₐ[ℂ] MatrixStageLimit => f sigma)
      (canonicalStageHom_comp hS)
  have hI' : canonicalStageHom k (stageMorphism mI k hI sigmaInv) = canonicalStageHom mI sigmaInv := by
    exact congrArg (fun f : Stage mI →⋆ₐ[ℂ] MatrixStageLimit => f sigmaInv)
      (canonicalStageHom_comp hI)
  have hW' : canonicalStageHom k (stageMorphism mW k hW omega) = canonicalStageHom mW omega := by
    exact congrArg (fun f : Stage mW →⋆ₐ[ℂ] MatrixStageLimit => f omega)
      (canonicalStageHom_comp hW)
  calc
    petzRecoveryMap (canonicalStageHom mP P) (canonicalStageHom mS sigma)
        (canonicalStageHom mI sigmaInv) (canonicalStageHom mW omega) =
      petzRecoveryMap (canonicalStageHom k (stageMorphism mP k hP P))
        (canonicalStageHom k (stageMorphism mS k hS sigma))
        (canonicalStageHom k (stageMorphism mI k hI sigmaInv))
        (canonicalStageHom k (stageMorphism mW k hW omega)) := by
          rw [← hP', ← hS', ← hI', ← hW']
    _ = canonicalStageHom k
        (petzRecoveryMap (stageMorphism mP k hP P) (stageMorphism mS k hS sigma)
          (stageMorphism mI k hI sigmaInv) (stageMorphism mW k hW omega)) :=
            (petzRecoveryMap_canonicalStageHom k _ _ _ _).symm

/-- Master compilation conjunction for Petz recovery and causal pinching
compatibility with the matrix stage direct limit. -/
theorem compile_petz_matrix_stage_limit :
    (∀ {m n : ℕ} (h : m ≤ n) (P X : Stage m),
      stageMorphism m n h (causalChannel P X) =
        causalChannel (stageMorphism m n h P) (stageMorphism m n h X)) ∧
    (∀ {m n : ℕ} (h : m ≤ n) (P sigma sigmaInv omega : Stage m),
      stageMorphism m n h (petzRecoveryMap P sigma sigmaInv omega) =
        petzRecoveryMap (stageMorphism m n h P) (stageMorphism m n h sigma)
          (stageMorphism m n h sigmaInv) (stageMorphism m n h omega)) ∧
    (∀ (n : ℕ) (P X : Stage n),
      canonicalStageHom n (causalChannel P X) =
        causalChannel (canonicalStageHom n P) (canonicalStageHom n X)) ∧
    (∀ (n : ℕ) (P sigma sigmaInv omega : Stage n),
      canonicalStageHom n (petzRecoveryMap P sigma sigmaInv omega) =
        petzRecoveryMap (canonicalStageHom n P) (canonicalStageHom n sigma)
          (canonicalStageHom n sigmaInv) (canonicalStageHom n omega)) :=
  ⟨fun h P X => causalChannel_stageMorphism h P X,
   fun h P s si w => petzRecoveryMap_stageMorphism h P s si w,
   fun n P X => causalChannel_canonicalStageHom n P X,
   fun n P s si w => petzRecoveryMap_canonicalStageHom n P s si w⟩

end InfoGeometry.QuantumContext.PetzMatrixStageLimit


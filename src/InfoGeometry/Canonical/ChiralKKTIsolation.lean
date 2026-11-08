import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Arithmetic.PrimeMajoranaPfaffian

/-!
# InfoGeometry.Canonical.ChiralKKTIsolation

Owner-side closure theorem: the KKT wings isolate the chiral anomaly in the
grade-zero/orthogonal sector, with vanishing off-diagonal wing couplings.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.ChiralKKTIsolation

open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ConformalUnification

section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
KKT chiral isolation packet:
under KKT wing hypotheses, the chiral anomaly operator is grade-zero and
its mixed `(+,-)` / `(-,+)` components vanish.
-/
theorem chiralAnomaly_kkt_isolation_packet
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator ∧
    InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 ∧
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 ∧
    CI.chiralAnomalyOperator
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.minusProjector X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CI.chiralAnomalyOperator_isGZero_of_kkt_wings X hA hAMP hAD
  · exact CI.chiralAnomalyOperator_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings X hA hAMP hAD
  · exact CI.chiralAnomalyOperator_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings X hA hAMP hAD
  · exact CI.chiralAnomalyOperator_eq_diagonal_blocks_of_kkt_wings X hA hAMP hAD

/--
Any explicit polarized realization `χ = [u⁺(A), u⁻(B)]` is automatically in the
even (`g₀`) channel.
-/
theorem isGZero_of_eq_commutator_uPlus_uMinus
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B χ : E →L[ℝ] E)
    (hχ : χ = InfoGeometry.Canonical.KKTCore.commutator
      (InfoGeometry.Canonical.KKTCore.uPlus X A)
      (InfoGeometry.Canonical.KKTCore.uMinus X B)) :
    InfoGeometry.Canonical.KKTCore.IsGZero X χ := by
  rw [hχ]
  exact InfoGeometry.Canonical.KKTCore.commutator_uPlus_uMinus_isGZero (X := X) A B

/--
Specialized anomaly realization theorem:
if the chiral anomaly operator is realized as a polarized commutator, then it
is grade-zero.
-/
theorem chiralAnomalyOperator_isGZero_of_polarized_realization
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B : E →L[ℝ] E)
    (hreal : CI.chiralAnomalyOperator = InfoGeometry.Canonical.KKTCore.commutator
      (InfoGeometry.Canonical.KKTCore.uPlus X A)
      (InfoGeometry.Canonical.KKTCore.uMinus X B)) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator := by
  exact isGZero_of_eq_commutator_uPlus_uMinus (X := X) (A := A) (B := B)
    (χ := CI.chiralAnomalyOperator) hreal

/--
Any explicit polarized realization
`χ = u⁺(A)u⁻(B) + u⁻(B)u⁺(A)` is automatically in the even (`g₀`) channel.
-/
theorem isGZero_of_eq_anticommutator_uPlus_uMinus
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B χ : E →L[ℝ] E)
    (hχ : χ =
      InfoGeometry.Canonical.KKTCore.uPlus X A * InfoGeometry.Canonical.KKTCore.uMinus X B
        + InfoGeometry.Canonical.KKTCore.uMinus X B * InfoGeometry.Canonical.KKTCore.uPlus X A) :
    InfoGeometry.Canonical.KKTCore.IsGZero X χ := by
  rw [hχ]
  exact InfoGeometry.Canonical.KKTCore.anticommutator_uPlus_uMinus_isGZero (X := X) A B

/--
Polarized anticommutator realization implies explicit chiral block isolation:
off-diagonal KKT wings vanish and only diagonal blocks remain.
-/
theorem chiralAnomalyOperator_block_isolation_of_polarized_anticommutator_realization
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B : E →L[ℝ] E)
    (hreal : CI.chiralAnomalyOperator =
      InfoGeometry.Canonical.KKTCore.uPlus X A * InfoGeometry.Canonical.KKTCore.uMinus X B
        + InfoGeometry.Canonical.KKTCore.uMinus X B * InfoGeometry.Canonical.KKTCore.uPlus X A) :
    InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 ∧
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 ∧
    CI.chiralAnomalyOperator
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.minusProjector X := by
  have hG0 :
      InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator :=
    isGZero_of_eq_anticommutator_uPlus_uMinus
      (X := X) (A := A) (B := B) (χ := CI.chiralAnomalyOperator) hreal
  refine ⟨?_, ?_, ?_⟩
  · exact InfoGeometry.Canonical.KKTCore.plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0
  · exact InfoGeometry.Canonical.KKTCore.minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0
  · exact InfoGeometry.Canonical.KKTCore.eq_diagonal_blocks_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0

/--
Polarized realization implies explicit chiral block isolation:
off-diagonal KKT wings vanish and only diagonal blocks remain.
-/
theorem chiralAnomalyOperator_block_isolation_of_polarized_realization
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B : E →L[ℝ] E)
    (hreal : CI.chiralAnomalyOperator = InfoGeometry.Canonical.KKTCore.commutator
      (InfoGeometry.Canonical.KKTCore.uPlus X A)
      (InfoGeometry.Canonical.KKTCore.uMinus X B)) :
    InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 ∧
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 ∧
    CI.chiralAnomalyOperator
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.minusProjector X := by
  have hG0 :
      InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator :=
    chiralAnomalyOperator_isGZero_of_polarized_realization
      (CI := CI) (X := X) (A := A) (B := B) hreal
  refine ⟨?_, ?_, ?_⟩
  · exact InfoGeometry.Canonical.KKTCore.plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0
  · exact InfoGeometry.Canonical.KKTCore.minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0
  · exact InfoGeometry.Canonical.KKTCore.eq_diagonal_blocks_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0

/--
Unified polarized realization packet:
both commutator and anticommutator realizations force the same KKT block
isolation of the anomaly operator.
-/
theorem chiralAnomalyOperator_block_isolation_superpacket
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B : E →L[ℝ] E)
    (hcomm : CI.chiralAnomalyOperator = InfoGeometry.Canonical.KKTCore.commutator
      (InfoGeometry.Canonical.KKTCore.uPlus X A)
      (InfoGeometry.Canonical.KKTCore.uMinus X B))
    (hanti : CI.chiralAnomalyOperator =
      InfoGeometry.Canonical.KKTCore.uPlus X A * InfoGeometry.Canonical.KKTCore.uMinus X B
        + InfoGeometry.Canonical.KKTCore.uMinus X B * InfoGeometry.Canonical.KKTCore.uPlus X A) :
    (InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 ∧
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 ∧
    CI.chiralAnomalyOperator
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.minusProjector X)
    ∧
    (InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 ∧
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 ∧
    CI.chiralAnomalyOperator
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.minusProjector X) := by
  refine ⟨?_, ?_⟩
  ·
    have hG0 :
        InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator :=
      chiralAnomalyOperator_isGZero_of_polarized_realization
        (CI := CI) (X := X) (A := A) (B := B) hcomm
    refine ⟨?_, ?_, ?_⟩
    · exact InfoGeometry.Canonical.KKTCore.plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero
        (X := X) (A := CI.chiralAnomalyOperator) hG0
    · exact InfoGeometry.Canonical.KKTCore.minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero
        (X := X) (A := CI.chiralAnomalyOperator) hG0
    · exact InfoGeometry.Canonical.KKTCore.eq_diagonal_blocks_of_isGZero
        (X := X) (A := CI.chiralAnomalyOperator) hG0
  · exact chiralAnomalyOperator_block_isolation_of_polarized_anticommutator_realization
      (CI := CI) (X := X) (A := A) (B := B) hanti

/--
Converse bridge: if a chiral operator equals its KKT diagonal block sum, then
it is grade-zero.
-/
theorem isGZero_of_eq_diagonal_blocks
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (χ : E →L[ℝ] E)
    (hdiag : χ
      = InfoGeometry.Canonical.KKTCore.plusProjector X * χ
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * χ
          * InfoGeometry.Canonical.KKTCore.minusProjector X) :
    InfoGeometry.Canonical.KKTCore.IsGZero X χ := by
  change
    InfoGeometry.Canonical.KKTCore.plusProjector X * χ
        * InfoGeometry.Canonical.KKTCore.plusProjector X
      + InfoGeometry.Canonical.KKTCore.minusProjector X * χ
        * InfoGeometry.Canonical.KKTCore.minusProjector X
      = χ
  exact hdiag.symm

/--
Block-isolation packet (both off-diagonal zeros and diagonal decomposition)
implies grade-zero for the anomaly operator.
-/
theorem chiralAnomalyOperator_isGZero_of_block_isolation
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hpm : InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0)
    (hmp : InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0)
    (hdiag : CI.chiralAnomalyOperator
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
          * InfoGeometry.Canonical.KKTCore.minusProjector X) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator := by
  -- `hpm`/`hmp` are retained as explicit hypotheses in the packet; grade-zero
  -- follows from the diagonal decomposition equality itself.
  have _ := hpm
  have _ := hmp
  exact isGZero_of_eq_diagonal_blocks (X := X) (χ := CI.chiralAnomalyOperator) hdiag

/--
Grade-zero is equivalent to exact KKT diagonal-block decomposition.
-/
theorem isGZero_iff_eq_diagonal_blocks
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (χ : E →L[ℝ] E) :
    InfoGeometry.Canonical.KKTCore.IsGZero X χ ↔
      χ = InfoGeometry.Canonical.KKTCore.plusProjector X * χ
            * InfoGeometry.Canonical.KKTCore.plusProjector X
          + InfoGeometry.Canonical.KKTCore.minusProjector X * χ
            * InfoGeometry.Canonical.KKTCore.minusProjector X := by
  constructor
  · intro hG0
    exact InfoGeometry.Canonical.KKTCore.eq_diagonal_blocks_of_isGZero
      (X := X) (A := χ) hG0
  · intro hdiag
    exact isGZero_of_eq_diagonal_blocks (X := X) (χ := χ) hdiag

/--
Specialized anomaly equivalence: being grade-zero is exactly diagonal KKT
block isolation.
-/
theorem chiralAnomalyOperator_isGZero_iff_diagonal_blocks
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator ↔
      CI.chiralAnomalyOperator
        = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
            * InfoGeometry.Canonical.KKTCore.plusProjector X
          + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
            * InfoGeometry.Canonical.KKTCore.minusProjector X := by
  exact isGZero_iff_eq_diagonal_blocks (X := X) (χ := CI.chiralAnomalyOperator)

/--
Polarized commutator realization is equivalent to saying:
it is grade-zero and has vanishing off-diagonal KKT wings.
-/
theorem polarized_commutator_realization_implies_full_isolation
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B : E →L[ℝ] E)
    (hreal : CI.chiralAnomalyOperator = InfoGeometry.Canonical.KKTCore.commutator
      (InfoGeometry.Canonical.KKTCore.uPlus X A)
      (InfoGeometry.Canonical.KKTCore.uMinus X B)) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator ∧
    InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 ∧
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 := by
  have hG0 :
      InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator :=
    chiralAnomalyOperator_isGZero_of_polarized_realization
      (CI := CI) (X := X) (A := A) (B := B) hreal
  have hOff :=
    InfoGeometry.Canonical.KKTCore.plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0
  have hOff' :=
    InfoGeometry.Canonical.KKTCore.minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero
      (X := X) (A := CI.chiralAnomalyOperator) hG0
  exact ⟨hG0, hOff, hOff'⟩

/-- Finite zero-mode Pfaffian amplitude on the owner-side arithmetic carrier. -/
def zeroModePfaffianAmplitude
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) : ℝ :=
  InfoGeometry.Arithmetic.PrimeMajoranaPfaffian.blockPfaffian P q

/-- Determinant/volume shadow of the finite zero-mode block. -/
def zeroModeDeterminantShadow
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) : ℝ :=
  (zeroModePfaffianAmplitude P q) ^ 2

/--
Owner-side finite Pfaffian square law:
the zero-mode block Pfaffian amplitude squares to its determinant shadow.
-/
theorem zeroModePfaffian_square_eq_determinantShadow
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) :
    (zeroModePfaffianAmplitude P q) ^ 2 = zeroModeDeterminantShadow P q := by
  rfl

/--
Dirac/Pfaffian/zero-mode closure packet in the polarized KKT corridor:
if the anomaly operator is realized by the `u⁺/u⁻` commutator channel, then
the operator is grade-zero with vanishing off-diagonal wings, and the attached
finite zero-mode antisymmetric block carries a Pfaffian amplitude whose square
is the determinant shadow.
-/
theorem polarized_zeroMode_pfaffian_closure_packet
    (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (A B : E →L[ℝ] E)
    (hreal : CI.chiralAnomalyOperator = InfoGeometry.Canonical.KKTCore.commutator
      (InfoGeometry.Canonical.KKTCore.uPlus X A)
      (InfoGeometry.Canonical.KKTCore.uMinus X B))
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.chiralAnomalyOperator ∧
    InfoGeometry.Canonical.KKTCore.plusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 ∧
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.chiralAnomalyOperator
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 ∧
    (zeroModePfaffianAmplitude P q) ^ 2 = zeroModeDeterminantShadow P q := by
  rcases polarized_commutator_realization_implies_full_isolation
      (CI := CI) (X := X) (A := A) (B := B) hreal with ⟨hG0, hpm, hmp⟩
  exact ⟨hG0, hpm, hmp, zeroModePfaffian_square_eq_determinantShadow P q⟩

/-- Concrete triad relations used by the split-Clifford local model. -/
theorem triad_square_packet :
    InfoGeometry.Algebra.HypercomplexTriad.I * InfoGeometry.Algebra.HypercomplexTriad.I
      = -(1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) ∧
    InfoGeometry.Algebra.HypercomplexTriad.E * InfoGeometry.Algebra.HypercomplexTriad.E
      = (1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) ∧
    InfoGeometry.Algebra.HypercomplexTriad.N * InfoGeometry.Algebra.HypercomplexTriad.N
      = (0 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) := by
  exact ⟨InfoGeometry.Algebra.HypercomplexTriad.I_sq,
    InfoGeometry.Algebra.HypercomplexTriad.E_sq,
    InfoGeometry.Algebra.HypercomplexTriad.N_sq⟩

end

end InfoGeometry.Canonical.ChiralKKTIsolation

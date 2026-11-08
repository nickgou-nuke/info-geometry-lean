import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.ParaKahlerCantorBridge32
import InfoGeometry.Categorical.FiniteWordPathWeights
import InfoGeometry.Thermo.Gibbs
import InfoGeometry.Thermo.CantorGibbsModularBridge
import InfoGeometry.Canonical.CantorLocalCl11HopParity
import InfoGeometry.Canonical.CantorKMSState
import InfoGeometry.Canonical.CantorPlabicTwistorBridge
import InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
import InfoGeometry.Projective.MatrixPluckerPositiveBridge

open scoped BigOperators InnerProductSpace

/-!
# Cantor–Gibbs Partition-of-Unity Bridge

This module completes the architectural unification:

1. **FinitePoU** — the abstract finite partition of unity (resolution of identity) inducing a discrete PMF.
2. **Born-PoU on Cantor Cylinders** — the positive Grassmannian blade induces a probability measure supported on its six depth-5 Plücker cylinders.
3. **Gibbs-PoU on Cantor Cylinders** — the Born weights define an energy function whose Gibbs measure equals the Born measure.
4. **Twistor Covariance** — the Gibbs measure inherits GL(2) projective covariance from the Grassmannian chart.

The positroid decomposition and top-cell form are owned by the dedicated
`Gr(2,4)` topology modules; the finite Cantor channel layer here is kept
distinct from that geometry.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorGibbsPoUBridge

open InfoGeometry.Canonical.ParaKahlerCantorBridge32
open InfoGeometry.Categorical.FiniteWordPathWeights
open InfoGeometry.Thermo
open InfoGeometry.Thermo.CantorGibbsModularBridge
open InfoGeometry.Canonical.CantorLocalCl11HopParity
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorPlabicTwistorBridge
open InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-! ## 1. Abstract Finite Partition of Unity (PoU) -/

/-- A finite Partition of Unity on a type `α` is a family of non-negative reals summing to 1.
    This is the discrete analogue of a smooth partition of unity / resolution of identity. -/
structure FinitePoU (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  sum_one : ∑ a : α, weight a = 1

namespace FinitePoU

variable {α : Type*} [Fintype α] (pou : FinitePoU α)

/-- Every finite PoU canonically induces a discrete probability measure (PMF) on `α`. -/
def toPMF : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (pou.weight a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => pou.nonneg a), pou.sum_one]
    norm_num)

end FinitePoU

theorem FinitePoU.ext {α : Type*} [Fintype α] {p q : FinitePoU α}
    (h : ∀ a, p.weight a = q.weight a) : p = q := by
  cases p with
  | mk pw pn ps =>
    cases q with
    | mk qw qn qs =>
      have hfun : pw = qw := funext h
      subst qw
      rfl

/-! ## 2. Born-Rule PoU on Depth-5 Cantor Cylinders -/

/-- The normalized Cl(5,5) spinor state induces a FinitePoU on the 32 depth-5 Cantor cylinders
    via the Born rule: p(w) = |⟨w|ψ⟩|². -/
def spinorToCantorPoU (ψ : Word5 → ℂ)
    (h_norm : ∑ w : Word5, Complex.normSq (ψ w) = 1) :
    FinitePoU Word5 where
  weight w := Complex.normSq (ψ w)
  nonneg w := Complex.normSq_nonneg (ψ w)
  sum_one := by
    simpa [Complex.normSq] using h_norm

/-! The six active Plücker channels of a `Gr(2,4)` Cantor state.
    These are measurement outcomes, not positroid cells: a point with all six
    minors positive lies in the single full-support top positroid cell. -/
inductive PluckerChannelGr24 : Type where
  | channel01 : PluckerChannelGr24
  | channel02 : PluckerChannelGr24
  | channel03 : PluckerChannelGr24
  | channel12 : PluckerChannelGr24
  | channel13 : PluckerChannelGr24
  | channel23 : PluckerChannelGr24

def pluckerChannelIndex (c : PluckerChannelGr24) : Fin 6 :=
  match c with
  | PluckerChannelGr24.channel01 => 0
  | PluckerChannelGr24.channel02 => 1
  | PluckerChannelGr24.channel03 => 2
  | PluckerChannelGr24.channel12 => 3
  | PluckerChannelGr24.channel13 => 4
  | PluckerChannelGr24.channel23 => 5

/-! The positive Gr(2,4) blade induces a FinitePoU on the 32 depth-5 Cantor
    cylinders via the Born rule on its six active channels. -/
def grassmannianBornPoU (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4)) :
    FinitePoU Word5 :=
  { weight := fun w =>
      ∑ i : Fin 6, if pluckerAddress i = w then pluckerSectorProbability M i else 0
    nonneg := by
      intro w
      apply Finset.sum_nonneg
      intro i hi
      split_ifs
      · exact (pluckerSector_pou M hM).nonneg i
      · exact le_rfl
    sum_one := by
      classical
      unfold pluckerSectorProbability
      calc
        (∑ w : Word5, ∑ i : Fin 6,
            if pluckerAddress i = w then
              (matrixPluckerCoords M i) ^ 2 / pluckerSectorNormSq M else 0)
            = ∑ i : Fin 6, ∑ w : Word5,
                if pluckerAddress i = w then
                  (matrixPluckerCoords M i) ^ 2 / pluckerSectorNormSq M else 0 := by
                    rw [Finset.sum_comm]
        _ = ∑ i : Fin 6, pluckerSectorProbability M i := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_eq_single (pluckerAddress i)]
              · simp [pluckerSectorProbability]
              · intro w hw hwi
                have hne : pluckerAddress i ≠ w := Ne.symm hwi
                simp [hne]
              · intro h
                exact (h (Finset.mem_univ _)).elim
        _ = 1 := amplituhedronChannel_partition_sum M hM }

/-! Master Theorem 4A (Full Support): The Born measure has strictly positive weight
    on the 6 active Cantor cylinders for any strictly positive chart. -/
theorem grassmannianBornPoU_activeSupport
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4)) :
    ∀ i : Fin 6, 0 < (grassmannianBornPoU M hM).weight (pluckerAddress i) := by
  intro i
  have hweight : (grassmannianBornPoU M hM).weight (pluckerAddress i) =
      pluckerSectorProbability M i := by
    classical
    simp only [grassmannianBornPoU]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hne : pluckerAddress j ≠ pluckerAddress i := by
        intro h
        exact hji (pluckerAddress_injective h)
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [hweight]
  exact pluckerSectorProbability_pos M hM i

/-! ## 3. Gibbs Measure on Cantor Cylinder Weights -/

/-! The finite Gibbs law is normalized by its partition function. -/
def gibbsPartitionFunction {α : Type*} [Fintype α]
    (energy : α → ℝ) (ε : ℝ) : ℝ :=
  ∑ a : α, Real.exp (-energy a / ε)

lemma gibbsPartitionFunction_pos {α : Type*} [Fintype α] [Nonempty α]
    (energy : α → ℝ) (ε : ℝ) :
    0 < gibbsPartitionFunction energy ε := by
  classical
  unfold gibbsPartitionFunction
  apply Finset.sum_pos
  · intro a ha
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

noncomputable def finiteGibbsPoU {α : Type*} [Fintype α] [Nonempty α]
    (energy : α → ℝ) (ε : ℝ) : FinitePoU α where
  weight a := Real.exp (-energy a / ε) / gibbsPartitionFunction energy ε
  nonneg a := div_nonneg (le_of_lt (Real.exp_pos _))
    (le_of_lt (gibbsPartitionFunction_pos energy ε))
  sum_one := by
    unfold gibbsPartitionFunction
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (gibbsPartitionFunction_pos energy ε))

/-! Gibbs probabilities on the 32 depth-five Cantor addresses. -/
noncomputable def cantorGibbsMeasure (w : Word5 → ℝ) (ε : ℝ) :
    FinitePoU Word5 :=
  finiteGibbsPoU w ε

/-! ## 4. The Pushforward Theorem: Born PoU = Gibbs PoU -/

/- The inverse-temperature-scaled surprisal is the energy whose Gibbs law
recovers a strictly positive probability vector. -/
def pluckerSectorEnergy (M : Matrix2x4) (ε : ℝ) (i : Fin 6) : ℝ :=
  -ε * Real.log (pluckerSectorProbability M i)

theorem pluckerSectorEnergy_gibbs_numerator
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4))
    (ε : ℝ) (hε : 0 < ε) (i : Fin 6) :
    Real.exp (-pluckerSectorEnergy M ε i / ε) = pluckerSectorProbability M i := by
  rw [show -pluckerSectorEnergy M ε i / ε =
      Real.log (pluckerSectorProbability M i) by
        unfold pluckerSectorEnergy
        have hε0 : ε ≠ 0 := ne_of_gt hε
        field_simp]
  exact Real.exp_log (pluckerSectorProbability_pos M hM i)

noncomputable def pluckerSectorGibbsPoU (M : Matrix2x4)
    (_hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4))
    (ε : ℝ) : FinitePoU (Fin 6) :=
  finiteGibbsPoU (pluckerSectorEnergy M ε) ε

def pluckerSectorBornFinitePoU (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4)) :
    FinitePoU (Fin 6) where
  weight := pluckerSectorProbability M
  nonneg i := le_of_lt (pluckerSectorProbability_pos M hM i)
  sum_one := amplituhedronChannel_partition_sum M hM

theorem pluckerSectorGibbsPoU_eq_born (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4))
    (ε : ℝ) (hε : 0 < ε) :
    pluckerSectorGibbsPoU M hM ε = pluckerSectorBornFinitePoU M hM := by
  have hnum (i : Fin 6) := pluckerSectorEnergy_gibbs_numerator M hM ε hε i
  have hZ : gibbsPartitionFunction (pluckerSectorEnergy M ε) ε = 1 := by
    unfold gibbsPartitionFunction
    simp_rw [hnum]
    exact amplituhedronChannel_partition_sum M hM
  apply FinitePoU.ext
  intro i
  change Real.exp (-pluckerSectorEnergy M ε i / ε) /
      gibbsPartitionFunction (pluckerSectorEnergy M ε) ε =
    pluckerSectorProbability M i
  rw [hnum i, hZ, div_one]

theorem pluckerSectorGibbsPMF_eq_born (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4))
    (ε : ℝ) (hε : 0 < ε) :
    (pluckerSectorGibbsPoU M hM ε).toPMF = pluckerSectorPMF M hM := by
  rw [pluckerSectorGibbsPoU_eq_born M hM ε hε]
  apply PMF.ext
  intro i
  change ENNReal.ofReal (pluckerSectorProbability M i) =
    ENNReal.ofReal ((pluckerSector_pou M hM).weight i)
  congr 1

theorem bornEqualsGibbsOnCantor
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4))
    (ε : ℝ) (hε : ε > 0) :
    (pluckerSectorGibbsPoU M hM ε).toPMF.map pluckerAddress =
      pluckerAddressPMF M hM := by
  rw [pluckerSectorGibbsPMF_eq_born M hM ε hε]
  rfl

/-! ## 5. Twistor Covariance of the Gibbs Measure -/

/-- The Gibbs measure is projective GL(2) invariant on the Cantor weights,
    inherited from the Plücker covariance of the Grassmannian chart. -/
theorem gibbsMeasure_gl2_invariant
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4))
    (M2 : Matrix (Fin 2) (Fin 2) ℝ)
    (h_det : Matrix.det M2 ≠ 0)
    (ε : ℝ) (_hε : ε > 0)
    (hM2 : M2 * M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4)) :
    (cantorGibbsMeasure (fun w => -Real.log ((grassmannianBornPoU (M2 * M) hM2).weight w)) ε).toPMF =
    (cantorGibbsMeasure (fun w => -Real.log ((grassmannianBornPoU M hM).weight w)) ε).toPMF := by
  have hweight (w : Word5) :
      (grassmannianBornPoU (M2 * M) hM2).weight w =
        (grassmannianBornPoU M hM).weight w := by
    classical
    simp only [grassmannianBornPoU]
    rw [Finset.sum_congr rfl]
    intro i hi
    by_cases haddr : pluckerAddress i = w
    · simp [haddr, pluckerSectorProbability_row_basis_invariant M2 M
        (by simpa [detTwo] using h_det) hM i]
    · simp [haddr]
  have henergy :
      (fun w => -Real.log ((grassmannianBornPoU (M2 * M) hM2).weight w)) =
      (fun w => -Real.log ((grassmannianBornPoU M hM).weight w)) := by
    funext w
    rw [hweight w]
  rw [henergy]

end InfoGeometry.Canonical.CantorGibbsPoUBridge

end noncomputable section

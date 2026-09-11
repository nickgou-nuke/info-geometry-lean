/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.CircularChiralCarrierReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge

/-!
# Span bridge for the circular chiral gauge witnesses

The carrier readouts and the standard-column root readouts are combined here.
This proves membership in the canonical root span for every witness, without
claiming that the witness family itself spans until the converse inclusion is
proved.
-/

namespace InfoGeometry.Algebra.ChiralGaugeRootSpanBridge

open InfoGeometry.Algebra.CircularChiralCarrierReadout
open InfoGeometry.Algebra.CircularChiralDerivationsFourteen
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge

private abbrev RootSpan : Submodule ℝ Der :=
  Submodule.span ℝ (Set.range rootDerivation)

private abbrev WitnessSpan : Submodule ℝ Der :=
  Submodule.span ℝ (Set.range (fun g : GaugeGenerator =>
    vectorCanonicalLinearEquiv (gaugeWitnessNativeDerivation g)))

private theorem root_mem (i : Fin 14) : rootDerivation i ∈ RootSpan :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem root_mem_of_smul_mem {c : ℝ} {i : Fin 14}
    (hc : c ≠ 0) (h : c • rootDerivation i ∈ WitnessSpan) :
    rootDerivation i ∈ WitnessSpan := by
  have hscaled := WitnessSpan.smul_mem c⁻¹ h
  simpa [smul_smul, hc] using hscaled

theorem chiral_witness_mem_root_span (g : GaugeGenerator) :
    vectorCanonicalLinearEquiv (gaugeWitnessNativeDerivation g) ∈ RootSpan := by
  fin_cases g
  · rw [gaugeWitnessNativeDerivation_cartan0_canonical_readout,
      standardColumn_U0_V0_root]
    exact RootSpan.add_mem (root_mem 6) (root_mem 13)
  · rw [gaugeWitnessNativeDerivation_cartan1_canonical_readout,
      standardColumn_U1_V1_root]
    exact RootSpan.add_mem (RootSpan.smul_mem _ (root_mem 6)) (root_mem 13)
  · rw [gaugeWitnessNativeDerivation_gluon01_canonical_readout,
      standardColumn_U0_V1_root]
    exact RootSpan.smul_mem _ (root_mem 5)
  · rw [gaugeWitnessNativeDerivation_gluon02_canonical_readout,
      standardColumn_U0_V2_root]
    exact RootSpan.smul_mem _ (root_mem 11)
  · rw [gaugeWitnessNativeDerivation_gluon10_canonical_readout,
      standardColumn_U1_V0_root]
    exact RootSpan.smul_mem _ (root_mem 1)
  · rw [gaugeWitnessNativeDerivation_gluon12_canonical_readout,
      standardColumn_U1_V2_root]
    exact RootSpan.smul_mem _ (root_mem 12)
  · rw [gaugeWitnessNativeDerivation_gluon20_canonical_readout,
      standardColumn_U2_V0_root]
    exact RootSpan.smul_mem _ (root_mem 2)
  · rw [gaugeWitnessNativeDerivation_gluon21_canonical_readout,
      standardColumn_U2_V1_root]
    exact RootSpan.smul_mem _ (root_mem 7)
  · rw [gaugeWitnessNativeDerivation_quarkUp0_canonical_readout,
      standardColumn_E11_U0_root]
    exact RootSpan.smul_mem _ (root_mem 10)
  · rw [gaugeWitnessNativeDerivation_quarkUp1_canonical_readout,
      standardColumn_E11_U1_root]
    exact root_mem 9
  · rw [gaugeWitnessNativeDerivation_quarkUp2_canonical_readout,
      standardColumn_E11_U2_root]
    exact RootSpan.smul_mem _ (root_mem 4)
  · rw [gaugeWitnessNativeDerivation_quarkDown0_canonical_readout,
      standardColumn_E11_V0_root]
    exact root_mem 0
  · rw [gaugeWitnessNativeDerivation_quarkDown1_canonical_readout,
      standardColumn_E11_V1_root]
    exact root_mem 3
  · rw [gaugeWitnessNativeDerivation_quarkDown2_canonical_readout,
      standardColumn_E11_V2_root]
    exact root_mem 8

theorem chiral_witnesses_span_le_root_span :
    Submodule.span ℝ
        (Set.range (fun g : GaugeGenerator =>
          vectorCanonicalLinearEquiv (gaugeWitnessNativeDerivation g))) ≤
      RootSpan := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, rfl⟩
  exact chiral_witness_mem_root_span g

theorem root_zero_mem_chiral_witness_span : rootDerivation 0 ∈ WitnessSpan := by
  rw [← standardColumn_E11_V0_root,
    ← gaugeWitnessNativeDerivation_quarkDown0_canonical_readout]
  exact Submodule.subset_span ⟨GaugeGenerator.quarkDown0, rfl⟩

theorem root_three_mem_chiral_witness_span : rootDerivation 3 ∈ WitnessSpan := by
  rw [← standardColumn_E11_V1_root,
    ← gaugeWitnessNativeDerivation_quarkDown1_canonical_readout]
  exact Submodule.subset_span ⟨GaugeGenerator.quarkDown1, rfl⟩

theorem root_eight_mem_chiral_witness_span : rootDerivation 8 ∈ WitnessSpan := by
  rw [← standardColumn_E11_V2_root,
    ← gaugeWitnessNativeDerivation_quarkDown2_canonical_readout]
  exact Submodule.subset_span ⟨GaugeGenerator.quarkDown2, rfl⟩

theorem root_five_mem_chiral_witness_span : rootDerivation 5 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_gluon01_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.gluon01, rfl⟩
  rw [standardColumn_U0_V1_root] at hw
  have hscaled := WitnessSpan.smul_mem (-1 / 3 : ℝ) hw
  simpa [smul_smul] using hscaled

theorem root_eleven_mem_chiral_witness_span : rootDerivation 11 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 2) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_gluon02_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.gluon02, rfl⟩
  rw [standardColumn_U0_V2_root] at hw
  exact root_mem_of_smul_mem (by norm_num) hw

theorem root_one_mem_chiral_witness_span : rootDerivation 1 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_gluon10_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.gluon10, rfl⟩
  rw [standardColumn_U1_V0_root] at hw
  exact root_mem_of_smul_mem (by norm_num) hw

theorem root_twelve_mem_chiral_witness_span : rootDerivation 12 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 2) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_gluon12_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.gluon12, rfl⟩
  rw [standardColumn_U1_V2_root] at hw
  exact root_mem_of_smul_mem (by norm_num) hw

theorem root_two_mem_chiral_witness_span : rootDerivation 2 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_gluon20_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.gluon20, rfl⟩
  rw [standardColumn_U2_V0_root] at hw
  exact root_mem_of_smul_mem (by norm_num) hw

theorem root_seven_mem_chiral_witness_span : rootDerivation 7 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_gluon21_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.gluon21, rfl⟩
  rw [standardColumn_U2_V1_root] at hw
  exact root_mem_of_smul_mem (by norm_num) hw

theorem root_four_mem_chiral_witness_span : rootDerivation 4 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 2) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_quarkUp2_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.quarkUp2, rfl⟩
  rw [standardColumn_E11_U2_root] at hw
  exact root_mem_of_smul_mem (by norm_num) hw

theorem root_ten_mem_chiral_witness_span : rootDerivation 10 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_quarkUp0_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.quarkUp0, rfl⟩
  rw [standardColumn_E11_U0_root] at hw
  exact root_mem_of_smul_mem (by norm_num) hw

theorem root_nine_mem_chiral_witness_span : rootDerivation 9 ∈ WitnessSpan := by
  have hw :
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 1) ∈
        WitnessSpan := by
    rw [← gaugeWitnessNativeDerivation_quarkUp1_canonical_readout]
    exact Submodule.subset_span ⟨GaugeGenerator.quarkUp1, rfl⟩
  rw [standardColumn_E11_U1_root] at hw
  exact hw

theorem root_six_mem_chiral_witness_span : rootDerivation 6 ∈ WitnessSpan := by
  have h0 : rootDerivation 6 + rootDerivation 13 ∈ WitnessSpan := by
    have hw :
        canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0) ∈
          WitnessSpan := by
      rw [← gaugeWitnessNativeDerivation_cartan0_canonical_readout]
      exact Submodule.subset_span ⟨GaugeGenerator.cartan0, rfl⟩
    rw [standardColumn_U0_V0_root] at hw
    exact hw
  have h1 : (-2 : ℝ) • rootDerivation 6 + rootDerivation 13 ∈ WitnessSpan := by
    have hw :
        canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1) ∈
          WitnessSpan := by
      rw [← gaugeWitnessNativeDerivation_cartan1_canonical_readout]
      exact Submodule.subset_span ⟨GaugeGenerator.cartan1, rfl⟩
    rw [standardColumn_U1_V1_root] at hw
    exact hw
  have hd := WitnessSpan.sub_mem h1 h0
  have hdiff : (-2 : ℝ) • rootDerivation 6 + rootDerivation 13 - (rootDerivation 6 + rootDerivation 13) = (-3 : ℝ) • rootDerivation 6 := by
    module
  rw [hdiff] at hd
  exact root_mem_of_smul_mem (by norm_num) hd

theorem root_thirteen_mem_chiral_witness_span : rootDerivation 13 ∈ WitnessSpan := by
  have h0 : rootDerivation 6 + rootDerivation 13 ∈ WitnessSpan := by
    have hw :
        canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0) ∈
          WitnessSpan := by
      rw [← gaugeWitnessNativeDerivation_cartan0_canonical_readout]
      exact Submodule.subset_span ⟨GaugeGenerator.cartan0, rfl⟩
    rw [standardColumn_U0_V0_root] at hw
    exact hw
  have h6 : rootDerivation 6 ∈ WitnessSpan := root_six_mem_chiral_witness_span
  have h := WitnessSpan.sub_mem h0 h6
  have hdiff : rootDerivation 6 + rootDerivation 13 - rootDerivation 6 = rootDerivation 13 := by
    module
  rw [hdiff] at h
  exact h

end InfoGeometry.Algebra.ChiralGaugeRootSpanBridge

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinExistenceBridge
import InfoGeometry.Canonical.DrazinJordanChevalleyBridge
import InfoGeometry.Canonical.DrazinSpectralFittingBridge
import InfoGeometry.Canonical.DrazinCommutant
import InfoGeometry.Canonical.RoseDrazinPolynomial
import InfoGeometry.Canonical.GrevilleSouriauFrameDrazin
import InfoGeometry.Canonical.DiracKahlerDrazinPropagatorBridge
import InfoGeometry.Canonical.HodgeStarOperatorDrazinBridge
import InfoGeometry.Canonical.DrazinPeirceParity
import InfoGeometry.Canonical.DrazinMPCartan
import InfoGeometry.Canonical.DrazinMoorePenrosePartition
import InfoGeometry.Canonical.GradedDMPResolution
import InfoGeometry.Canonical.GradedDMPDependencyOrder
import InfoGeometry.Canonical.CampbellMeyerWeakDrazin
import InfoGeometry.Canonical.MoorePenroseDrazinObstruction
import InfoGeometry.Canonical.MoorePenroseDrazinCriterion
import InfoGeometry.Canonical.DrazinShellCascade
import InfoGeometry.Canonical.DrazinShellPeirce
import InfoGeometry.QuantumContext.RectangularPeirceDrazin
import InfoGeometry.QuantumContext.GradedDMPTransport
import InfoGeometry.QuantumContext.MarkovDrazinSemisimplicity
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse
import InfoGeometry.HodgeCohomology.KreinDrazinGreen
import InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect
import InfoGeometry.GromovWittenErlangen.DrazinLocalization
import InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification
import InfoGeometry.OperatorAlgebra.OntologyRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis

/-!
# Epistemic Compilation (`Solve et Coagula`) & Ontology Unification of the Drazin Species

This module relates Drazin declarations across the `Canonical`, `Singular`, `QuantumContext`,
`Core`, and `OperatorAlgebra.PeirceSpine` lanes (by the explicit iff/`rfl` bridges listed
below; other lanes, e.g. `Algebraic.DrazinSurgery`, are not bridged here) over an arbitrary associative unital ring `[Ring R]`
(and `[StarRing R]` where involutions or Moore–Penrose shells are invoked), without wrapper
structures, proof sockets, or commutative surrogates:

0. **Stage 0 — Cross-Lane Ontology Unification & Definitional Deduplication**:
   - Unifies the three indexed Drazin inverse predicates in the repository:
     `InfoGeometry.QuantumContext.Drazin.IsDrazinInverse a b k ↔ InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k`
     (`quantumContext_iff_canonical_drazin`) and
     `InfoGeometry.Singular.Drazin.IsDrazinInverse a b k ↔ InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k`
     (`singular_iff_canonical_drazin`).
   - Unifies the duplicate projector, Fitting/Jordan–Chevalley, Peirce-block, Cartan-grade,
     and Malik–Thome `DMP`/`MPD` declarations across lanes by definitional/equational identity:
     `spectralProj = projection`, `kernelProj = complementaryProjection`,
     `a_semisimple = fittingRegularPart`, `a_nilpotent = fittingNilpotentPart`,
     `component11 = peirce11`, `component10 = conePlus`, `component01 = coneMinus`,
     `component00 = peirce00`, `evenPart = evenGrade`, `oddPart = oddGrade`,
     `dmpInverse a b m = dmpOp (projection a b) m`, and
     `dualDmpInverse a b m = mpdOp (projection a b) m`.

1. **Movement I — Primordial Dual/Triple Roots, Clabject Individuation, & Binary Cut (`C1`–`C3`)**:
   - Reuses `DrazinExistenceBridge`, `GradedDMPTransport`, `DrazinPeirceParity`,
     `DrazinJordanChevalleyBridge`, `DrazinSpectralFittingBridge`, `CladisticPhylogenesisBridge`,
     `OperatorSurgery`, and `OntologyRing` to establish:
     - 3-way equivalence of `QuantumContext`, `Singular`, and `Canonical` Drazin predicates,
     - `cladeJoin P_D Q_D = 1`, `cladeFork P_D Q_D = invS P_D`, and unique fixed-point clabject
       decomposition (`drazin_unique_clabject_fixed_point_decomposition` via
       `drazin_core_null_unique_projector_decomposition`),
     - Purely even Peirce parity of `a`, `b`, and `fittingNilpotentPart a b` (`operator_even`,
       `operator_odd_zero`, `inverse_even`, `inverse_odd_zero`),
     - Jordan–Chevalley / Fitting split `a = fittingRegularPart a b + fittingNilpotentPart a b`
       with unique Fitting module decomposition (`fitting_decomposition_unique`,
       `drazin_fitting_trivial_intersection`).

2. **Movement II — The Fourfold Non-Commutative Relational Anatomy (`C4`)**:
   - Reuses `EpistemicCompilerPeirceBridge` and `DrazinMPCartan` to isolate the fourfold Peirce
     sectors (`peirce11`, `conePlus`, `coneMinus`, `peirce00`), square-zero off-diagonal cones,
     and faithful `2 × 2` coordinate representation `peirceCoordinateRingHom`.

3. **Movement III — Malik–Thome `DMP`/`MPD` Pairing and Inner-Inverse Sandwich (`C5`)**:
   - Reuses `DrazinMoorePenrosePartition`, `GradedDMPResolution`, `GradedDMPDependencyOrder`,
     `CyclotomicGaloisNilpotentSylvesterSynthesis`, and `EpistemicCompilerPeirceBridge` to connect
     the canonical `dmpInverse`/`dualDmpInverse` lane (`dmp_sandwich`, `dmp_difference`,
     `dmp_eq_dual_iff_odd_zero`, `dmp_inner_iff_nilpotent_part_zero`) with the universal inner-inverse
     sandwich collapse (`projection a b * m_dag * projection a b = b`), directional tension `J`,
     integrative bridge `Φ`, round-trip Gramians `qgtPlus`/`qgtMinus`, substantive gravity `V`,
     perspectival curvature `Σ`, and split-quaternion Tetraktys closure.

4. **Movement IV — Socratic Aporia, Moore–Penrose Obstruction & Criterion, Shell Cascade, & Meta-Cognitive Tower (`C6`–`C9`)**:
   - Reuses `EpistemicCompilerPeirceBridge`, `OntologyRing`, `MoorePenroseDrazinObstruction`,
     `MoorePenroseDrazinCriterion`, `DrazinShellCascade`, and `DrazinShellPeirce` to establish
     orthogonal Fitting additivity of `idempotencyDefect`, coupled thesis aporia, recursive
     defect tower splitting, superoperator group-inverse closure `peirceAdCube = peirceAd`,
     Grassmannian tangent equivalence, the MP-vs-Drazin nilpotent obstruction
     (`nilpotent_moore_penrose_not_drazin`) and EP commutation criterion (`exists_index_iff_commute`),
     and the strictly triangular nilpotent shell cascade (`drazin_core_and_shell_cascade`,
     `full_operator_triangular_peirce_reconstruction`).

5. **Movement V — Acyclic Causal Posets, Cline Shift, All-Degree Polynomial Drazin, Bicommutant Closure, Kemeny–Snell Markov Group Drazin, Krein Self-Adjoint Green, & Master Synthesis (`C10`–`C11`)**:
   - Orders the six epistemic stages into the strictly acyclic poset `DrazinEpistemicStage` alongside
     the diamond poset `GradedDMPDependencyOrder.Stage`, the 4-stratum multi-level ontology
     `OntologyMetaLevel`, rectangular Peirce–Drazin retracts (`isDrazinInverse_of_retract`,
     `mp_isometric_corner`, `lifted_recovery`), and Erlangen 2.0 `RingEquiv` transport.
   - Integrates bicommutant closure (`inverse_commutes_of_commutes`, `projection_commutes_of_commutes`),
     Clade 0 wild nilpotent perturbations (`weakWildInverse_ne_Drazin`), the all-degree polynomial
     Drazin construction (`isDrazinInverse_polynomialDrazinCandidate`), Cline's non-commutative
     Drazin shift (`isDrazinInverse_clineDrazinShift`), the Kemeny–Snell stationary-projector
     Markov group Drazin construction (`isDrazinInverse_kemenySnellDeviation`,
     `exists_stochastic_laplacian_groupInverse`), and Krein self-adjoint Green operator & projector
     inheritance (`green_krein_adjoint`, `regular_projector_krein_adjoint`,
     `complementary_projector_krein_adjoint`) in `drazin_cline_polynomial_bicommutant_markov_krein_synthesis`.
-/

namespace InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula

open scoped BigOperators
open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinExistenceBridge
open InfoGeometry.Canonical.DrazinJordanChevalleyBridge
open InfoGeometry.Canonical.DrazinSpectralFittingBridge
open InfoGeometry.Canonical.DrazinPeirceParity
open InfoGeometry.Canonical.DrazinMPCartan
open InfoGeometry.Canonical.DrazinMoorePenrosePartition
open InfoGeometry.Canonical.GradedDMPResolution
open InfoGeometry.Canonical.GradedDMPDependencyOrder
open InfoGeometry.Canonical.CampbellMeyerWeakDrazin
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.MoorePenroseDrazinObstruction
open InfoGeometry.Canonical.MoorePenroseDrazinCriterion
open InfoGeometry.Canonical.DrazinNilpotentShell
open InfoGeometry.Canonical.DrazinShellPeirce
open InfoGeometry.QuantumContext.RectangularPeirceDrazin
open InfoGeometry.QuantumContext.GradedDMPTransport

variable {R : Type*} [Ring R]

/-!
## Stage 0: Cross-Lane Ontology Unification & Definitional Bridges
-/

/-- Reverse adapter from `Canonical.Drazin.IsDrazinInverse` to
`QuantumContext.Drazin.IsDrazinInverse`, complementing `GradedDMPTransport.toCanonical`. -/
theorem ofCanonical {a b : R} {k : ℕ}
    (h : InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k) :
    InfoGeometry.QuantumContext.Drazin.IsDrazinInverse a b k :=
  ⟨h.idempotent, h.comm, h.power⟩

/-- **Claim C1a (`quantumContext_iff_canonical_drazin`)**:
Exact bidirectional equivalence between the `QuantumContext` and `Canonical` Drazin predicates. -/
theorem quantumContext_iff_canonical_drazin (a b : R) (k : ℕ) :
    InfoGeometry.QuantumContext.Drazin.IsDrazinInverse a b k ↔
      InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k :=
  ⟨toCanonical, ofCanonical⟩

/-- **Claim C1b (`singular_iff_canonical_drazin`)**:
Exact bidirectional equivalence between the `Singular` and `Canonical` Drazin predicates. -/
theorem singular_iff_canonical_drazin (a b : R) (k : ℕ) :
    InfoGeometry.Singular.Drazin.IsDrazinInverse a b k ↔
      InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k :=
  ⟨canonical_isDrazinInverse_of_singular, singular_isDrazinInverse_of_canonical⟩

/-- **Claim C1c (`singular_iff_quantumContext_drazin`)**:
Exact bidirectional equivalence between the `Singular` and `QuantumContext` Drazin predicates. -/
theorem singular_iff_quantumContext_drazin (a b : R) (k : ℕ) :
    InfoGeometry.Singular.Drazin.IsDrazinInverse a b k ↔
      InfoGeometry.QuantumContext.Drazin.IsDrazinInverse a b k :=
  (singular_iff_canonical_drazin a b k).trans (quantumContext_iff_canonical_drazin a b k).symm

/-- Definitional unification of `QuantumContext.Drazin.spectralProj` and `Canonical` `projection`. -/
@[simp] theorem spectralProj_eq_projection (a b : R) :
    InfoGeometry.QuantumContext.Drazin.spectralProj a b = projection a b := rfl

/-- Definitional unification of `QuantumContext.Drazin.kernelProj` and `complementaryProjection`. -/
@[simp] theorem kernelProj_eq_complementaryProjection (a b : R) :
    InfoGeometry.QuantumContext.Drazin.kernelProj a b = complementaryProjection a b := rfl

/-- Definitional unification of `DrazinJordanChevalleyBridge.a_semisimple` and `fittingRegularPart`. -/
@[simp] theorem a_semisimple_eq_fittingRegularPart (a b : R) :
    a_semisimple a b = fittingRegularPart a b := rfl

/-- Definitional unification of `DrazinJordanChevalleyBridge.a_nilpotent` and `fittingNilpotentPart`. -/
@[simp] theorem a_nilpotent_eq_fittingNilpotentPart (a b : R) :
    a_nilpotent a b = fittingNilpotentPart a b := rfl

/-- Definitional unification of `Core.PeirceDecomposition` blocks with `PeirceSpine` blocks. -/
theorem core_peirce_blocks_eq_peirceSpine (P X : R) :
    InfoGeometry.Core.PeirceDecomposition.component11 P X =
      InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P X ∧
    InfoGeometry.Core.PeirceDecomposition.component10 P X = conePlus P X ∧
    InfoGeometry.Core.PeirceDecomposition.component01 P X = coneMinus P X ∧
    InfoGeometry.Core.PeirceDecomposition.component00 P X =
      InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 P X ∧
    evenPart P X = evenGrade P X ∧
    oddPart P X = oddGrade P X :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Equational unification of `Canonical.DrazinMoorePenrosePartition` (`dmpInverse`, `dualDmpInverse`)
with `PeirceSpine` (`dmpOp`, `mpdOp`). -/
theorem canonical_dmp_eq_peirceSpine_dmpOp {a b : R} {k : ℕ}
    (h : IsDrazinInverse a b k) (m : R) :
    dmpInverse a b m = dmpOp (projection a b) m ∧
    dualDmpInverse a b m = mpdOp (projection a b) m :=
  ⟨dmp_eq_projection_mul h, dualDmp_eq_mul_projection a b m⟩

private theorem defect_add_of_ortho {x y : R} (hxy : x * y = 0) (hyx : y * x = 0) :
    idempotencyDefect (x + y) = idempotencyDefect x + idempotencyDefect y := by
  unfold idempotencyDefect
  calc
    (x + y) * (x + y) - (x + y)
        = (x * x - x) + (y * y - y) + x * y + y * x := by noncomm_ring
    _ = (x * x - x) + (y * y - y) := by rw [hxy, hyx, add_zero, add_zero]

private theorem qgtMinus_compress_idempotent (P m_dag : R) :
    (1 - P) * (mpdOp P m_dag * dmpOp P m_dag) * (1 - P) = qgtMinus P m_dag m_dag := by
  unfold mpdOp dmpOp qgtMinus coneMinus conePlus
  noncomm_ring

/-!
## Movement I: Primordial Dual/Triple Roots, Clabject Individuation, & Binary Cut (`C1`–`C3`)
-/

/-- The Drazin core projector `P_D = projection a b` passes through `b` on both sides. -/
theorem projection_mul_drazin_self {a b : R} {k : ℕ} (h : IsDrazinInverse a b k) :
    projection a b * b = b ∧ b * projection a b = b := by
  constructor
  · unfold projection
    rw [h.comm, h.idempotent]
  · unfold projection
    rw [← mul_assoc, h.idempotent]

/-- The complementary shadow projector `Q_D = 1 - a * b` annihilates `b` on both sides. -/
theorem complementaryProjection_mul_drazin_zero {a b : R} {k : ℕ} (h : IsDrazinInverse a b k) :
    complementaryProjection a b * b = 0 ∧ b * complementaryProjection a b = 0 := by
  rcases projection_mul_drazin_self h with ⟨hL, hR⟩
  exact ⟨by unfold complementaryProjection; rw [sub_mul, one_mul, hL, sub_self],
         by unfold complementaryProjection; rw [mul_sub, mul_one, hR, sub_self]⟩

/-- **Claim C3 (`drazin_unique_clabject_fixed_point_decomposition`)**:
Every element `x : R` decomposes uniquely into a conscious fixed point of `projection a b`
and a repressed shadow fixed point of `complementaryProjection a b`, reusing
`OntologyRing.drazin_core_null_unique_projector_decomposition`. -/
theorem drazin_unique_clabject_fixed_point_decomposition
    {a b : R} {k : ℕ} (h : IsDrazinInverse a b k) (x : R) :
    ∃! parts : R × R,
      parts.1 ∈ projectorSubspace (projection a b) ∧
      parts.2 ∈ projectorSubspace (complementaryProjection a b) ∧
      parts.1 + parts.2 = x :=
  drazin_core_null_unique_projector_decomposition
    ⟨b, k, singular_isDrazinInverse_of_canonical h⟩ x

/-- **Movement I (`drazin_primordial_dual_roots_and_binary_cut`, `C1`–`C3`)**:
Reuses `DrazinPeirceParity`, `DrazinJordanChevalleyBridge`, `CladisticPhylogenesisBridge`,
and `OntologyRing` to establish:
1. `cladeJoin P_D Q_D = 1`, `cladeFork P_D Q_D = invS P_D`, and `cladeFork P_D Q_D ^ 2 = 1`,
2. Synapomorphic polarity `+1` on `projectorSubspace P_D`, `-1` on `projectorSubspace Q_D`, and
   unique clabject fixed-point decomposition for every `z : R`,
3. Purely even Peirce grading of `a`, `b`, and `fittingNilpotentPart a b`
   (`operator_even`, `operator_odd_zero`, `inverse_even`, `inverse_odd_zero`),
4. Exact Jordan–Chevalley / Fitting split (`jordan_chevalley_sum`, `a_semisimple_mul_drazin`,
   `drazin_mul_a_semisimple`, `a_semisimple_mul_a_nilpotent`, `a_nilpotent_mul_a_semisimple`,
   `fittingNilpotentPart_pow_succ_eq_zero`). -/
theorem drazin_primordial_dual_roots_and_binary_cut
    {a b : R} {k : ℕ} (h : IsDrazinInverse a b k) :
    (cladeJoin (projection a b) (complementaryProjection a b) = 1 ∧
     cladeFork (projection a b) (complementaryProjection a b) = invS (projection a b) ∧
     cladeFork (projection a b) (complementaryProjection a b) *
       cladeFork (projection a b) (complementaryProjection a b) = 1) ∧
    ((∀ x ∈ projectorSubspace (projection a b),
        cladeFork (projection a b) (complementaryProjection a b) * x = x) ∧
     (∀ y ∈ projectorSubspace (complementaryProjection a b),
        cladeFork (projection a b) (complementaryProjection a b) * y = -y) ∧
     (∀ z : R, ∃! parts : R × R,
        parts.1 ∈ projectorSubspace (projection a b) ∧
        parts.2 ∈ projectorSubspace (complementaryProjection a b) ∧
        parts.1 + parts.2 = z)) ∧
    (evenGrade (projection a b) a = a ∧
     oddGrade (projection a b) a = 0 ∧
     evenGrade (projection a b) b = b ∧
     oddGrade (projection a b) b = 0) ∧
    (fittingRegularPart a b + fittingNilpotentPart a b = a ∧
     fittingRegularPart a b * b = projection a b ∧
     b * fittingRegularPart a b = projection a b ∧
     fittingRegularPart a b * fittingNilpotentPart a b = 0 ∧
     fittingNilpotentPart a b * fittingRegularPart a b = 0 ∧
     (fittingNilpotentPart a b) ^ (k + 1) = 0) := by
  have hP := projection_is_idempotent h
  have hQ := complementaryProjection_is_idempotent h
  have hPQ := projection_mul_complementaryProjection h
  have hQP := complementaryProjection_mul_projection h
  have hPhylo := cladeFork_character_polarity_and_mrca_inclusion hP hQ hPQ hQP
  have hForkSq : cladeFork (projection a b) (complementaryProjection a b) *
      cladeFork (projection a b) (complementaryProjection a b) = 1 := by
    change invS (projection a b) * invS (projection a b) = 1
    peirce_nf hP
  exact ⟨⟨projection_add_complementaryProjection, rfl, hForkSq⟩,
         ⟨hPhylo.2.2.2.2.1, hPhylo.2.2.2.2.2.1,
          drazin_unique_clabject_fixed_point_decomposition h⟩,
         ⟨operator_even h, operator_odd_zero h,
          inverse_even h, inverse_odd_zero h⟩,
         ⟨fittingRegularPart_add_fittingNilpotentPart_eq_self,
          a_semisimple_mul_drazin h,
          drazin_mul_a_semisimple h,
          a_semisimple_mul_a_nilpotent h,
          a_nilpotent_mul_a_semisimple h,
          fittingNilpotentPart_pow_succ_eq_zero h⟩⟩

/-!
## Movement II: The Fourfold Non-Commutative Relational Anatomy (`C4`)
-/

/-- **Movement II (`drazin_fourfold_relational_anatomy`, `C4`)**:
Reuses `EpistemicCompilerPeirceBridge` and `DrazinMPCartan` to isolate the fourfold Peirce
anatomy across `P_D = projection a b` for any `X Y : R`:
1. Exact four-sector reconstruction `peirce11 P_D X + conePlus P_D X + coneMinus P_D X + peirce00 P_D X = X`,
2. Exact core/radical evaluations on `(a, b)`:
   `peirce11 P_D a = fittingRegularPart a b`, `peirce00 P_D a = fittingNilpotentPart a b`,
   `peirce11 P_D b = b`, and `peirce00 P_D b = 0`,
3. Nilpotency of outward projection and inward shadow-intrusion:
   `conePlus P_D X * conePlus P_D Y = 0` and `coneMinus P_D X * coneMinus P_D Y = 0`,
4. Chiral conjugation under `cladeFork P_D Q_D`,
5. Faithful multiplicative `2 × 2` Peirce coordinate representation `peirceCoordinateRingHom`. -/
theorem drazin_fourfold_relational_anatomy
    {a b : R} {k : ℕ} (h : IsDrazinInverse a b k) (X Y : R) :
    (InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) X +
       conePlus (projection a b) X +
       coneMinus (projection a b) X +
       InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (projection a b) X = X) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) a = fittingRegularPart a b ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (projection a b) a = fittingNilpotentPart a b ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) b = b ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (projection a b) b = 0) ∧
    (conePlus (projection a b) X * conePlus (projection a b) Y = 0 ∧
     coneMinus (projection a b) X * coneMinus (projection a b) Y = 0) ∧
    (cladeFork (projection a b) (complementaryProjection a b) *
       evenGrade (projection a b) X *
       cladeFork (projection a b) (complementaryProjection a b) =
       evenGrade (projection a b) X ∧
     cladeFork (projection a b) (complementaryProjection a b) *
       oddGrade (projection a b) X *
       cladeFork (projection a b) (complementaryProjection a b) =
       -oddGrade (projection a b) X) ∧
    (Function.Injective (peirceCoordinateRingHom (projection_is_idempotent h)) ∧
     peirceCoordinateMatrix (projection a b) (X * Y) =
       peirceCoordinateMatrix (projection a b) X *
         peirceCoordinateMatrix (projection a b) Y) := by
  have hP := projection_is_idempotent h
  have hPa := projection_comm_self h
  have hQa := complementaryProjection_comm_self h
  have hQ := complementaryProjection_is_idempotent h
  rcases projection_mul_drazin_self h with ⟨hPbL, hPbR⟩
  rcases complementaryProjection_mul_drazin_zero h with ⟨hQbL, _⟩
  have hFork : cladeFork (projection a b) (complementaryProjection a b) =
      invS (projection a b) := rfl
  have h11a : InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) a =
      fittingRegularPart a b := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 fittingRegularPart
    rw [hPa, mul_assoc, hP]
  have h00a : InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (projection a b) a =
      fittingNilpotentPart a b := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 fittingNilpotentPart
    change complementaryProjection a b * a * complementaryProjection a b =
      a * complementaryProjection a b
    rw [hQa, mul_assoc, hQ]
  have h11b : InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) b = b := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11
    rw [hPbL, hPbR]
  have h00b : InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (projection a b) b = 0 := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00
    change complementaryProjection a b * b * complementaryProjection a b = 0
    rw [hQbL, zero_mul]
  refine ⟨peirce_quartet_reconstruction hP X,
          ⟨h11a, h00a, h11b, h00b⟩,
          ⟨conePlus_mul_conePlus hP X Y, coneMinus_mul_coneMinus hP X Y⟩,
          ⟨by rw [hFork]; peirce_nf hP, by rw [hFork]; peirce_nf hP⟩,
          ⟨peirceCoordinateRingHom_injective hP, peirceCoordinateMatrix_mul hP X Y⟩⟩

/-!
## Movement III: Malik–Thome `DMP`/`MPD` Pairing and Inner-Inverse Sandwich (`C5`)
-/

/-- **Movement III (`drazin_transcendent_function_malik_thome`, `C5`)**:
Reuses `DrazinMoorePenrosePartition`, `GradedDMPResolution`,
`CyclotomicGaloisNilpotentSylvesterSynthesis`, and `EpistemicCompilerPeirceBridge` to show that
given ANY Drazin witness `h : IsDrazinInverse a b k` and ANY inner `{1}`-inverse `m_dag`
(`hInner : a * m_dag * a = a`), the compressed inner inverse on `P_D = projection a b`
collapses to `b` (`projection a b * m_dag * projection a b = b`), and pairing the Malik–Thome
hybrids `dmpInverse a b m_dag = dmpOp P_D m_dag` and `dualDmpInverse a b m_dag = mpdOp P_D m_dag`.
The split-quaternion (`Φ, J, V, Σ`) identities in the conclusion hold for any idempotent
`P` and any `m`; only the sandwich collapse and `dmpOp = b + conePlus` use the Drazin and
inner-inverse hypotheses. -/
theorem drazin_transcendent_function_malik_thome
    {a b m_dag : R} {k : ℕ} (h : IsDrazinInverse a b k)
    (hInner : a * m_dag * a = a) :
    (dmpInverse a b m_dag = dmpOp (projection a b) m_dag ∧
     dualDmpInverse a b m_dag = mpdOp (projection a b) m_dag ∧
     projection a b * m_dag * projection a b = b) ∧
    (dmpOp (projection a b) m_dag = b + conePlus (projection a b) m_dag ∧
     mpdOp (projection a b) m_dag = b + coneMinus (projection a b) m_dag) ∧
    (dmpOp (projection a b) m_dag - mpdOp (projection a b) m_dag =
       peirceAd (projection a b) m_dag ∧
     peirceAd (projection a b) m_dag = genJ (projection a b) m_dag m_dag ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm (projection a b) (dmpOp (projection a b) m_dag) -
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm (projection a b) (mpdOp (projection a b) m_dag) =
       genPhi (projection a b) m_dag m_dag) ∧
    (dmpOp (projection a b) m_dag * mpdOp (projection a b) m_dag - b * b =
       qgtPlus (projection a b) m_dag m_dag ∧
     complementaryProjection a b *
       (mpdOp (projection a b) m_dag * dmpOp (projection a b) m_dag) *
       complementaryProjection a b =
       qgtMinus (projection a b) m_dag m_dag ∧
     qgtPlus (projection a b) m_dag m_dag + qgtMinus (projection a b) m_dag m_dag =
       genV (projection a b) m_dag m_dag ∧
     qgtPlus (projection a b) m_dag m_dag - qgtMinus (projection a b) m_dag m_dag =
       genSig (projection a b) m_dag m_dag ∧
     genPhi (projection a b) m_dag m_dag * genPhi (projection a b) m_dag m_dag =
       genV (projection a b) m_dag m_dag ∧
     genJ (projection a b) m_dag m_dag * genJ (projection a b) m_dag m_dag =
       -genV (projection a b) m_dag m_dag ∧
     genJ (projection a b) m_dag m_dag * genPhi (projection a b) m_dag m_dag =
       genSig (projection a b) m_dag m_dag) := by
  have hP := projection_is_idempotent h
  have hBM : b * a = projection a b := h.comm.symm
  have hMB : a * b = projection a b := rfl
  have hSand := drazin_mp_universal_sandwich_collapse h.idempotent hBM hMB hInner
  have hClosure := dmp_residual_qgt_and_anamnesis_tetraktys_closure hP m_dag
  have hTet := tetraktys_coniunctio (projection a b) hP m_dag m_dag
  have hPeirce11 : InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) m_dag = b :=
    hSand.2.2.2.1
  have hDmpB : dmpOp (projection a b) m_dag = b + conePlus (projection a b) m_dag := by
    rw [hClosure.1, hPeirce11]
  have hMpdB : mpdOp (projection a b) m_dag = b + coneMinus (projection a b) m_dag := by
    rw [hClosure.2.1, hPeirce11]
  have hAdJ : peirceAd (projection a b) m_dag = genJ (projection a b) m_dag m_dag := by
    unfold peirceAd InfoGeometry.OperatorAlgebra.PeirceSpine.comm genJ conePlus coneMinus
    peirce_nf hP
  have hPlus : dmpOp (projection a b) m_dag * mpdOp (projection a b) m_dag - b * b =
      qgtPlus (projection a b) m_dag m_dag := by
    rw [hClosure.2.2.1, hPeirce11]
    abel
  have hMinus : complementaryProjection a b *
      (mpdOp (projection a b) m_dag * dmpOp (projection a b) m_dag) *
      complementaryProjection a b =
      qgtMinus (projection a b) m_dag m_dag :=
    qgtMinus_compress_idempotent (projection a b) m_dag
  exact ⟨⟨dmp_eq_projection_mul h, dualDmp_eq_mul_projection a b m_dag, hSand.2.2.2.1⟩,
         ⟨hDmpB, hMpdB⟩,
         ⟨rfl, hAdJ, hClosure.2.2.2.2.2.2.2.2.1⟩,
         ⟨hPlus, hMinus, rfl, rfl, hTet.2.2.1, hTet.2.2.2.1, hTet.2.2.2.2.1⟩⟩

/-!
## Movement IV: Socratic Aporia, Moore–Penrose Obstruction & Criterion, Shell Cascade, & Meta-Cognitive Tower (`C6`–`C9`)
-/

/-- **Movement IV (`drazin_socratic_aporia_and_metacognitive_tower`, `C6`–`C9`)**:
Reuses `DrazinJordanChevalleyBridge`, `EpistemicCompilerPeirceBridge`, `OntologyRing`,
`MoorePenroseDrazinObstruction`, `MoorePenroseDrazinCriterion`, and `DrazinShellCascade`:
1. **Orthogonal Fitting Split of Socratic Aporia (`C6`)**:
   `idempotencyDefect (projection a b) = 0`,
   `idempotencyDefect (complementaryProjection a b) = 0`, and
   `idempotencyDefect a = idempotencyDefect (fittingRegularPart a b) + idempotencyDefect (fittingNilpotentPart a b)`.
2. **Coupled Thesis Aporia & Completed Square (`C6`)**:
   `idempotencyDefect (projection a b + genPhi (projection a b) m_dag m_dag) = genV (projection a b) m_dag m_dag`,
   `idempotencyDefect (projection a b + genJ (projection a b) m_dag m_dag) = -genV (projection a b) m_dag m_dag`, and
   `((2 : ℤ) • (projection a b + genPhi (projection a b) m_dag m_dag) - 1) ^ 2 = 1 + (4 : ℤ) • genV (projection a b) m_dag m_dag`.
3. **Recursive Defect Iteration Tower (`C9`)**:
   `idempotencyDefect^[n] (genV (projection a b) m_dag m_dag) = idempotencyDefect^[n] (qgtPlus (projection a b) m_dag m_dag) + idempotencyDefect^[n] (qgtMinus (projection a b) m_dag m_dag)`.
4. **Superoperator Meta-Cognitive Group-Inverse Closure & Grassmannian Tangent Space (`C9`)**:
   `peirceAdCube (projection a b) X = peirceAd (projection a b) X`,
   `peirceAdFourth (projection a b) X = peirceAdSq (projection a b) X`,
   `peirceAdSq (projection a b) X = oddGrade (projection a b) X`, and
   `((projection a b * X + X * projection a b = X) ↔ oddGrade (projection a b) X = X)`.
5. **Fundamental Moore–Penrose vs. Drazin Obstruction, EP Criterion, & Symbiotic Shell Cascade (`C7`–`C8`)**:
   `¬ IsDrazinInverse n_op m_op k`,
   `(∃ idx, IsDrazinInverse n_op m_op idx) ↔ n_op * m_op = m_op * n_op`,
   `cladeSubsumes (drazinShellProj a b M m) (complementaryProjection a b)`,
   `projectorSubspace (drazinShellProj a b M m) ⊆ projectorSubspace (complementaryProjection a b)`,
   `cladeSubsumes (drazinRangeProj a b M q) (drazinRangeProj a b M p)` for `p ≤ q`,
   `drazinShellProj a b M m * a * drazinShellProj a b M s = 0` for `m ≤ s`, and
   `a = projection a b * a * projection a b + ∑ idx ∈ Finset.range k, drazinShellProj a b M idx * a * (∑ r_idx ∈ Finset.range idx, drazinShellProj a b M r_idx)`. -/
theorem drazin_socratic_aporia_and_metacognitive_tower
    [StarRing R]
    {a b m_dag n_op m_op : R} {k r m s p q : ℕ}
    (h : IsDrazinInverse a b k)
    (hMP : IsMoorePenroseInverse n_op m_op)
    (hn_nil : n_op ^ r = 0) (hn_ne : n_op ≠ 0)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a b) M)
    (hms : m ≤ s) (hpq : p ≤ q) (X : R) :
    -- 1. Orthogonal Fitting Split of Socratic Aporia:
    (idempotencyDefect (projection a b) = 0 ∧
     idempotencyDefect (complementaryProjection a b) = 0 ∧
     idempotencyDefect a =
       idempotencyDefect (fittingRegularPart a b) +
         idempotencyDefect (fittingNilpotentPart a b)) ∧
    -- 2. Coupled Thesis Aporia & Completed Square:
    (idempotencyDefect (projection a b + genPhi (projection a b) m_dag m_dag) =
       genV (projection a b) m_dag m_dag ∧
     idempotencyDefect (projection a b + genJ (projection a b) m_dag m_dag) =
       -genV (projection a b) m_dag m_dag ∧
     ((2 : ℤ) • (projection a b + genPhi (projection a b) m_dag m_dag) - 1) *
       ((2 : ℤ) • (projection a b + genPhi (projection a b) m_dag m_dag) - 1) =
       1 + (4 : ℤ) • genV (projection a b) m_dag m_dag) ∧
    -- 3. Recursive Defect Iteration Tower:
    (∀ n : ℕ,
       idempotencyDefect^[n] (genV (projection a b) m_dag m_dag) =
         idempotencyDefect^[n] (qgtPlus (projection a b) m_dag m_dag) +
           idempotencyDefect^[n] (qgtMinus (projection a b) m_dag m_dag)) ∧
    -- 4. Superoperator Group-Inverse Closure & Grassmannian Tangent Space:
    (peirceAdCube (projection a b) X = peirceAd (projection a b) X ∧
     peirceAdFourth (projection a b) X = peirceAdSq (projection a b) X ∧
     peirceAdSq (projection a b) X = oddGrade (projection a b) X ∧
     ((projection a b * X + X * projection a b = X) ↔ oddGrade (projection a b) X = X)) ∧
    -- 5. Fundamental MP Obstruction, EP Criterion, & Symbiotic Nilpotent Shell Cascade:
    (¬ IsDrazinInverse n_op m_op k ∧
     ((∃ idx, IsDrazinInverse n_op m_op idx) ↔ n_op * m_op = m_op * n_op) ∧
     cladeSubsumes (drazinShellProj a b M m) (complementaryProjection a b) ∧
     projectorSubspace (drazinShellProj a b M m) ⊆
       projectorSubspace (complementaryProjection a b) ∧
     cladeSubsumes (drazinRangeProj a b M q) (drazinRangeProj a b M p) ∧
     drazinShellProj a b M m * a * drazinShellProj a b M s = 0 ∧
     a = projection a b * a * projection a b +
           ∑ idx ∈ Finset.range k,
             drazinShellProj a b M idx * a *
               (∑ r_idx ∈ Finset.range idx, drazinShellProj a b M r_idx)) := by
  have hP := projection_is_idempotent h
  have hQ := complementaryProjection_is_idempotent h
  have hDefP : idempotencyDefect (projection a b) = 0 := by
    simp [idempotencyDefect, hP]
  have hDefQ : idempotencyDefect (complementaryProjection a b) = 0 := by
    simp [idempotencyDefect, hQ]
  have hAporia : idempotencyDefect a =
      idempotencyDefect (fittingRegularPart a b) +
        idempotencyDefect (fittingNilpotentPart a b) := by
    calc
      idempotencyDefect a
          = idempotencyDefect (fittingRegularPart a b + fittingNilpotentPart a b) := by
            congr 1
            exact fittingRegularPart_add_fittingNilpotentPart_eq_self.symm
      _ = idempotencyDefect (fittingRegularPart a b) +
            idempotencyDefect (fittingNilpotentPart a b) :=
            defect_add_of_ortho (a_semisimple_mul_a_nilpotent h) (a_nilpotent_mul_a_semisimple h)
  have hGold := golden_coagulation_discriminant (projection a b) hP m_dag m_dag
  have hAporiaJ := (epistemic_aporia_defect_laws hP m_dag m_dag).2.2
  have hTower := genV_defect_iterates_cycle_split hP m_dag m_dag
  have hSieve := nigredo_commutator_sieve hP X
  have hAdSqOdd : peirceAdSq (projection a b) X = oddGrade (projection a b) X := by
    rw [← hSieve.1]
    rfl
  have hShellSub : cladeSubsumes (drazinShellProj a b M m) (complementaryProjection a b) := by
    unfold cladeSubsumes drazinShellProj
    exact ⟨by rw [mul_assoc, hQ], by rw [← mul_assoc, ← mul_assoc, hQ]⟩
  have hRangeSub : cladeSubsumes (drazinRangeProj a b M q) (drazinRangeProj a b M p) :=
    ⟨drazinRangeProj_mul_of_ge h hM hpq, drazinRangeProj_mul_of_le h hM hpq⟩
  exact ⟨⟨hDefP, hDefQ, hAporia⟩,
         ⟨hGold.1, hAporiaJ, hGold.2⟩,
         hTower,
         ⟨hSieve.2.2.2.1, hSieve.2.2.2.2, hAdSqOdd,
          grassmannian_tangent_iff_oddGrade_fixed hP X⟩,
         ⟨nilpotent_moore_penrose_not_drazin hMP hn_nil hn_ne k,
          exists_index_iff_commute hMP,
          hShellSub,
          cladeSubsumes_projectorSubspace_subset hShellSub,
          hRangeSub,
          drazinShellProj_mul_a_mul_drazinShellProj_eq_zero_of_le h hM hms,
          drazin_core_and_shell_cascade h hM⟩⟩

/-!
## Movement V: Acyclic Causal Posets (`DrazinEpistemicStage`, `GradedDMPDependencyOrder.Stage`, `OntologyMetaLevel`) & Master Coagulation (`C10`–`C11`)
-/

/-- The 6-stage acyclic causal poset of the Drazin `solve et coagula` epistemic compiler. -/
inductive DrazinEpistemicStage : Type
  | E0_PrimordialDualRootsAndBinaryCut
  | E1_FourfoldPeirceAnatomy
  | E2_MalikThomeTranscendentFunction
  | E3_SocraticAporiaAndShellCascade
  | E4_SuperoperatorAndRectangularRetractTower
  | E5_ErlangenMultilevelMasterCoagulation
  deriving DecidableEq, Repr, Inhabited

namespace DrazinEpistemicStage

/-- Topological rank (`0` through `5`) in the Drazin epistemic compiler poset. -/
def rank : DrazinEpistemicStage → ℕ
  | .E0_PrimordialDualRootsAndBinaryCut         => 0
  | .E1_FourfoldPeirceAnatomy                   => 1
  | .E2_MalikThomeTranscendentFunction          => 2
  | .E3_SocraticAporiaAndShellCascade           => 3
  | .E4_SuperoperatorAndRectangularRetractTower => 4
  | .E5_ErlangenMultilevelMasterCoagulation     => 5

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder DrazinEpistemicStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal edge `u ≺ v` in the Drazin epistemic compiler poset. -/
def causalEdge (u v : DrazinEpistemicStage) : Prop :=
  u.rank < v.rank

instance instDecidableRelCausalEdge : DecidableRel causalEdge :=
  fun u v => inferInstanceAs (Decidable (u.rank < v.rank))

theorem transGen_causalEdge_lt_rank {u v : DrazinEpistemicStage}
    (h : Relation.TransGen causalEdge u v) : u.rank < v.rank := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih => exact Nat.lt_trans ih h2

/-- Strict acyclicity of the Drazin `solve et coagula` causal poset. -/
theorem causalEdge_acyclic (u : DrazinEpistemicStage) :
    ¬ Relation.TransGen causalEdge u u :=
  fun h => Nat.lt_irrefl u.rank (transGen_causalEdge_lt_rank h)

end DrazinEpistemicStage

/-!
### Movement V-B: Cline Shift, All-Degree Polynomial Drazin, Bicommutant Closure, Kemeny–Snell Markov Group Drazin, & Krein Self-Adjoint Green Inheritance
-/

section ClinePolynomialBicommutantMarkovKrein

open InfoGeometry.Canonical.DrazinCommutant
open InfoGeometry.Canonical.RoseDrazinPolynomial
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace
open InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded
open InfoGeometry.HodgeCohomology.KreinDrazinGreen

/-- If `x` commutes with `a` (`a * x = x * a`) and `b` is a Drazin inverse of `a`, then `x`
also commutes with the spectral projector `projection a b = a * b` and complementary projector
`complementaryProjection a b = 1 - a * b`. -/
theorem projection_commutes_of_commutes
    {a b x : R} {k : ℕ}
    (h : IsDrazinInverse a b k)
    (hx : a * x = x * a) :
    projection a b * x = x * projection a b ∧
    complementaryProjection a b * x = x * complementaryProjection a b := by
  have hbx : b * x = x * b := inverse_commutes_of_commutes h x hx
  have hproj : projection a b * x = x * projection a b := by
    unfold projection
    calc
      (a * b) * x = a * (b * x) := by noncomm_ring
      _ = a * (x * b) := by rw [hbx]
      _ = (a * x) * b := by noncomm_ring
      _ = (x * a) * b := by rw [hx]
      _ = x * (a * b) := by noncomm_ring
  refine ⟨hproj, ?_⟩
  unfold complementaryProjection
  calc
    (1 - projection a b) * x = x - projection a b * x := by noncomm_ring
    _ = x - x * projection a b := by rw [hproj]
    _ = x * (1 - projection a b) := by noncomm_ring

/-- Ring-level Clade 0 wild weak-Drazin perturbation: adding any right-multiple of the
complementary projector `z * complementaryProjection a b` to a Drazin inverse `b` preserves
the Campbell–Meyer weak Drazin relation `IsWeakDrazin a (b + z * complementaryProjection a b) k`,
while strictly changing the operator whenever `z * complementaryProjection a b ≠ 0`. -/
theorem isWeakDrazin_add_mul_complementaryProjection
    {a b : R} {k : ℕ}
    (h : IsDrazinInverse a b k) (z : R) :
    IsWeakDrazin a (b + z * complementaryProjection a b) k := by
  unfold IsWeakDrazin
  have hweak : b * a ^ (k + 1) = a ^ k := Drazin_isWeakDrazin h
  have hq_pow : complementaryProjection a b * a ^ k = 0 :=
    complementaryProjection_mul_power_eq_zero h
  calc
    (b + z * complementaryProjection a b) * a ^ (k + 1)
        = b * a ^ (k + 1) + z * (complementaryProjection a b * a ^ k) * a := by
            rw [pow_succ a k]
            noncomm_ring
    _ = a ^ k + z * 0 * a := by rw [hweak, hq_pow]
    _ = a ^ k := by noncomm_ring

/-- Any non-annihilated nilpotent perturbation `z * complementaryProjection a b ≠ 0` produces
a distinct weak Drazin inverse `b + z * complementaryProjection a b ≠ b`. -/
theorem add_mul_complementaryProjection_ne_self
    (a b z : R)
    (hz : z * complementaryProjection a b ≠ 0) :
    b + z * complementaryProjection a b ≠ b := by
  intro heq
  apply hz
  calc
    z * complementaryProjection a b = (b + z * complementaryProjection a b) - b := by noncomm_ring
    _ = b - b := by rw [heq]
    _ = 0 := sub_self b

/-- **Unified Synthesis of Cline's Shift, All-Degree Polynomial Drazin, Bicommutant Closure,
Weak-Drazin Wild Perturbation, Kemeny–Snell Markov Group Drazin, and Krein Self-Adjoint Green**:
**Aggregation note:** this theorem is a conjunction of existing results with independent
hypotheses; no implication or map between the conjuncts is asserted.
1. **Bicommutant Closure (`DrazinCommutant`)**:
   `a * x_comm = x_comm * a ⟹ b * x_comm = x_comm * b`, `P_D * x_comm = x_comm * P_D`, and
   `Q_D * x_comm = x_comm * Q_D`.
2. **Clade 0 Wild Nilpotent Perturbation (`CampbellMeyerWeakDrazin`)**:
   Both the general ring-level perturbation `b + z_wild * Q_D` (`isWeakDrazin_add_mul_complementaryProjection`,
   `add_mul_complementaryProjection_ne_self`) and the explicit `3 × 3` witness `weakWildInverse ≠ weakDrazinInverse`
   satisfy `IsWeakDrazin` while violating uniqueness.
3. **All-Degree Polynomial Drazin Construction (`RoseDrazinPolynomial`)**:
   `a_poly * p_poly = p_poly * a_poly` and `a_poly ^ (k_poly + 1) * p_poly = a_poly ^ k_poly`
   imply `IsDrazinInverse a_poly (polynomialDrazinCandidate a_poly p_poly k_poly) k_poly`
   with spectral projector `a_poly ^ k_poly * p_poly ^ k_poly`.
4. **Cline's Non-Commutative Drazin Shift (`ab → ba`)**:
   `IsDrazinInverse (u_cline * v_cline) d_cline k_cline` implies
   `IsDrazinInverse (v_cline * u_cline) (clineDrazinShift u_cline v_cline d_cline) (k_cline + 1)`
   with spectral projector `v_cline * d_cline * u_cline`, complementary projector
   `1 - v_cline * d_cline * u_cline`, and regular core
   `v_cline * projection (u_cline * v_cline) d_cline * u_cline`.
5. **Clade 6 — Kemeny–Snell Stationary-Projector Group Drazin & Stochastic Attention Laplacian**:
   For `E₀ * E₀ = E₀`, `L_markov * E₀ = 0`, `E₀ * L_markov = 0`, `(L_markov + E₀) * Z_ks = 1`,
   and `Z_ks * (L_markov + E₀) = 1`, `kemenySnellDeviation Z_ks E₀ = Z_ks - E₀` satisfies
   `IsDrazinInverse L_markov (kemenySnellDeviation Z_ks E₀) 1` with complementary projector `E₀`;
   and every finite row-stochastic matrix `P_stoch ∈ Matrix.rowStochastic ℝ ι` admits a group
   inverse for `Matrix.toLin' (1 - P_stoch)`.
6. **Clade 5 — Krein Self-Adjoint Green Operator & Projector Inheritance (`KreinDrazinGreen`)**:
   For any Krein self-adjoint bounded operator `op_krein : Space →L[ℝ] Space` with Drazin Green
   inverse `green_krein`, `kreinAdjoint green_krein = green_krein`,
   `kreinAdjoint (projection op_krein green_krein) = projection op_krein green_krein`, and
   `kreinAdjoint (complementaryProjection op_krein green_krein) = complementaryProjection op_krein green_krein`. -/
theorem drazin_cline_polynomial_bicommutant_markov_krein_synthesis
    {a b x_comm z_wild a_poly p_poly u_cline v_cline d_cline L_markov E₀ Z_ks : R}
    {k k_poly k_cline : ℕ}
    (h : IsDrazinInverse a b k)
    (hx_comm : a * x_comm = x_comm * a)
    (hz_wild : z_wild * complementaryProjection a b ≠ 0)
    (hpoly_comm : a_poly * p_poly = p_poly * a_poly)
    (hpoly_pow : a_poly ^ (k_poly + 1) * p_poly = a_poly ^ k_poly)
    (hcline : IsDrazinInverse (u_cline * v_cline) d_cline k_cline)
    (hE₀_idem : E₀ * E₀ = E₀)
    (hLE₀ : L_markov * E₀ = 0)
    (hE₀L : E₀ * L_markov = 0)
    (hLZ : (L_markov + E₀) * Z_ks = 1)
    (hZL : Z_ks * (L_markov + E₀) = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P_stoch : Matrix ι ι ℝ) (hP_stoch : P_stoch ∈ Matrix.rowStochastic ℝ ι)
    {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [CompleteSpace Space] [KreinSpace Space]
    {op_krein green_krein : Space →L[ℝ] Space} {k_krein : ℕ}
    (h_krein_drazin : IsDrazinInverse op_krein green_krein k_krein)
    (h_krein_sa : IsKreinSelfAdjoint op_krein) :
    -- 1. Bicommutant closure:
    (b * x_comm = x_comm * b ∧
     projection a b * x_comm = x_comm * projection a b ∧
     complementaryProjection a b * x_comm = x_comm * complementaryProjection a b) ∧
    -- 2. Clade 0 wild nilpotent perturbation (ring-level + 3×3 concrete witness):
    (IsWeakDrazin a (b + z_wild * complementaryProjection a b) k ∧
     b + z_wild * complementaryProjection a b ≠ b ∧
     IsWeakDrazin weakA weakWildInverse 2 ∧
     weakWildInverse ≠ weakDrazinInverse) ∧
    -- 3. All-degree polynomial Drazin construction:
    (IsDrazinInverse a_poly (polynomialDrazinCandidate a_poly p_poly k_poly) k_poly ∧
     projection a_poly (polynomialDrazinCandidate a_poly p_poly k_poly) =
       a_poly ^ k_poly * p_poly ^ k_poly) ∧
    -- 4. Cline's non-commutative Drazin shift (`ab → ba`):
    (IsDrazinInverse (v_cline * u_cline) (clineDrazinShift u_cline v_cline d_cline) (k_cline + 1) ∧
     projection (v_cline * u_cline) (clineDrazinShift u_cline v_cline d_cline) =
       v_cline * d_cline * u_cline ∧
     complementaryProjection (v_cline * u_cline) (clineDrazinShift u_cline v_cline d_cline) =
       1 - v_cline * d_cline * u_cline ∧
     fittingRegularPart (v_cline * u_cline) (clineDrazinShift u_cline v_cline d_cline) =
       v_cline * projection (u_cline * v_cline) d_cline * u_cline) ∧
    -- 5. Clade 6 (Kemeny–Snell Markov ergodic group Drazin & stochastic Laplacian group inverse):
    (IsDrazinInverse L_markov (kemenySnellDeviation Z_ks E₀) 1 ∧
     complementaryProjection L_markov (kemenySnellDeviation Z_ks E₀) = E₀ ∧
     (∃ D_stoch : Module.End ℝ (ι → ℝ), IsGroupInverse (Matrix.toLin' (1 - P_stoch)) D_stoch)) ∧
    -- 6. Clade 5 (Krein self-adjoint Green operator & projector inheritance):
    (kreinAdjoint green_krein = green_krein ∧
     kreinAdjoint (projection op_krein green_krein) = projection op_krein green_krein ∧
     kreinAdjoint (complementaryProjection op_krein green_krein) =
       complementaryProjection op_krein green_krein) := by
  have hproj_comm := projection_commutes_of_commutes h hx_comm
  exact ⟨⟨inverse_commutes_of_commutes h x_comm hx_comm, hproj_comm.1, hproj_comm.2⟩,
         ⟨isWeakDrazin_add_mul_complementaryProjection h z_wild,
          add_mul_complementaryProjection_ne_self a b z_wild hz_wild,
          weakWildInverse_isWeak, weakWildInverse_ne_Drazin⟩,
         ⟨isDrazinInverse_polynomialDrazinCandidate a_poly p_poly k_poly hpoly_comm hpoly_pow,
          polynomialDrazinCandidate_projection_eq a_poly p_poly k_poly hpoly_pow⟩,
         ⟨isDrazinInverse_clineDrazinShift hcline,
          clineDrazinShift_projection_eq hcline,
          clineDrazinShift_complementaryProjection_eq hcline,
          clineDrazinShift_fittingRegularPart_eq hcline⟩,
         ⟨isDrazinInverse_kemenySnellDeviation hE₀_idem hLE₀ hE₀L hLZ hZL,
          kemenySnellDeviation_complementaryProjection_eq hE₀_idem hLE₀ hE₀L hLZ,
          exists_stochastic_laplacian_groupInverse P_stoch hP_stoch⟩,
         ⟨green_krein_adjoint h_krein_drazin h_krein_sa,
          regular_projector_krein_adjoint h_krein_drazin h_krein_sa,
          complementary_projector_krein_adjoint h_krein_drazin h_krein_sa⟩⟩

end ClinePolynomialBicommutantMarkovKrein

/-!
### Movement V-C: Greville Souriau–Frame (Clade 1B), Split-Octonion $\ell$-Native Drazin Defect (Clade 4B), Dirac–Kähler & Hodge-Star Drazin Propagators (Clade 5B), and Gromov–Witten / $\mathrm{Cl}(5,5)$ Five-Graded Unification (Clade 7)
-/

section CompleteCladeComplementSynthesis

open InfoGeometry.Canonical.GrevilleSouriauFrameDrazin
open InfoGeometry.Canonical.HodgeStarOperatorDrazinBridge
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Lie.SplitOctonionEllNativeDrazinDefect
open InfoGeometry.GromovWittenErlangen
open InfoGeometry.SuperGrassmannian
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
open InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification

/-- **Complete 7-Clade Taxonomic Complement Synthesis (`drazin_clades_4b_5b_7_complete_complement_synthesis`)**:
**Aggregation note:** this theorem is a conjunction of existing results with independent
hypotheses; no implication or map between the conjuncts is asserted.
Collects results from the remaining specialized clades of the 7-clade taxonomy:
1. **Clade 1B — Greville's Ring-Level & Rational Souriau–Frame Formula (`GrevilleSouriauFrameDrazin`)**:
   `isDrazinInverse_grevilleSouriauFrameCandidate`, `grevilleSouriauFrameCandidate_projection_eq`,
   `greville_formula_candidate_isDrazinInverse`, and `mat3_noncommutativity_witness`.
2. **Clade 4B — Nonassociative Split-Octonion $\ell$-Native Drazin Defect (`SplitOctonionEllNativeDrazinDefect`)**:
   Canonical index-1 Drazin inverse `IsDrazinInverse ellGrading ellGrading 1`,
   `ellNativeDrazinProjector = flowPlus + flowMinus`, `ellNativeDrazinDefect = flowZero`,
   `LinearMap.range ellNativeDrazinDefect = LinearMap.ker ellGrading`, and
   `ellGrading * ellNativeDrazinDefect = 0`.
3. **Clade 5B — Dirac–Kähler Propagator & Hodge-Star Drazin Involution (`DiracKahlerDrazinPropagatorBridge` & `HodgeStarOperatorDrazinBridge`)**:
   `D_dk * G_dk + complementaryProjection D_dk G_dk = 1`, `A_dk * G_dk1 * A_dk = A_dk`,
   `B_hodge.hodgeStar * B_hodge.hodgeStar = 1`, and
   `B_hodge.hodgeLaplacian (nativeHodgeStar x_hodge) = nativeHodgeStar (B_hodge.hodgeLaplacian x_hodge)`.
4. **Clade 7 — Gromov–Witten Fixed-Sector `DrazinLocalization` & $\mathrm{Cl}(5,5)$ Five-Graded Para-Kähler / Fisher–Souriau Equivariance**:
   Orthogonal annihilation between localized edge Drazin residues and regular inverses
   (`edgeResidue_mul_regularInverse`, `edgeRegularInverse_mul_residue`), para-Kähler isotropic
   cross-sheet quadratic decomposition `g_pk (u_pk + α_pk) (u_pk + α_pk) = 2 * g_pk u_pk α_pk`,
   and symmetric-group equivariance of the Souriau–Massieu potential and Fisher–Souriau attention
   Laplacian (`souriauMassieuPotential_perm_invariant`, `fisherSouriauLaplacian_perm_equivariant`). -/
theorem drazin_clades_4b_5b_7_complete_complement_synthesis
    {a_grev b_prev inv_ps : R} {k_grev : ℕ}
    (hcomm_b : a_grev * b_prev = b_prev * a_grev)
    (hcomm_ps : a_grev * inv_ps = inv_ps * a_grev)
    (hrec_grev : a_grev ^ (k_grev + 1) * (b_prev * inv_ps) = a_grev ^ k_grev)
    {C_dk : Type*} [AddCommGroup C_dk] [Module ℝ C_dk]
    {D_dk G_dk A_dk G_dk1 : Module.End ℝ C_dk}
    (hProp_dk1 : IsDrazinInverse A_dk G_dk1 1)
    {E_hodge : Type*} [NormedAddCommGroup E_hodge] [InnerProductSpace ℝ E_hodge]
    [CompleteSpace E_hodge] [InfoGeometry.Krein.HodgeStarOperator.KreinSpace E_hodge]
    (B_hodge : DrazinHodgeChiralBridge (E := E_hodge))
    (hCompat_hodge : HodgeStarCompatibility B_hodge) (x_hodge : E_hodge)
    {G_gw T_gw Target_gw Coeff_gw Algebra_gw : Type*} [Ring Algebra_gw] [StarRing Algebra_gw]
    (P_gw : GWDrazinLocalizationPacket G_gw T_gw Target_gw Coeff_gw Algebra_gw)
    (e_gw : P_gw.virtualLocalization.graph.Edge)
    {V_pk : Type*} [AddCommGroup V_pk] [Module ℝ V_pk]
    (K_pk : V_pk →ₗ[ℝ] V_pk) (g_pk : V_pk →ₗ[ℝ] V_pk →ₗ[ℝ] ℝ)
    (hK_pk : ∀ v, K_pk (K_pk v) = v)
    (hsymm_pk : ∀ u v, g_pk u v = g_pk v u)
    (hg_pk : ∀ u v, g_pk (K_pk u) (K_pk v) = - g_pk u v)
    {u_pk α_pk : V_pk} (hu_pk : u_pk ∈ primalSheet K_pk) (hα_pk : α_pk ∈ covectorVacuumSheet K_pk)
    {n_fs : ℕ} (σ_fs : Equiv.Perm (Fin n_fs)) (s_fs : Fin n_fs → ℝ) (i_fs j_fs : Fin n_fs) :
    -- 1. Clade 1B (Greville general ring-level & rational Souriau–Frame formula):
    (IsDrazinInverse a_grev (grevilleSouriauFrameCandidate a_grev b_prev inv_ps k_grev) k_grev ∧
     projection a_grev (grevilleSouriauFrameCandidate a_grev b_prev inv_ps k_grev) =
       a_grev ^ k_grev * (b_prev * inv_ps) ^ k_grev ∧
     IsDrazinInverse grevilleA grevilleFormulaCandidate 2 ∧
     matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01) ∧
    -- 2. Clade 4B (Nonassociative Split-Octonion ell-native Drazin defect):
    (IsDrazinInverse ellGrading ellGrading 1 ∧
     ellNativeDrazinProjector = flowPlus + flowMinus ∧
     ellNativeDrazinDefect = flowZero ∧
     LinearMap.range ellNativeDrazinDefect = LinearMap.ker ellGrading ∧
     ellGrading * ellNativeDrazinDefect = 0) ∧
    -- 3. Clade 5B (Dirac–Kähler propagator & Hodge-star Drazin involution):
    (D_dk * G_dk + complementaryProjection D_dk G_dk = 1 ∧
     A_dk * G_dk1 * A_dk = A_dk ∧
     B_hodge.hodgeStar * B_hodge.hodgeStar = (1 : E_hodge →L[ℝ] E_hodge) ∧
     B_hodge.hodgeLaplacian (nativeHodgeStar (E := E_hodge) x_hodge) =
       nativeHodgeStar (E := E_hodge) (B_hodge.hodgeLaplacian x_hodge)) ∧
    -- 4. Clade 7 (Gromov–Witten Drazin localization & Cl(5,5) Para-Kähler / Fisher–Souriau equivariance):
    (P_gw.edgeLocalizedDrazinResidue e_gw * P_gw.edgeLocalizedRegularInverse e_gw = 0 ∧
     P_gw.edgeLocalizedRegularInverse e_gw * P_gw.edgeLocalizedDrazinResidue e_gw = 0 ∧
     g_pk (u_pk + α_pk) (u_pk + α_pk) = 2 * g_pk u_pk α_pk ∧
     souriauMassieuPotential (s_fs ∘ σ_fs) = souriauMassieuPotential s_fs ∧
     fisherSouriauLaplacian (s_fs ∘ σ_fs) i_fs j_fs =
       fisherSouriauLaplacian s_fs (σ_fs i_fs) (σ_fs j_fs)) := by
  exact ⟨⟨isDrazinInverse_grevilleSouriauFrameCandidate a_grev b_prev inv_ps k_grev hcomm_b hcomm_ps hrec_grev,
          grevilleSouriauFrameCandidate_projection_eq a_grev b_prev inv_ps k_grev hrec_grev,
          greville_formula_candidate_isDrazinInverse,
          mat3_noncommutativity_witness⟩,
         ⟨(singular_iff_canonical_drazin ellGrading ellGrading 1).mp ellGrading_isDrazinInverse,
          ellNativeDrazinProjector_eq_flowPlus_add_flowMinus,
          ellNativeDrazinDefect_eq_flowZero,
          ellNativeDrazinDefect_range_eq_ker,
          ellGrading_mul_ellNativeDrazinDefect⟩,
         ⟨dirac_drazin_projection_decomposition D_dk G_dk,
          drazin_greens_function A_dk G_dk1 hProp_dk1,
          drazin_hodgeStar_clm_sq_eq_one_of_compatibility B_hodge hCompat_hodge,
          drazin_laplacian_commutes_nativeHodgeStar_of_compatibility B_hodge hCompat_hodge x_hodge⟩,
         ⟨P_gw.edgeResidue_mul_regularInverse e_gw,
          P_gw.edgeRegularInverse_mul_residue e_gw,
          paraKahler_sum_quadratic_eq_two_pairing K_pk g_pk hK_pk hsymm_pk hg_pk hu_pk hα_pk,
          souriauMassieuPotential_perm_invariant σ_fs s_fs,
          fisherSouriauLaplacian_perm_equivariant σ_fs s_fs i_fs j_fs⟩⟩

end CompleteCladeComplementSynthesis

/-- **Master Structural Synthesis (`drazin_epistemic_solve_et_coagula_master_synthesis`, `C1`–`C11`)**:
**Aggregation note:** this theorem is a conjunction of existing results with independent
hypotheses; no implication or map between the conjuncts is asserted.
Collects the Movement I–V results over `[Ring R] [StarRing R]`:
1. **Acyclic Causal Posets (`DrazinEpistemicStage`, `GradedDMPDependencyOrder.Stage`, & `OntologyMetaLevel`, `C11`)**:
   Strict acyclicity of `DrazinEpistemicStage.causalEdge` (`E0 → E5`), incomparability of the
   Drazin and Moore–Penrose branches in `GradedDMPDependencyOrder.Stage`
   (`inverse_branches_incomparable`), and strict acyclicity of `OntologyMetaLevel.instantiatesEdge`.
2. **Movement I (Triple-Root Equivalence, Uniqueness, Clabject Individuation, Binary Cut, & Cladistic Fork, `C1`–`C3`)**:
   `Singular.Drazin.IsDrazinInverse ↔ Canonical.Drazin.IsDrazinInverse`,
   `QuantumContext.Drazin.IsDrazinInverse ↔ Canonical.Drazin.IsDrazinInverse`,
   index-independent uniqueness `b = c`, unique clabject fixed-point decomposition (`∃! parts`),
   `cladeJoin P_D Q_D = 1`, `cladeFork P_D Q_D = invS P_D`, `evenGrade P_D a = a`,
   `fittingRegularPart a b * b = P_D`, and `(fittingNilpotentPart a b) ^ (k + 1) = 0`.
3. **Movement II (Fourfold Peirce Anatomy & Faithful `2 × 2` Coordinate Representation, `C4`)**:
   4-sector decomposition across `P_D`, nilpotent cones `conePlus ^ 2 = 0`, `coneMinus ^ 2 = 0`,
   `peirce11 P_D a = fittingRegularPart a b`, `peirce00 P_D a = fittingNilpotentPart a b`, and
   injectivity of `peirceCoordinateRingHom`.
4. **Movement III (Universal Drazin–Inner-Inverse Sandwich & Malik–Thome Transcendent Function, `C5`)**:
   From `a * m_dag * a = a`, `dmpInverse a b m_dag = dmpOp P_D m_dag`,
   `dualDmpInverse a b m_dag = mpdOp P_D m_dag`,
   `projection a b * m_dag * projection a b = b`,
   `dmpOp - mpdOp = peirceAd P_D m_dag`, `dmpOp * mpdOp - b * b = qgtPlus`,
   `Q_D * (mpdOp * dmpOp) * Q_D = qgtMinus`, `qgtPlus ± qgtMinus = genV / genSig`,
   `Φ * Φ = V`, and `J * J = -V`.
5. **Movement IV (Socratic Aporia, MP Obstruction & Criterion, Shell Cascade, & Meta-Cognitive Tower, `C6`–`C9`)**:
   `idempotencyDefect a = idempotencyDefect (fittingRegularPart a b) + idempotencyDefect (fittingNilpotentPart a b)`,
   `idempotencyDefect (P_D + Φ) = V`, `idempotencyDefect (P_D + J) = -V`, recursive defect tower split,
   `nilpotent_moore_penrose_not_drazin`, `exists_index_iff_commute`, shell clade subsumption,
   strict cascade triangularity `S_m * a * S_s = 0` (`m ≤ s`), core + shell reconstruction of `a`,
   `peirceAdCube P_D X = peirceAd P_D X`, and Grassmannian tangent characterization
   `(P_D * X + X * P_D = X) ↔ oddGrade P_D X = X`.
6. **Movement V (Taxonomic Generalized-Inverse Chain, Rectangular Retract Lift, & Erlangen 2.0 Transport, `C10`)**:
   `IsDrazinInverse p_idem p_idem 1`, `IsCommutingWeakDrazin a b k`, `IsWeakDrazin a b k`,
   rectangular Peirce–Drazin lift `isDrazinInverse_of_retract` at index `k_rect + r_rect + 1`,
   and `RingEquiv` transport `IsDrazinInverse (e a) (e b) k`. -/
theorem drazin_epistemic_solve_et_coagula_master_synthesis
    [StarRing R] {S : Type*} [Ring S] (e : R ≃+* S)
    {m_dim n_dim : Type*} [Fintype m_dim] [DecidableEq m_dim] [Fintype n_dim] [DecidableEq n_dim]
    {K_rect : Matrix n_dim m_dim R} {Q_rect : Matrix m_dim n_dim R}
    (hRetract : Q_rect * K_rect = 1) (T_rect : Matrix n_dim n_dim R)
    (hCommRect : Commute (K_rect * Q_rect) T_rect)
    {D_rect : Matrix m_dim m_dim R} {k_rect r_rect : ℕ}
    (hD_rect : InfoGeometry.QuantumContext.Drazin.IsDrazinInverse (Q_rect * T_rect * K_rect) D_rect k_rect)
    (hN_rect : ((1 - K_rect * Q_rect) * T_rect * (1 - K_rect * Q_rect)) ^ r_rect = 0)
    {a b c m_dag p_idem n_op m_op : R} {k ℓ r m s p q : ℕ}
    (h : IsDrazinInverse a b k)
    (hc : IsDrazinInverse a c ℓ)
    (hInner : a * m_dag * a = a)
    (hp_idem : p_idem * p_idem = p_idem)
    (hMP : IsMoorePenroseInverse n_op m_op)
    (hn_nil : n_op ^ r = 0) (hn_ne : n_op ≠ 0)
    {M : ℕ → R} (hM : PowerMPFamily (fittingNilpotentPart a b) M)
    (hms : m ≤ s) (hpq : p ≤ q) (X Y : R) :
    -- 1. Acyclic Causal Posets (`DrazinEpistemicStage`, `GradedDMPDependencyOrder.Stage`, & `OntologyMetaLevel`):
    ((∀ st : DrazinEpistemicStage, ¬ Relation.TransGen DrazinEpistemicStage.causalEdge st st) ∧
     DrazinEpistemicStage.causalEdge .E0_PrimordialDualRootsAndBinaryCut .E1_FourfoldPeirceAnatomy ∧
     DrazinEpistemicStage.causalEdge .E4_SuperoperatorAndRectangularRetractTower .E5_ErlangenMultilevelMasterCoagulation ∧
     (¬ (Stage.drazin ≤ Stage.penrose) ∧ ¬ (Stage.penrose ≤ Stage.drazin)) ∧
     (∀ L : OntologyMetaLevel, ¬ Relation.TransGen OntologyMetaLevel.instantiatesEdge L L)) ∧
    -- 2. Movement I (Triple-Root Equivalence, Uniqueness, Clabject Individuation, Binary Cut, & Cladistic Fork):
    ((InfoGeometry.Singular.Drazin.IsDrazinInverse a b k ↔
        InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k) ∧
     (InfoGeometry.QuantumContext.Drazin.IsDrazinInverse a b k ↔
        InfoGeometry.Canonical.Drazin.IsDrazinInverse a b k) ∧
     b = c ∧
     (∀ z : R, ∃! parts : R × R,
        parts.1 ∈ projectorSubspace (projection a b) ∧
        parts.2 ∈ projectorSubspace (complementaryProjection a b) ∧
        parts.1 + parts.2 = z) ∧
     cladeJoin (projection a b) (complementaryProjection a b) = 1 ∧
     cladeFork (projection a b) (complementaryProjection a b) = invS (projection a b) ∧
     evenGrade (projection a b) a = a ∧
     oddGrade (projection a b) a = 0 ∧
     fittingRegularPart a b * b = projection a b ∧
     (fittingNilpotentPart a b) ^ (k + 1) = 0) ∧
    -- 3. Movement II (Fourfold Peirce Anatomy & Faithful Coordinate Representation):
    (InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) X +
       conePlus (projection a b) X +
       coneMinus (projection a b) X +
       InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (projection a b) X = X ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 (projection a b) a = fittingRegularPart a b ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 (projection a b) a = fittingNilpotentPart a b ∧
     conePlus (projection a b) X * conePlus (projection a b) Y = 0 ∧
     coneMinus (projection a b) X * coneMinus (projection a b) Y = 0 ∧
     Function.Injective (peirceCoordinateRingHom (projection_is_idempotent h))) ∧
    -- 4. Movement III (Universal Drazin–Inner-Inverse Sandwich & Malik–Thome Transcendent Function):
    (dmpInverse a b m_dag = dmpOp (projection a b) m_dag ∧
     dualDmpInverse a b m_dag = mpdOp (projection a b) m_dag ∧
     projection a b * m_dag * projection a b = b ∧
     dmpOp (projection a b) m_dag - mpdOp (projection a b) m_dag =
       peirceAd (projection a b) m_dag ∧
     dmpOp (projection a b) m_dag * mpdOp (projection a b) m_dag - b * b =
       qgtPlus (projection a b) m_dag m_dag ∧
     complementaryProjection a b *
       (mpdOp (projection a b) m_dag * dmpOp (projection a b) m_dag) *
       complementaryProjection a b =
       qgtMinus (projection a b) m_dag m_dag ∧
     qgtPlus (projection a b) m_dag m_dag + qgtMinus (projection a b) m_dag m_dag =
       genV (projection a b) m_dag m_dag ∧
     qgtPlus (projection a b) m_dag m_dag - qgtMinus (projection a b) m_dag m_dag =
       genSig (projection a b) m_dag m_dag ∧
     genPhi (projection a b) m_dag m_dag * genPhi (projection a b) m_dag m_dag =
       genV (projection a b) m_dag m_dag ∧
     genJ (projection a b) m_dag m_dag * genJ (projection a b) m_dag m_dag =
       -genV (projection a b) m_dag m_dag) ∧
    -- 5. Movement IV (Socratic Aporia, MP Obstruction & Criterion, Shell Cascade, & Meta-Cognitive Tower):
    (idempotencyDefect a =
       idempotencyDefect (fittingRegularPart a b) +
         idempotencyDefect (fittingNilpotentPart a b) ∧
     idempotencyDefect (projection a b + genPhi (projection a b) m_dag m_dag) =
       genV (projection a b) m_dag m_dag ∧
     idempotencyDefect (projection a b + genJ (projection a b) m_dag m_dag) =
       -genV (projection a b) m_dag m_dag ∧
     (∀ n : ℕ,
       idempotencyDefect^[n] (genV (projection a b) m_dag m_dag) =
         idempotencyDefect^[n] (qgtPlus (projection a b) m_dag m_dag) +
           idempotencyDefect^[n] (qgtMinus (projection a b) m_dag m_dag)) ∧
     ¬ IsDrazinInverse n_op m_op k ∧
     ((∃ idx, IsDrazinInverse n_op m_op idx) ↔ n_op * m_op = m_op * n_op) ∧
     cladeSubsumes (drazinShellProj a b M m) (complementaryProjection a b) ∧
     cladeSubsumes (drazinRangeProj a b M q) (drazinRangeProj a b M p) ∧
     drazinShellProj a b M m * a * drazinShellProj a b M s = 0 ∧
     a = projection a b * a * projection a b +
           ∑ idx ∈ Finset.range k,
             drazinShellProj a b M idx * a *
               (∑ r_idx ∈ Finset.range idx, drazinShellProj a b M r_idx) ∧
     peirceAdCube (projection a b) X = peirceAd (projection a b) X ∧
     ((projection a b * X + X * projection a b = X) ↔ oddGrade (projection a b) X = X)) ∧
    -- 6. Movement V (Taxonomic Chain, Rectangular Peirce–Drazin Lift, & Erlangen 2.0 Transport):
    (IsDrazinInverse p_idem p_idem 1 ∧
     IsCommutingWeakDrazin a b k ∧
     IsWeakDrazin a b k ∧
     InfoGeometry.QuantumContext.Drazin.IsDrazinInverse
       T_rect (InfoGeometry.Algebra.RectangularRetract.cornerHom K_rect Q_rect hRetract D_rect)
       (k_rect + r_rect + 1) ∧
     IsDrazinInverse (e a) (e b) k) := by
  have hI := drazin_primordial_dual_roots_and_binary_cut h
  have hII := drazin_fourfold_relational_anatomy h X Y
  have hIII := drazin_transcendent_function_malik_thome h hInner
  have hIV := drazin_socratic_aporia_and_metacognitive_tower
    (m_dag := m_dag) h hMP hn_nil hn_ne hM hms hpq X
  have hWeak : IsWeakDrazin a b k := Drazin_isWeakDrazin h
  have hCommWeak : IsCommutingWeakDrazin a b k := ⟨hWeak, h.comm⟩
  exact ⟨⟨DrazinEpistemicStage.causalEdge_acyclic, by decide, by decide,
          inverse_branches_incomparable,
          OntologyMetaLevel.instantiatesEdge_acyclic⟩,
         ⟨singular_iff_canonical_drazin a b k,
          quantumContext_iff_canonical_drazin a b k,
          unique_of_indices h hc,
          hI.2.1.2.2,
          hI.1.1, hI.1.2.1, hI.2.2.1.1, hI.2.2.1.2.1,
          hI.2.2.2.2.1, hI.2.2.2.2.2.2.2.2⟩,
         ⟨hII.1, hII.2.1.1, hII.2.1.2.1, hII.2.2.1.1, hII.2.2.1.2, hII.2.2.2.2.1⟩,
         ⟨hIII.1.1, hIII.1.2.1, hIII.1.2.2, hIII.2.2.1.1, hIII.2.2.2.1, hIII.2.2.2.2.1,
          hIII.2.2.2.2.2.1, hIII.2.2.2.2.2.2.1, hIII.2.2.2.2.2.2.2.1, hIII.2.2.2.2.2.2.2.2.1⟩,
         ⟨hIV.1.2.2, hIV.2.1.1, hIV.2.1.2.1, hIV.2.2.1, hIV.2.2.2.2.1,
          hIV.2.2.2.2.2.1, hIV.2.2.2.2.2.2.1, hIV.2.2.2.2.2.2.2.2.1,
          hIV.2.2.2.2.2.2.2.2.2.1, hIV.2.2.2.2.2.2.2.2.2.2,
          hIV.2.2.2.1.1, hIV.2.2.2.1.2.2.2⟩,
         ⟨of_idempotent hp_idem, hCommWeak, hWeak,
          isDrazinInverse_of_retract hRetract T_rect hCommRect hD_rect hN_rect,
          map_ringEquiv e h⟩⟩

end InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.EmergentSpacetimeSuperchargeCartanTransactionSynthesis
import InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
import InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
import InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis
import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron
import InfoGeometry.Projective.MatrixPluckerPositiveBridge
import InfoGeometry.Canonical.PositivePluckerFisherBridge
import InfoGeometry.Canonical.AmplituhedronDifferentialResidue
import InfoGeometry.Canonical.BMSSymmetrySoftHairBridge
import InfoGeometry.Canonical.CelestialMellinCapstone

/-!
# Frontier 109 (Wave 13): Finite Supercolor, Positive-Grassmannian, and Information-Geometric Identities

This file packages selected finite theorems from separate owner modules: bi-graded sign laws,
linear carrier maps, scalar Maurer–Cartan jet identities, finite matrix-chart identities, reciprocal
channel and logarithmic-scale identities, a determinant-like expression on split sedenions, a
finite celestial charge model, algebraic shear/readout identities, and Fisher quadratic forms.
The package does not identify these separate carriers through a common map, assert geometric
realizations such as an associahedron or cosmological polytope, construct analytic differential
forms or holonomy, or prove physical scattering-amplitude identities.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.AmplituhedronBeyondHorizonsGrandSynthesis

open scoped Matrix BigOperators
open Finset Matrix Real
open InfoGeometry.Synthesis.EmergentSpacetimeSuperchargeCartanTransactionSynthesis
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
open InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis
open InfoGeometry.Synthesis.Cl55TwistorSplitSedenionColorBridge
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Canonical
open InfoGeometry.Canonical.AmplituhedronResidue
open InfoGeometry.Canonical.PositivePluckerFisherBridge
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge
open InfoGeometry.Quantum.CelestialMellin
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Canonical.ChiralCausalConeFlow
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Lie.CanonicalZornDerivationDimension

/-!
## Section 1: Finite Supercolor Signs, Twistor Carrier Maps, Maurer–Cartan Jets, and Reciprocal Densities
-/

/-- Explicit non-commutativity witness on the $2 \times 2$ real matrix carrier (`T16`). -/
theorem amplituhedron_synthesis_matrix2_ne_comm :
    spinCurrentPlus2 * spinCurrentMinus2 ≠ spinCurrentMinus2 * spinCurrentPlus2 :=
  spinCurrentPlus2_mul_spinCurrentMinus2_ne_comm

/-- **Theorem 1.1 (`finite_supercolor_twistor_jet_and_reciprocal_density_laws`)**:
Packages selected finite algebraic identities from their respective owners:
1. **$\mathbb{Z}_2 \times \mathbb{Z}_2$ Koszul Supercolor Parastatistics**:
   The quark–quark exchange sign is `+1`, the lepton–lepton exchange sign is `-1`,
   and the quark–lepton exchange sign is `-1`, as recorded by the corresponding
   `z2z2KoszulSign` values. These are sign-factor identities, not relations between
   algebra generators.
2. **Twistor / Split-Sedenion Carrier Equivalence**:
   `twistor55SplitSedenionEquiv` is an exact bijection `Twistor55 ℝ ≃ SplitSedenion ℝ`;
   the conclusion below records its inverse law and additivity. No Günaydin–Gürsey coordinate
   decomposition or dimension statement is part of this theorem.
3. **Scalar Maurer–Cartan Jet Identities**:
   For any flat 5-graded Maurer–Cartan jet `J_mc` with vanishing contact bracket (`J_mc.br_m2_p2 = 0`),
   the finite jet components satisfy `gradeM1CovariantSpinDerivative J_mc = -J_mc.br_p1_m2`
   and `grade0SpinConnectionCurvature J_mc = -J_mc.br_m1_p1`. These are scalar jet equations,
   not differential forms or a soldered connection.
4. **Finite Reciprocal-Density Factorization**:
   For any positive cell coordinates $\alpha : \mathrm{Fin}\, d \to \mathbb{R}$ ($\alpha_i > 0$),
   the reciprocal product is positive and removing one factor gives the algebraic identity
   `α i * cellVolumeDensity α = poincareResidueDensity α i`. This is not an analytic boundary
   residue or differential form. -/
theorem finite_supercolor_twistor_jet_and_reciprocal_density_laws
    {d : ℕ} (Z W : Twistor55 ℝ)
    (J_mc : FiveGradedMaurerCartanJet ℝ)
    (α : Fin d → ℝ) (i : Fin d)
    (h_flat : mcCurvatureTower J_mc = (0, 0, 0, 0, 0))
    (h_contact : J_mc.br_m2_p2 = 0)
    (hα_pos : ∀ j : Fin d, 0 < α j) :
    (z2z2KoszulSign gradeQuark gradeQuark = 1 ∧
     z2z2KoszulSign gradeLepton gradeLepton = -1 ∧
     z2z2KoszulSign gradeQuark gradeLepton = -1) ∧
    (twistor55SplitSedenionEquiv.symm (twistor55SplitSedenionEquiv Z) = Z ∧
     twistor55ToSplitSedenion (Z + W) =
       sedenionAdd (twistor55ToSplitSedenion Z) (twistor55ToSplitSedenion W)) ∧
    (gradeM1CovariantSpinDerivative J_mc = -J_mc.br_p1_m2 ∧
     grade0SpinConnectionCurvature J_mc = -J_mc.br_m1_p1) ∧
    (0 < cellVolumeDensity α ∧
     cellVolumeDensity α = dlogDensity (α i) * poincareResidueDensity α i ∧
     α i * cellVolumeDensity α = poincareResidueDensity α i) := by
  have h_signs := z2z2_color_supersymmetry_sign_laws gradeQuark gradeLepton
  have h_mc := maurer_cartan_spin_and_spin_connection_unification J_mc h_flat h_contact
  have hαi_ne : α i ≠ 0 := ne_of_gt (hα_pos i)
  refine ⟨⟨h_signs.2.2.2.2.2, h_signs.2.2.2.2.1, h_signs.2.2.2.1⟩,
    ⟨twistor55SplitSedenionEquiv.left_inv Z, twistor55ToSplitSedenion_add Z W⟩,
    ⟨h_mc.2.1.1, h_mc.1.2⟩,
    ⟨cellVolumeDensity_pos α hα_pos,
     cell_density_residue_factorization α i,
     bcfw_boundary_residue_cancellation α i hαi_ne⟩⟩

/-!
## Section 2: The Positive Grassmannian $\mathrm{Gr}_+(k, n)$, the Linear Amplituhedron Map $Y = C Z$, & the $\mathrm{Gr}(2,4)$ Plücker–Klein Syzygy
-/

/-- **Theorem 2.1 (`positive_grassmannian_amplituhedron_and_plucker_klein_laws`)**:
Packages the finite matrix-chart laws of the Positive Grassmannian and the Amplituhedron map
from `InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron` and
`InfoGeometry.Projective.MatrixPluckerPositiveBridge`:
The dimension hypothesis `k ≤ n` ensures that the maximal-minor selector type is nonempty.
1. **$\mathrm{GL}_+(k)$ Minor Equivariance & Positive Interior Preservation**:
   Left multiplication by $A \in M_k(\mathbb{R})$ scales every maximal minor by $\det A$
   (`maximalMinor (A * C) s = det A * maximalMinor C s`), preserving `positiveGrassmannianInterior`
   whenever $\det A > 0$.
2. **Linear Amplituhedron Map Equivariance ($Y = C Z$)**:
   The amplituhedron map `amplituhedronMap Z C = C * Z` is equivariant under left $\mathrm{GL}(k)$
   row operations (`amplituhedronMap Z (A * C) = A * amplituhedronMap Z C`) and right kinematic
   transformations (`amplituhedronMap (Z * B) C = amplituhedronMap Z C * B`), and maps
   `positiveGrassmannianChart` into `amplituhedronImage Z`.
3. **Zero-Column Chart Classification**:
   For $2 \le n$ and any $C \in M_{2 \times n}(\mathbb{R})$ with nonnegative $2 \times 2$ minors,
   appending a zero column keeps `appendZeroColumn₂ C` in the nonnegative chart and outside
   `positiveGrassmannianInterior`. This states chart membership and failure of strict positivity,
   not topological boundary or facet structure.
4. **Exact $\mathrm{Gr}(2,4)$ Plücker–Klein Quadratic Syzygy**:
   For any $M \in M_{2 \times 4}(\mathbb{R})$, its six ordered $2 \times 2$ Plücker minors satisfy
   $\Delta_{01}\Delta_{23} - \Delta_{02}\Delta_{13} + \Delta_{03}\Delta_{12} = 0$. -/
theorem positive_grassmannian_amplituhedron_and_plucker_klein_laws
    {k n m : ℕ} (hkn : k ≤ n) (hn₂ : 2 ≤ n)
    (A : Matrix (Fin k) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    (s : Fin k → Fin n)
    (C₂ : Matrix (Fin 2) (Fin n) ℝ)
    (M₂₄ : Matrix2x4)
    (hA : 0 < Matrix.det A)
    (hC_pos : C ∈ positiveGrassmannianInterior (k := k) (n := n))
    (hC₂_nonneg : HasNonnegativeMaximalMinors C₂) :
    (maximalMinor (A * C) s = Matrix.det A * maximalMinor C s ∧
     A * C ∈ positiveGrassmannianInterior (k := k) (n := n)) ∧
    (amplituhedronMap Z (A * C) = A * amplituhedronMap Z C ∧
     amplituhedronMap (Z * B) C = amplituhedronMap Z C * B ∧
     amplituhedronMap Z C ∈ amplituhedronImage (k := k) (n := n) (m := m) Z) ∧
    (appendZeroColumn₂ C₂ ∈ positiveGrassmannianChart (k := 2) (n := n + 1) ∧
     appendZeroColumn₂ C₂ ∉ positiveGrassmannianInterior (k := 2) (n := n + 1)) ∧
    (matrixPluckerCoords M₂₄ 0 * matrixPluckerCoords M₂₄ 5 -
     matrixPluckerCoords M₂₄ 1 * matrixPluckerCoords M₂₄ 4 +
     matrixPluckerCoords M₂₄ 2 * matrixPluckerCoords M₂₄ 3 = 0) := by
  have _selector_nonempty : ∃ s : Fin k → Fin n, StrictMono s := by
    refine ⟨fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩, ?_⟩
    intro i j hij
    exact hij
  have hC_chart : C ∈ positiveGrassmannianChart (k := k) (n := n) :=
    positiveGrassmannianInterior_subset_chart hC_pos
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn₂
  refine ⟨⟨maximalMinor_left_mul A C s, positiveGrassmannianInterior_left_mul A C hA hC_pos⟩,
    ⟨amplituhedronMap_left_mul Z A C,
     amplituhedronMap_right_mul Z B C,
     amplituhedronMap_mem_image Z C hC_chart⟩,
    appendZeroColumn₂_boundary_classification n hn C₂ hC₂_nonneg,
    matrixPluckerCoords_klein_relation M₂₄⟩

/-!
## Section 3: Reciprocal-Channel and Logarithmic-Scale Identities
-/

/-- A scalar sum of two reciprocal channel variables. This definition does not
encode a polytope or an amplitude map. -/
def fourPointReciprocalChannelSum (s t : ℝ) : ℝ :=
  s⁻¹ + t⁻¹

/-- Logarithmic ratio coordinate $\tau(t_0, t) := \ln(t / t_0)$. -/
def logarithmicScaleCoordinate (t₀ t : ℝ) : ℝ :=
  Real.log (t / t₀)

/-- **Theorem 3.1 (`reciprocal_channel_and_logarithmic_scale_laws`)**:
1. **Reciprocal-Channel Algebra**:
   For positive real variables `s` and `t`,
   $$\frac{1}{s} + \frac{1}{t} = \frac{s + t}{s t} = (s + t) \cdot s^{-1} t^{-1}.$$
2. **Positivity and Reciprocal Cancellation**:
   The reciprocal sum is positive and multiplication by either positive variable gives the
   corresponding cancellation identity below.
3. **Logarithmic-Ratio Scale Law**:
   For `t₀ ≠ 0`, `time_t ≠ 0`, and `lam > 0`,
   $$\tau(t_0, \lambda t) - \tau(t_0, t) = \ln \lambda, \qquad \tau(t_0, t_0) = 0.$$ -/
theorem reciprocal_channel_and_logarithmic_scale_laws
    (s t t₀ time_t lam : ℝ)
    (hs : 0 < s) (ht : 0 < t)
    (ht₀ : t₀ ≠ 0) (htime : time_t ≠ 0) (hlam : 0 < lam) :
    (fourPointReciprocalChannelSum s t = (s + t) * (s⁻¹ * t⁻¹)) ∧
    (0 < fourPointReciprocalChannelSum s t) ∧
    (s * fourPointReciprocalChannelSum s t = 1 + s * t⁻¹ ∧
     t * fourPointReciprocalChannelSum s t = 1 + t * s⁻¹) ∧
    (logarithmicScaleCoordinate t₀ t₀ = 0 ∧
     logarithmicScaleCoordinate t₀ (lam * time_t) - logarithmicScaleCoordinate t₀ time_t =
       Real.log lam) := by
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have h_quot_ne : time_t / t₀ ≠ 0 := div_ne_zero htime ht₀
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · dsimp [fourPointReciprocalChannelSum]
    field_simp [hs_ne, ht_ne]
    ring
  · dsimp [fourPointReciprocalChannelSum]
    exact add_pos (inv_pos.mpr hs) (inv_pos.mpr ht)
  · dsimp [fourPointReciprocalChannelSum]
    rw [mul_add, mul_inv_cancel₀ hs_ne]
  · dsimp [fourPointReciprocalChannelSum]
    rw [mul_add, mul_inv_cancel₀ ht_ne, add_comm]
  · dsimp [logarithmicScaleCoordinate]
    rw [div_self ht₀, Real.log_one]
  · dsimp [logarithmicScaleCoordinate]
    have h_div : (lam * time_t) / t₀ = lam * (time_t / t₀) := mul_div_assoc lam time_t t₀
    rw [h_div, Real.log_mul hlam_ne h_quot_ne]
    ring

/-!
## Section 4: Split-Sedenion Associator, Zero Divisors, and a Formal $A D - B C$ Expression
-/

/-- Determinant-like expression $A D - B C$ defined using the split-sedenion
product. It is not asserted to be a determinant or Plücker coordinate. -/
def sedenionFormalMinor2x2 (A B C D : SplitSedenion ℝ) : SplitSedenion ℝ :=
  sedenionSub (sedenionMul A D) (sedenionMul B C)

/-- **Theorem 4.1 (`splitSedenion_nonassoc_zero_divisor_formal_minor_and_derivation_tangent`)**:
Records finite facts about the Cayley–Dickson split-sedenion carrier
`SplitSedenion ℝ = ZornSplitOctonion ℝ × ZornSplitOctonion ℝ`:
1. **Failure of Associativity**:
   `sedenionMul` has a non-vanishing associator:
   $\exists X, Y, Z \in \mathrm{SplitSedenion}\, \mathbb{R},\; (X \circ Y) \circ Z \neq X \circ (Y \circ Z)$.
2. **A Formal $A D - B C$ Expression Vanishes on a Zero-Divisor Pair**:
   The explicit non-zero Peirce zero-divisor pair
   $X_{\mathrm{zd}} = (e_0, 0) \neq 0$ and $Y_{\mathrm{zd}} = (e_1, 0) \neq 0$ satisfies
   $X_{\mathrm{zd}} \circ Y_{\mathrm{zd}} = (0, 0)$, so the defined expression
   `sedenionFormalMinor2x2 X_zd 0 0 Y_zd` vanishes. This does not assert any
   determinant theory, Plücker coordinates, or failure of Plücker relations.
3. **Linearized Product Identity for a Derivation**:
   For every 14-parameter $G_2$ derivation `sedenionG2Derivation p` ($p \in \mathrm{Params}$)
   and any split-sedenion zero-divisor pair $(X, Y)$ satisfying `sedenionMul X Y = sedenionZero`,
   the derivation law yields the first-order product identity:
   $$(D_p X) \circ Y + X \circ (D_p Y) = (0, 0),$$
   and `sedenionG2Derivation` is injective on the 14-dimensional parameter space `Params`. -/
theorem splitSedenion_nonassoc_zero_divisor_formal_minor_and_derivation_tangent
    (p : Params) (X Y : SplitSedenion ℝ)
    (h_zd : sedenionMul X Y = sedenionZero) :
    (∃ A B C : SplitSedenion ℝ,
       sedenionMul (sedenionMul A B) C ≠ sedenionMul A (sedenionMul B C)) ∧
    (((zornE0 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ)) ≠ sedenionZero ∧
     ((zornE1 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ)) ≠ sedenionZero ∧
     sedenionFormalMinor2x2
       ((zornE0 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ))
       sedenionZero sedenionZero
       ((zornE1 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ)) = sedenionZero) ∧
    (sedenionAdd
       (sedenionMul (sedenionG2Derivation p X) Y)
       (sedenionMul X (sedenionG2Derivation p Y)) = sedenionZero ∧
     Function.Injective sedenionG2Derivation) := by
  have h_nonassoc := cl44_associative_vs_splitSedenion_nonAssociative.2
  have h_peirce := splitSedenion_explicit_zero_divisors_and_null_norm
  have h_zero_mul_zero : sedenionMul (sedenionZero : SplitSedenion ℝ) sedenionZero = sedenionZero := by
    change sedenionMul ((zornZero : ZornSplitOctonion ℝ), zornZero) (zornZero, zornZero) =
      (zornZero, zornZero)
    rw [(splitSedenion_chiral_sheet_shift_laws (zornZero : ZornSplitOctonion ℝ) zornZero).1,
        zornZero_mul]
  have h_sub_zero : sedenionSub (sedenionZero : SplitSedenion ℝ) sedenionZero = sedenionZero := by
    apply Prod.ext <;> (ext k <;> try fin_cases k) <;>
      simp [sedenionSub, sedenionAdd, sedenionNeg, sedenionZero, zornZero, zornAdd, zornSmul]
  have h_minor :
      sedenionFormalMinor2x2
        ((zornE0 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ))
        sedenionZero sedenionZero
        ((zornE1 : ZornSplitOctonion ℝ), (zornZero : ZornSplitOctonion ℝ)) = sedenionZero := by
    dsimp [sedenionFormalMinor2x2]
    rw [h_peirce.1, h_zero_mul_zero, h_sub_zero]
  have h_leibniz := sedenionG2Derivation_leibniz p X Y
  have h_der_zero : sedenionG2Derivation p sedenionZero = sedenionZero :=
    Prod.ext (zornG2Derivation_zornZero p) (zornG2Derivation_zornZero p)
  have h_tangent :
      sedenionAdd
        (sedenionMul (sedenionG2Derivation p X) Y)
        (sedenionMul X (sedenionG2Derivation p Y)) = sedenionZero := by
    rw [← h_leibniz, h_zd, h_der_zero]
  exact ⟨h_nonassoc, ⟨h_peirce.2.1, h_peirce.2.2.1, h_minor⟩,
    ⟨h_tangent, sedenionG2Derivation_injective⟩⟩

/-!
## Section 5: Finite Celestial Charge, Algebraic Shear Readout, and Fisher Quadratic Identities
-/

/-- **Theorem 5.1 (`celestial_charge_shear_readout_and_fisher_souriau_laws`)**:
Packages finite identities from the celestial charge, shear/readout, and Fisher owners:
1. **Finite Celestial Weight and Charge Additivity**:
   For any $\lambda \in \mathbb{R}$ and frequency $\omega > 0$, the celestial conformal weight
   `celestialWeight lambda` lies on the critical line $\operatorname{Re}(\Delta) = 1/2$ with
   unit Mellin phase norm $\| \omega^{-i\lambda} e^{-i E \ln \omega} \| = 1$, and the discrete
   The BMS charge is the finite weighted-sum model in `BMSSymmetry.CelestialSphere` and is additive
   in its profile argument.
2. **Unipotent Shear and Residue-Readout Composition**:
   For any non-zero shear parameter $p \in \mathbb{C}$ ($p \neq 0$) and conformal weight $h \in \mathbb{C}$,
   the chiral lightcone unipotent shear `unipotentChiralShear p = 1 + p • Splus` preserves the
   $3+1\mathrm{D}$ lightcone determinant $\det(U(p)\,\mathrm{chiralMatrix}(X)) = Q(X)$ while its
   matrix determinant identity and $U(p)^2 = U(2p)$ hold; the rank-two residue-readout
   composition is non-identity. This is an algebraic readout identity, not analytic holonomy or
   a braid-group monodromy theorem.
3. **Finite Plücker Fisher Quadratic and Souriau–Massieu Variance**:
   For any $M \in \mathrm{positiveGrassmannianInterior}(2, 4)$, its normalized squared Plücker
   sector probabilities satisfy nonnegativity of the quadratic form for every supplied vector
   `v` (no tangent-space restriction is asserted), and the square-root amplitude lies on the
   radius-2 sphere. The finite Fisher–Souriau Hessian form equals a nonnegative variance. -/
theorem celestial_charge_shear_readout_and_fisher_souriau_laws
    {m : ℕ} [Nonempty (Fin m)]
    (E lambda omega : ℝ) (h_omega : 0 < omega)
    (S : BMSSymmetry.CelestialSphere (Fin m)) (f1 f2 T_vv : Fin m → ℝ)
    (p h : ℂ) (hp : p ≠ 0) (X_chiral : Chiral3)
    (M : PluckerMatrix)
    (hM : M ∈ positiveGrassmannianInterior (k := 2) (n := 4))
    (v_plucker : Fin 6 → ℝ)
    (s δs : Fin m → ℝ) :
    ((celestialWeight lambda).re = 1 / 2 ∧
     ‖mellinScaleFreePhase E lambda omega‖ = 1 ∧
     S.bmsCharge (fun i => f1 i + f2 i) T_vv =
       S.bmsCharge f1 T_vv + S.bmsCharge f2 T_vv) ∧
    (Matrix.det (unipotentChiralShear p * chiralMatrix X_chiral) =
       (lightconePotential X_chiral : ℂ) ∧
     unipotentChiralShear p * unipotentChiralShear p = unipotentChiralShear (2 * p) ∧
     unipotentChiralShear p * unipotentChiralShear p ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
     (unipotentResidueReadout (rankTwoLogResidue h) p).comp
       (unipotentResidueReadout (rankTwoLogResidue h) p) ≠ LinearMap.id) ∧
    (0 ≤ pluckerFisherPair M hM v_plucker v_plucker ∧
     ∑ i : Fin 6, ((pluckerStrictProbability M hM).twoSqrtAmplitude i) ^ 2 = 4 ∧
     (∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k =
        ∑ j : Fin m, souriauAttentionWeight s j * (δs j - souriauMomentMap s δs) ^ 2) ∧
     0 ≤ ∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k) := by
  have h_cel := InfoGeometry.Canonical.CelestialMellinCapstone.verification_capstone E lambda omega h_omega
  have h_shear := unipotentChiralShear_mul_and_det p p h X_chiral ![0, 1]
  have h_double := unipotentChiralShear_double_ne_one p hp
  have h_rank2 := rankTwo_unipotentResidueReadout_double_ne_id h p hp
  have h_fs := fisherSouriau_quadratic_eq_variance_and_nonneg s δs
  refine ⟨⟨h_cel.1, h_cel.2.2.1, S.bms_charge_add f1 f2 T_vv⟩,
    ⟨h_shear.2.2.1, h_double.1, h_double.2, h_rank2⟩,
    ⟨pluckerFisherPair_nonneg M hM v_plucker,
     plucker_sqrt_amplitude_sphere M hM,
     h_fs.1, h_fs.2⟩⟩

end InfoGeometry.Synthesis.AmplituhedronBeyondHorizonsGrandSynthesis

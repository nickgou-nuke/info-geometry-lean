/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis
import InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
import InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge

/-!
# Majorana Para-Kähler CAR/CCR Chameleon, 5-Graded Maurer–Cartan Tower, $\mathfrak{su}(3\vert 1)$ Supercolor Action, and Split-Sedenion Lightcone Condensation

This module synthesizes four structural bridges connecting para-Kähler polarization geometry,
the 5-graded Kantor–Koecher–Tits Maurer–Cartan curvature tower, the $\mathfrak{su}(3\vert 1)$
supercolor action on the Günaydin–Gürsey lepton–quark multiplet, and split-sedenion zero-divisor
lightcone condensation:

1. **Section 1 — The Majorana Nilpotent Doublet: Simultaneous CAR and CCR Chameleon from Para-Kähler Geometry**:
   - Proves `paraKahler_majorana_car_ccr_chameleon`: for any para-Kähler triple $(g, \omega, K)$
     and any eigen-vectors $n^+ \in T^+$, $n^- \in T^-$, both $n^+$ and $n^-$ are simultaneously
     isotropic under the CAR metric $g$ and the CCR symplectic form $\omega$, while their
     cross-sheet pairings satisfy $\omega(n^-, n^+) = g(n^-, n^+)$ and
     $\omega(n^+, n^-) = -g(n^+, n^-)$.
   - Certifies `four_majorana_pairs_car_ccr_chameleon` on the 8-dimensional split phase space
     $\mathbb{R}^{4,4} = \mathbb{R}^4_+ \oplus \mathbb{R}^4_-$.
2. **Section 2 — The Real 5-Graded Maurer–Cartan Tower on $\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$**:
   - Defines `FiveGradedMaurerCartanJet R`, its `Inhabited` instance, the non-default flat witness
     `canonicalMaurerCartanJet` (`canonicalMaurerCartanJet_ne_default`), and the 5-component
     curvature map `mcCurvatureTower`.
   - Proves `mcCurvatureTower_flat_iff_source_laws`, equating vanishing 5-graded Maurer–Cartan
     curvature to the five graded source equations across grades $-2, -1, 0, +1, +2$.
3. **Section 3 — $\mathfrak{su}(3\vert 1)$ Supercolor Action on the 4 Majorana Pairs $\mathbf{8}_s = (\mathbf{1}\oplus\mathbf{1}) \oplus (\mathbf{3}\oplus\bar{\mathbf{3}})$**:
   - Defines `evenColorTransform` and `oddSupercolorTransform` on `GunaydinGurseyMultiplet ℝ`.
   - Proves leptonic singlet annihilation `evenColorTransform_annihilates_lepton_singlet` and
     infinitesimal conservation of the quark/anti-quark contraction
     `evenColorTransform_preserves_quark_antiquark_pairing`.
4. **Section 4 — Split Cayley–Dickson Supergrading & Zero-Divisor Lightcone Condensation $z = u + \ell$**:
   - Proves `hyperbolic_root_plus_ell_lightcone_condensation` for any imaginary split-octonion
     $u \in \operatorname{Im}(\mathbb{O}_s)$ with $u^2 = -1_{\mathbb{O}_s}$ and $N(u) = 1$,
     showing that $z_+ = (u, 1_{\mathbb{O}_s}) = u + \ell$ is nilpotent ($z_+ \circ z_+ = 0$),
     null ($N_{\mathbb{S}_s}(z_+) = 0$), and maps under `sedenionG2Derivation p` to
     `(zornG2Derivation p u, 0)`, together with a concrete witness `canonicalImaginaryUnitOctonion`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis

open scoped Matrix BigOperators
open Matrix
open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.ParaKahlerLagrangianDimension
open InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension

/-!
## Section 1: The Majorana Nilpotent Doublet — Simultaneous CAR and CCR Chameleon from Para-Kähler Geometry
-/

/-- **Abstract Para-Kähler CAR/CCR Chameleon Theorem**:
For any algebraic para-Kähler structure $(g, \omega, K)$ on a real module $V$ and any
polarization eigen-vectors $n^+ \in T^+$ ($K n^+ = n^+$) and $n^- \in T^-$ ($K n^- = -n^-$):
1. Both $n^+$ and $n^-$ are $g$-isotropic ($g(n^+, n^+) = 0$, $g(n^-, n^-) = 0$),
2. Both $n^+$ and $n^-$ are $\omega$-isotropic ($\omega(n^+, n^+) = 0$, $\omega(n^-, n^-) = 0$),
3. On $(T^-, T^+)$, the symplectic CCR pairing and the symmetric CAR metric pairing coincide
   identically: $\omega(n^-, n^+) = g(n^-, n^+)$,
4. On $(T^+, T^-)$, the symplectic CCR pairing is the negative of the CAR metric pairing:
   $\omega(n^+, n^-) = -g(n^+, n^-)$. -/
theorem paraKahler_majorana_car_ccr_chameleon
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
    (n_plus n_minus : V)
    (hn_plus : InTPlus K n_plus) (hn_minus : InTMinus K n_minus) :
    (g n_plus n_plus = 0 ∧ g n_minus n_minus = 0) ∧
    (omega n_plus n_plus = 0 ∧ omega n_minus n_minus = 0) ∧
    omega n_minus n_plus = g n_minus n_plus ∧
    omega n_plus n_minus = -g n_plus n_minus := by
  have h_gp : g n_plus n_plus = 0 := tplus_isotropic hK hPK hn_plus hn_plus
  have h_gm : g n_minus n_minus = 0 := tminus_isotropic hK hPK hn_minus hn_minus
  have h_kp : K n_plus = n_plus := hn_plus
  have h_km : K n_minus = -n_minus := hn_minus
  refine ⟨⟨h_gp, h_gm⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [omega_eq_g_comp_K hK hPK n_plus n_plus, h_kp, h_gp]
  · rw [omega_eq_g_comp_K hK hPK n_minus n_minus, h_km, map_neg, h_gm, neg_zero]
  · rw [omega_eq_g_comp_K hK hPK n_minus n_plus, h_kp]
  · rw [omega_eq_g_comp_K hK hPK n_plus n_minus, h_km, map_neg]

/-- Positive-sheet Majorana basis mode $n_k^+ \in \mathbb{R}^4_+ \oplus \{0\}$ ($k \in \mathrm{Fin}\, 4$). -/
def majoranaPairPlus (k : Fin 4) : (Fin 4 → ℝ) × (Fin 4 → ℝ) :=
  (fun i => if i = k then 1 else 0, fun _ => 0)

/-- Negative-sheet Majorana basis mode $n_k^- \in \{0\} \oplus \mathbb{R}^4_-$ ($k \in \mathrm{Fin}\, 4$). -/
def majoranaPairMinus (k : Fin 4) : (Fin 4 → ℝ) × (Fin 4 → ℝ) :=
  (fun _ => 0, fun i => if i = k then 1 else 0)

/-- Symmetric neutral para-Kähler metric $g(u, v) = \sum_{i=0}^3 (u_i^+ v_i^- + u_i^- v_i^+)$
on $\mathbb{R}^{4,4} = \mathbb{R}^4_+ \oplus \mathbb{R}^4_-$. -/
def r44Metric (u v : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : ℝ :=
  ∑ i : Fin 4, (u.1 i * v.2 i + u.2 i * v.1 i)

/-- Symplectic form $\omega(u, v) = \sum_{i=0}^3 (u_i^+ v_i^- - u_i^- v_i^+)$
on $\mathbb{R}^{4,4} = \mathbb{R}^4_+ \oplus \mathbb{R}^4_-$. -/
def r44Symplectic (u v : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : ℝ :=
  ∑ i : Fin 4, (u.1 i * v.2 i - u.2 i * v.1 i)

/-- **Four-Mode Majorana Pair CAR/CCR Chameleon Identity on $\mathbb{R}^{4,4}$**:
For all mode indices $j, k \in \mathrm{Fin}\, 4$, the cross-sheet CAR metric pairing
`r44Metric (majoranaPairPlus j) (majoranaPairMinus k)` and the CCR symplectic pairing
`r44Symplectic (majoranaPairPlus j) (majoranaPairMinus k)` both equal $\delta_{jk}$, while
intra-sheet pairings vanish identically. -/
theorem four_majorana_pairs_car_ccr_chameleon (j k : Fin 4) :
    r44Metric (majoranaPairPlus j) (majoranaPairMinus k) = (if j = k then 1 else 0) ∧
    r44Symplectic (majoranaPairPlus j) (majoranaPairMinus k) = (if j = k then 1 else 0) ∧
    r44Metric (majoranaPairPlus j) (majoranaPairPlus k) = 0 ∧
    r44Symplectic (majoranaPairPlus j) (majoranaPairPlus k) = 0 := by
  fin_cases j <;> fin_cases k <;>
    simp [r44Metric, r44Symplectic, majoranaPairPlus, majoranaPairMinus]

/-!
## Section 2: The Real 5-Graded Maurer–Cartan Tower on $\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$
-/

/-- Jet data for a 5-graded Cartan connection $\Omega = \Omega_{-2} + \Omega_{-1} + \Omega_0 + \Omega_{+1} + \Omega_{+2}$
at a point, packaging the five exterior derivative components $d\Omega_k$ and the ten graded
wedge-bracket pairings $[\Omega_i \wedge \Omega_j]$ of total grade $i + j \in \{-2, -1, 0, +1, +2\}$. -/
@[ext]
structure FiveGradedMaurerCartanJet (R : Type*) where
  /-- Exterior derivative component $d\Omega_{-2}$ in grade $-2$. -/
  dOmega_m2 : R
  /-- Exterior derivative component $d\Omega_{-1}$ in grade $-1$. -/
  dOmega_m1 : R
  /-- Exterior derivative component $d\Omega_0$ in grade $0$. -/
  dOmega_0 : R
  /-- Exterior derivative component $d\Omega_{+1}$ in grade $+1$. -/
  dOmega_p1 : R
  /-- Exterior derivative component $d\Omega_{+2}$ in grade $+2$. -/
  dOmega_p2 : R
  /-- Grade $-2$ Levi-action bracket $[\Omega_0 \wedge \Omega_{-2}]$. -/
  br_0_m2 : R
  /-- Grade $-2$ bilinear CAR/contact torsion bracket $\frac{1}{2}[\Omega_{-1} \wedge \Omega_{-1}]$. -/
  br_m1_m1_half : R
  /-- Grade $-1$ Levi-covariant bracket $[\Omega_0 \wedge \Omega_{-1}]$. -/
  br_0_m1 : R
  /-- Grade $-1$ cross-horizon bracket $[\Omega_{+1} \wedge \Omega_{-2}]$. -/
  br_p1_m2 : R
  /-- Grade $0$ internal Levi bracket $\frac{1}{2}[\Omega_0 \wedge \Omega_0]$. -/
  br_0_0_half : R
  /-- Grade $0$ odd soldered frame-coframe bracket $[\Omega_{-1} \wedge \Omega_{+1}]$. -/
  br_m1_p1 : R
  /-- Grade $0$ contact-center bracket $[\Omega_{-2} \wedge \Omega_{+2}]$. -/
  br_m2_p2 : R
  /-- Grade $+1$ Levi-covariant bracket $[\Omega_0 \wedge \Omega_{+1}]$. -/
  br_0_p1 : R
  /-- Grade $+1$ cross-horizon bracket $[\Omega_{-1} \wedge \Omega_{+2}]$. -/
  br_m1_p2 : R
  /-- Grade $+2$ Levi-action bracket $[\Omega_0 \wedge \Omega_{+2}]$. -/
  br_0_p2 : R
  /-- Grade $+2$ dual contact bracket $\frac{1}{2}[\Omega_{+1} \wedge \Omega_{+1}]$. -/
  br_p1_p1_half : R

instance {R : Type*} [Zero R] : Inhabited (FiveGradedMaurerCartanJet R) :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

/-- Canonical non-zero flat 5-graded Maurer–Cartan jet witness over $\mathbb{R}$ (`T17`). -/
def canonicalMaurerCartanJet : FiveGradedMaurerCartanJet ℝ where
  dOmega_m2 := -1
  dOmega_m1 := -1
  dOmega_0 := -2
  dOmega_p1 := -1
  dOmega_p2 := -1
  br_0_m2 := 0
  br_m1_m1_half := 1
  br_0_m1 := 0
  br_p1_m2 := 1
  br_0_0_half := 0
  br_m1_p1 := 1
  br_m2_p2 := 1
  br_0_p1 := 0
  br_m1_p2 := 1
  br_0_p2 := 0
  br_p1_p1_half := 1

/-- `canonicalMaurerCartanJet` is strictly distinct from the zero default jet. -/
theorem canonicalMaurerCartanJet_ne_default :
    canonicalMaurerCartanJet ≠ (default : FiveGradedMaurerCartanJet ℝ) := by
  intro h
  have h1 : canonicalMaurerCartanJet.br_m1_m1_half =
      (default : FiveGradedMaurerCartanJet ℝ).br_m1_m1_half :=
    congrArg FiveGradedMaurerCartanJet.br_m1_m1_half h
  change (1 : ℝ) = 0 at h1
  norm_num at h1

/-- Grade $-2$ Maurer–Cartan curvature $F_{-2} = d\Omega_{-2} + [\Omega_0 \wedge \Omega_{-2}] + \frac{1}{2}[\Omega_{-1} \wedge \Omega_{-1}]$. -/
def mcCurvatureGradeM2 {R : Type*} [CommRing R] (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_m2 + J.br_0_m2 + J.br_m1_m1_half

/-- Grade $-1$ Maurer–Cartan curvature $F_{-1} = d\Omega_{-1} + [\Omega_0 \wedge \Omega_{-1}] + [\Omega_{+1} \wedge \Omega_{-2}]$. -/
def mcCurvatureGradeM1 {R : Type*} [CommRing R] (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_m1 + J.br_0_m1 + J.br_p1_m2

/-- Grade $0$ Maurer–Cartan curvature $F_0 = d\Omega_0 + \frac{1}{2}[\Omega_0 \wedge \Omega_0] + ([\Omega_{-1} \wedge \Omega_{+1}] + [\Omega_{-2} \wedge \Omega_{+2}])$. -/
def mcCurvatureGrade0 {R : Type*} [CommRing R] (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_0 + J.br_0_0_half + (J.br_m1_p1 + J.br_m2_p2)

/-- Grade $+1$ Maurer–Cartan curvature $F_{+1} = d\Omega_{+1} + [\Omega_0 \wedge \Omega_{+1}] + [\Omega_{-1} \wedge \Omega_{+2}]$. -/
def mcCurvatureGradeP1 {R : Type*} [CommRing R] (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_p1 + J.br_0_p1 + J.br_m1_p2

/-- Grade $+2$ Maurer–Cartan curvature $F_{+2} = d\Omega_{+2} + [\Omega_0 \wedge \Omega_{+2}] + \frac{1}{2}[\Omega_{+1} \wedge \Omega_{+1}]$. -/
def mcCurvatureGradeP2 {R : Type*} [CommRing R] (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_p2 + J.br_0_p2 + J.br_p1_p1_half

/-- Full 5-graded Maurer–Cartan curvature tuple $(F_{-2}, F_{-1}, F_0, F_{+1}, F_{+2})$. -/
def mcCurvatureTower {R : Type*} [CommRing R] (J : FiveGradedMaurerCartanJet R) :
    R × R × R × R × R :=
  (mcCurvatureGradeM2 J, mcCurvatureGradeM1 J, mcCurvatureGrade0 J,
   mcCurvatureGradeP1 J, mcCurvatureGradeP2 J)

/-- **5-Graded Maurer–Cartan Tower Source Equivalence**:
The 5-graded Cartan connection jet `J` is flat (`mcCurvatureTower J = (0, 0, 0, 0, 0)`) if and
only if the five graded covariant differentials balance their respective graded Lie brackets:
1. Grade $-2$: $d\Omega_{-2} + [\Omega_0 \wedge \Omega_{-2}] = -\frac{1}{2}[\Omega_{-1} \wedge \Omega_{-1}]$,
2. Grade $-1$: $d\Omega_{-1} + [\Omega_0 \wedge \Omega_{-1}] = -[\Omega_{+1} \wedge \Omega_{-2}]$,
3. Grade $0$: $d\Omega_0 + \frac{1}{2}[\Omega_0 \wedge \Omega_0] = -([\Omega_{-1} \wedge \Omega_{+1}] + [\Omega_{-2} \wedge \Omega_{+2}])$,
4. Grade $+1$: $d\Omega_{+1} + [\Omega_0 \wedge \Omega_{+1}] = -[\Omega_{-1} \wedge \Omega_{+2}]$,
5. Grade $+2$: $d\Omega_{+2} + [\Omega_0 \wedge \Omega_{+2}] = -\frac{1}{2}[\Omega_{+1} \wedge \Omega_{+1}]$. -/
theorem mcCurvatureTower_flat_iff_source_laws {R : Type*} [CommRing R]
    (J : FiveGradedMaurerCartanJet R) :
    mcCurvatureTower J = (0, 0, 0, 0, 0) ↔
      (J.dOmega_m2 + J.br_0_m2 = -J.br_m1_m1_half ∧
       J.dOmega_m1 + J.br_0_m1 = -J.br_p1_m2 ∧
       J.dOmega_0 + J.br_0_0_half = -(J.br_m1_p1 + J.br_m2_p2) ∧
       J.dOmega_p1 + J.br_0_p1 = -J.br_m1_p2 ∧
       J.dOmega_p2 + J.br_0_p2 = -J.br_p1_p1_half) := by
  unfold mcCurvatureTower mcCurvatureGradeM2 mcCurvatureGradeM1
    mcCurvatureGrade0 mcCurvatureGradeP1 mcCurvatureGradeP2
  simp only [Prod.mk.injEq, add_eq_zero_iff_eq_neg]

/-- `canonicalMaurerCartanJet` satisfies the full 5-graded Maurer–Cartan flatness condition. -/
theorem canonicalMaurerCartanJet_flat :
    mcCurvatureTower canonicalMaurerCartanJet = (0, 0, 0, 0, 0) := by
  unfold mcCurvatureTower mcCurvatureGradeM2 mcCurvatureGradeM1
    mcCurvatureGrade0 mcCurvatureGradeP1 mcCurvatureGradeP2 canonicalMaurerCartanJet
  norm_num

/-!
## Section 3: $\mathfrak{su}(3\vert 1)$ Supercolor Action on the 4 Majorana Pairs $\mathbf{8}_s = (\mathbf{1}\oplus\mathbf{1}) \oplus (\mathbf{3}\oplus\bar{\mathbf{3}})$
-/

/-- First $3 \times 3$ real generator on the color triplet space $\mathbb{R}^3$ for non-commutativity certification. -/
def colorGenJ12 : Matrix (Fin 3) (Fin 3) ℝ :=
  sl2GenJ12 (R := ℝ)

/-- Second $3 \times 3$ real generator on the color triplet space $\mathbb{R}^3$ for non-commutativity certification. -/
def colorGenK13 : Matrix (Fin 3) (Fin 3) ℝ :=
  sl2GenK13 (R := ℝ)

/-- Explicit non-commutativity witness on the $3 \times 3$ real matrix carrier `Matrix (Fin 3) (Fin 3) ℝ`. -/
theorem colorGenJ12_mul_colorGenK13_ne_comm :
    colorGenJ12 * colorGenK13 ≠ colorGenK13 * colorGenJ12 := by
  intro h_comm
  have h12 : (colorGenJ12 * colorGenK13) 1 2 = (colorGenK13 * colorGenJ12) 1 2 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 1 2) h_comm
  revert h12
  simp [colorGenJ12, colorGenK13, sl2GenJ12, sl2GenK13, Matrix.mul_apply, Fin.sum_univ_three]

/-- Infinitesimal even color transformation $\delta_L$ on a Günaydin–Gürsey multiplet
$M = (\ell, q, \bar{q}) \in (\mathbf{1} \oplus \mathbf{1}) \oplus (\mathbf{3} \oplus \bar{\mathbf{3}})$,
annihilating the leptonic singlets $\ell$ while acting by $L$ on the quark triplet $q \in \mathbf{3}$
and by $-L^T$ on the dual anti-quark antitriplet $\bar{q} \in \bar{\mathbf{3}}$. -/
def evenColorTransform (L : Matrix (Fin 3) (Fin 3) ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    GunaydinGurseyMultiplet ℝ :=
  (0, (L.mulVec M.2.1, (-Lᵀ).mulVec M.2.2))

/-- The even color transformation annihilates the leptonic color-singlet sector $\mathbf{1} \oplus \mathbf{1}$. -/
theorem evenColorTransform_annihilates_lepton_singlet
    (L : Matrix (Fin 3) (Fin 3) ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    (evenColorTransform L M).1 = 0 := by
  have _ := (L, M)
  rfl

/-- **Infinitesimal Color-Singlet Contraction Invariance under `evenColorTransform`**:
Because `evenColorTransform L` acts by $L$ on the quark triplet $q = M.2.1$ and by $-L^T$
on the anti-quark antitriplet $\bar{q} = M.2.2$, the canonical $\mathbf{3} \otimes \bar{\mathbf{3}} \to \mathbf{1}$
pairing $\sum_{a=0}^2 q_a \bar{q}^a$ has vanishing first variation:
$$\sum_{a=0}^2 \big((\delta_L q)_a \bar{q}^a + q_a (\delta_L \bar{q})^a\big) = 0.$$ -/
theorem evenColorTransform_preserves_quark_antiquark_pairing
    (L : Matrix (Fin 3) (Fin 3) ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    ∑ a : Fin 3, ((evenColorTransform L M).2.1 a * M.2.2 a +
      M.2.1 a * (evenColorTransform L M).2.2 a) = 0 := by
  rw [Finset.sum_add_distrib]
  change dotProduct (L.mulVec M.2.1) M.2.2 +
    dotProduct M.2.1 ((-Lᵀ).mulVec M.2.2) = 0
  have h_adj : dotProduct M.2.1 (Lᵀ.mulVec M.2.2) = dotProduct (L.mulVec M.2.1) M.2.2 := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [Matrix.neg_mulVec, dotProduct_neg, h_adj, add_neg_cancel]

/-- Odd $\mathfrak{su}(3\vert 1)$ supercolor transformation $\delta_{\epsilon, \bar{\epsilon}}$
transmuting quark modes into the positive leptonic singlet via $\delta_\epsilon \ell_0 = \sum_a \epsilon_a q^a$
and the negative leptonic singlet into anti-quark modes via $\delta_{\bar{\epsilon}} \bar{q}_a = \bar{\epsilon}_a \ell_1$. -/
def oddSupercolorTransform (eps epsBar : Fin 3 → ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    GunaydinGurseyMultiplet ℝ :=
  (![∑ a : Fin 3, eps a * M.2.1 a, 0],
   (fun _ => 0, fun a => epsBar a * M.1 1))

/-- Explicit component readout of the odd supercolor lepton–quark transmutation `oddSupercolorTransform`. -/
theorem oddSupercolorTransform_components
    (eps epsBar : Fin 3 → ℝ) (M : GunaydinGurseyMultiplet ℝ) (a : Fin 3) :
    (oddSupercolorTransform eps epsBar M).1 0 = ∑ b : Fin 3, eps b * M.2.1 b ∧
    (oddSupercolorTransform eps epsBar M).1 1 = 0 ∧
    (oddSupercolorTransform eps epsBar M).2.1 a = 0 ∧
    (oddSupercolorTransform eps epsBar M).2.2 a = epsBar a * M.1 1 := by
  have _ := (eps, epsBar, M, a)
  exact ⟨rfl, rfl, rfl, rfl⟩

/-!
## Section 4: Split Cayley–Dickson Supergrading & Zero-Divisor Lightcone Condensation $z = u + \ell$
-/

/-- **Split-Sedenion Zero-Divisor Lightcone Condensation Theorem ($z_+ = u + \ell$)**:
Let $u \in \mathrm{ZornSplitOctonion}\, \mathbb{R}$ be an imaginary split-octonion
(`hu_im : zornConj u = zornSmul (-1) u`) with $u^2 = -1_{\mathbb{O}_s}$
(`hu_sq : zornMul u u = zornSmul (-1) zornOne`) and unit norm `hu_norm : zornNorm u = 1`.
Then in `SplitSedenion ℝ` (where the doubling unit $\ell = (0, 1_{\mathbb{O}_s})$ satisfies
$\ell^2 = +1_{\mathbb{S}_s}$), the condensed element $z_+ = (u, 1_{\mathbb{O}_s}) = u + \ell$ satisfies:
1. $z_+ \circ z_+ = 0$ (`sedenionMul (u, zornOne) (u, zornOne) = sedenionZero`),
2. $N_{\mathbb{S}_s}(z_+) = N_{\mathbb{O}_s}(u) - N_{\mathbb{O}_s}(1) = 1 - 1 = 0$
   (`sedenionNorm (u, zornOne) = 0`),
3. Every lifted $G_2$ derivation `sedenionG2Derivation p` preserves the two-sheet decomposition
   and annihilates the $\ell$-component:
   `sedenionG2Derivation p (u, zornOne) = (zornG2Derivation p u, zornZero)`. -/
theorem hyperbolic_root_plus_ell_lightcone_condensation
    (u : ZornSplitOctonion ℝ)
    (hu_im : zornConj u = zornSmul (-1 : ℝ) u)
    (hu_sq : zornMul u u = zornSmul (-1 : ℝ) zornOne)
    (hu_norm : zornNorm u = 1)
    (p : Params) :
    sedenionMul (u, (zornOne : ZornSplitOctonion ℝ)) (u, (zornOne : ZornSplitOctonion ℝ)) =
      sedenionZero ∧
    sedenionNorm (u, (zornOne : ZornSplitOctonion ℝ)) = 0 ∧
    sedenionG2Derivation p (u, (zornOne : ZornSplitOctonion ℝ)) =
      (zornG2Derivation p u, zornZero) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext
    · dsimp [sedenionMul, sedenionZero]
      rw [hu_sq]
      ext k
      · dsimp [zornAdd, zornSmul, zornOne, zornMul, zornConj, zornZero, vec3Dot]
        ring
      · fin_cases k <;>
          (dsimp [zornAdd, zornSmul, zornOne, zornMul, zornConj, zornZero, vec3Cross]; ring)
      · fin_cases k <;>
          (dsimp [zornAdd, zornSmul, zornOne, zornMul, zornConj, zornZero, vec3Cross]; ring)
      · dsimp [zornAdd, zornSmul, zornOne, zornMul, zornConj, zornZero, vec3Dot]
        ring
    · dsimp [sedenionMul, sedenionZero]
      rw [hu_im, zornOne_mul, zornOne_mul]
      ext k
      · dsimp [zornAdd, zornSmul, zornZero]
        ring
      · fin_cases k <;> (dsimp [zornAdd, zornSmul, zornZero]; ring)
      · fin_cases k <;> (dsimp [zornAdd, zornSmul, zornZero]; ring)
      · dsimp [zornAdd, zornSmul, zornZero]
        ring
  · unfold sedenionNorm
    dsimp
    have h_one : zornNorm (zornOne : ZornSplitOctonion ℝ) = 1 := by
      dsimp [zornNorm, zornOne, vec3Dot]
      ring
    rw [hu_norm, h_one, sub_self]
  · apply Prod.ext
    · rfl
    · dsimp [sedenionG2Derivation, cdLift]
      exact zornG2Derivation_zornOne p

/-- Concrete imaginary split-octonion witness $u_0 = \begin{pmatrix} 0 & e_1 \\ -e_1 & 0 \end{pmatrix}$
satisfying $u_0^\star = -u_0$, $u_0^2 = -1_{\mathbb{O}_s}$, and $N_{\mathbb{O}_s}(u_0) = +1$. -/
def canonicalImaginaryUnitOctonion : ZornSplitOctonion ℝ :=
  ⟨0, ![1, 0, 0], ![-1, 0, 0], 0⟩

/-- Concrete non-vacuity certification that `canonicalImaginaryUnitOctonion` satisfies all three
hypotheses of `hyperbolic_root_plus_ell_lightcone_condensation`. -/
theorem canonicalImaginaryUnitOctonion_spec :
    zornConj canonicalImaginaryUnitOctonion =
      zornSmul (-1 : ℝ) canonicalImaginaryUnitOctonion ∧
    zornMul canonicalImaginaryUnitOctonion canonicalImaginaryUnitOctonion =
      zornSmul (-1 : ℝ) zornOne ∧
    zornNorm canonicalImaginaryUnitOctonion = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext k
    · dsimp [canonicalImaginaryUnitOctonion, zornConj, zornSmul]
      ring
    · fin_cases k <;> (dsimp [canonicalImaginaryUnitOctonion, zornConj, zornSmul]; ring)
    · fin_cases k <;> (dsimp [canonicalImaginaryUnitOctonion, zornConj, zornSmul]; ring)
    · dsimp [canonicalImaginaryUnitOctonion, zornConj, zornSmul]
      ring
  · ext k
    · dsimp [canonicalImaginaryUnitOctonion, zornMul, zornSmul, zornOne, vec3Dot]
      ring
    · fin_cases k <;>
        (dsimp [canonicalImaginaryUnitOctonion, zornMul, zornSmul, zornOne, vec3Cross]; ring)
    · fin_cases k <;>
        (dsimp [canonicalImaginaryUnitOctonion, zornMul, zornSmul, zornOne, vec3Cross]; ring)
    · dsimp [canonicalImaginaryUnitOctonion, zornMul, zornSmul, zornOne, vec3Dot]
      ring
  · dsimp [canonicalImaginaryUnitOctonion, zornNorm, vec3Dot]
    ring

end InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis

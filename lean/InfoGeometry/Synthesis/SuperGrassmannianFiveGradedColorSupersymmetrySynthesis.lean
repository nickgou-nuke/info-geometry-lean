/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.ArnoldParaKahlerBCFW
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Algebra.ZornGaugeEmergence
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
import InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge
import InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge

/-!
# Frontier 103: 5-Graded Super-Grassmannian, $\mathbb{Z}_2 \times \mathbb{Z}_2$ Color Supersymmetry, Günaydin–Gürsey Superbracket Closure, and Super-Berezinian Souriau–Massieu Synthesis

This module formalizes the operator-algebraic and supergeometric closure of Frontier 103 uniting
the 5-graded Kantor–Koecher–Tits (KKT) decomposition
$\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$,
Günaydin–Gürsey $\mathbb{Z}_2 \times \mathbb{Z}_2$ color supersymmetry, and the supersymmetric
Souriau–Massieu surprisal potential:

1. **$\mathbb{Z}_2 \times \mathbb{Z}_2$ Color Supersymmetry Bi-Grading (`z2z2KoszulSign`)**:
   - Assigns bi-degrees $(\deg_e, \deg_c) \in \mathrm{Fin}\, 2 \times \mathrm{Fin}\, 2$ to the
     gauge sector `gradeGauge0 = (0, 0)`, leptonic sector `gradeLepton = (1, 0)`, quark sector
     `gradeQuark = (1, 1)`, and color-adjoint bosonic sector `gradeColorBoson = (0, 1)`.
   - Proves symmetry, involutive unit square, and the exact sectoral commutation signs
     $(-1)^{\deg_e(A)\deg_e(B) + \deg_c(A)\deg_c(B)}$ (`z2z2_color_supersymmetry_sign_laws`).

2. **Closure of the $\mathfrak{g}_{\pm 1}$ and $\mathfrak{g}_{\pm 2}$ Günaydin–Gürsey Superbrackets**:
   - **Grade $\pm 1 \times \pm 1 \to \mathfrak{g}_0 = \mathfrak{sl}_3(\mathbb{R}) \oplus \mathfrak{gl}_1(\mathbb{R})$**:
     Defines the quark–antiquark outer-product matrix `quarkAntiquarkOuter`, its trace-free
     $\mathfrak{sl}_3(\mathbb{R})$ projection `quarkAntiquarkTracelessSL3`, and its dilatation
     scalar trace `quarkAntiquarkDilatationTrace`, proving exact trace-zero closure in the
     Peirce color algebra `SL3` and recovery of the Zorn meson singlet pairing
     (`gunaydin_gursey_g1_gm1_superbracket_closure`).
   - **Grade $\pm 1 \times \pm 1 \to \mathfrak{g}_{\pm 2}$ (Diquark Cross-Product & Baryon Singlet)**:
     Proves that multiplying two pure quark triplets in `ZornSplitOctonion ℝ` lands purely in the
     anti-quark sector via the 3D cross product $\mathbf{u}_1 \times \mathbf{u}_2$, and pairing
     with a third quark triplet yields the alternating baryon determinant
     (`zorn_quark_diquark_to_antiquark_and_lepton_baryon_closure`).
   - **Bidirectional Odd Supercolor Generator $\delta_{\epsilon, \bar{\epsilon}}$ (`oddSupercolorFull`)**:
     Proves that the square $\delta_{\epsilon, \bar{\epsilon}}^2$ of the odd lepton–quark
     supercolor generator closes directly onto the even bosonic socle $\mathfrak{g}_0$: scaling
     the leptonic singlets $\mathfrak{g}_{\pm 2}$ by the color contraction
     $\langle \epsilon, \bar{\epsilon} \rangle$ while acting on the quark/antiquark triplets
     $\mathfrak{g}_{\pm 1}$ by the rank-1 outer-product operators $\epsilon \otimes \bar{\epsilon}^T$
     and $\bar{\epsilon} \otimes \epsilon^T$ (`oddSupercolorFull_sq_closes_on_even_bosonic_socle`).

3. **`super_berezinian_gauge_invariance` & Supersymmetric Souriau–Massieu UV Cancellation**:
   - Defines `superBerezinian23` and `superTrace23` on the $(2\vert 3)$ lepton–quark super-carrier.
   - Proves `super_berezinian_gauge_invariance`: exact multiplicativity, invariance under
     Weyl light-cone boosts $\operatorname{diag}(\lambda, \lambda^{-1})$ on $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$
     and $\mathrm{SL}(3, \mathbb{R})$ color gauge transformations on $\mathfrak{g}_{\pm 1}$, and
     exact vanishing of the logarithmic Berezinian and supertrace under matched bosonic/fermionic
     UV vacuum shifts.
   - Defines `superSouriauMassieuPotential` and proves
     `superSouriauMassieu_uv_cancellation_and_moment_readout`.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis

noncomputable section

open scoped BigOperators Matrix
open Finset Matrix
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge
open InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis

/-!
## Section 1: $\mathbb{Z}_2 \times \mathbb{Z}_2$ Bi-Graded Color Supersymmetry Sign Laws
-/

/-- A bi-degree $(\deg_e, \deg_c) \in \mathrm{Fin}\, 2 \times \mathrm{Fin}\, 2$ encoding electric
(fermionic) parity $\deg_e$ and color triality parity $\deg_c$. -/
abbrev Z2Z2ColorGrade : Type := Fin 2 × Fin 2

/-- Grade $0$ gauge boson bi-degree $(0, 0)$. -/
def gradeGauge0 : Z2Z2ColorGrade := (0, 0)

/-- Grade $\pm 2$ leptonic color-singlet bi-degree $(1, 0)$ ($\deg_e = 1, \deg_c = 0$). -/
def gradeLepton : Z2Z2ColorGrade := (1, 0)

/-- Grade $\pm 1$ quark color-triplet bi-degree $(1, 1)$ ($\deg_e = 1, \deg_c = 1$). -/
def gradeQuark : Z2Z2ColorGrade := (1, 1)

/-- Pure color-odd bosonic bi-degree $(0, 1)$ ($\deg_e = 0, \deg_c = 1$). -/
def gradeColorBoson : Z2Z2ColorGrade := (0, 1)

/-- Symmetric $\mathbb{Z}_2 \times \mathbb{Z}_2$ exponent
$\langle g_1, g_2 \rangle = \deg_e(g_1)\deg_e(g_2) + \deg_c(g_1)\deg_c(g_2)$. -/
def z2z2Pairing (g₁ g₂ : Z2Z2ColorGrade) : ℕ :=
  g₁.1.val * g₂.1.val + g₁.2.val * g₂.2.val

/-- Color supersymmetry commutation sign
$\varepsilon(g_1, g_2) = (-1)^{\deg_e(g_1)\deg_e(g_2) + \deg_c(g_1)\deg_c(g_2)}$. -/
def z2z2KoszulSign (g₁ g₂ : Z2Z2ColorGrade) : ℝ :=
  (-1 : ℝ) ^ (z2z2Pairing g₁ g₂)

/-- Fundamental $\mathbb{Z}_2 \times \mathbb{Z}_2$ Color Supersymmetry Sign Theorem:
1. Symmetry: $\varepsilon(g_1, g_2) = \varepsilon(g_2, g_1)$,
2. Involutive unit square: $\varepsilon(g_1, g_2)^2 = 1$,
3. Gauge boson transparency: $\varepsilon((0,0), g) = +1$,
4. Lepton–Quark odd anticommutation: $\varepsilon(\text{quark}, \text{lepton}) = -1$,
5. Lepton–Lepton fermionic anticommutation: $\varepsilon(\text{lepton}, \text{lepton}) = -1$,
6. Quark–Quark bi-odd transmutation sign: $\varepsilon(\text{quark}, \text{quark}) = (-1)^{1+1} = +1$. -/
theorem z2z2_color_supersymmetry_sign_laws (g₁ g₂ : Z2Z2ColorGrade) :
    z2z2KoszulSign g₁ g₂ = z2z2KoszulSign g₂ g₁ ∧
    z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₁ g₂ = 1 ∧
    z2z2KoszulSign gradeGauge0 g₁ = 1 ∧
    z2z2KoszulSign gradeQuark gradeLepton = -1 ∧
    z2z2KoszulSign gradeLepton gradeLepton = -1 ∧
    z2z2KoszulSign gradeQuark gradeQuark = 1 := by
  have h_symm : z2z2Pairing g₁ g₂ = z2z2Pairing g₂ g₁ := by
    dsimp [z2z2Pairing]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [z2z2KoszulSign]
    rw [h_symm]
  · dsimp [z2z2KoszulSign]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeGauge0]
    simp
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeQuark, gradeLepton]
    norm_num
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeLepton]
    norm_num
  · dsimp [z2z2KoszulSign, z2z2Pairing, gradeQuark]
    norm_num

/-!
## Section 2: Closure of the $\mathfrak{g}_{\pm 1}$ and $\mathfrak{g}_{\pm 2}$ Günaydin–Gürsey Superbrackets
-/

/-- Rank-1 quark–antiquark outer-product matrix $(u \otimes v^T)_{ij} = u_i v_j$ in $M_3(\mathbb{R})$. -/
def quarkAntiquarkOuter (u v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => u i * v j

/-- Explicit matrix non-commutativity witness on `Matrix (Fin 3) (Fin 3) ℝ` via rank-1 quark outer products. -/
theorem quarkAntiquarkOuter_noncommutative :
    quarkAntiquarkOuter ![1, 0, 0] ![0, 1, 0] *
        quarkAntiquarkOuter ![0, 1, 0] ![0, 0, 1] ≠
      quarkAntiquarkOuter ![0, 1, 0] ![0, 0, 1] *
        quarkAntiquarkOuter ![1, 0, 0] ![0, 1, 0] := by
  intro h
  have h02 := congr_fun (congr_fun h 0) 2
  norm_num [quarkAntiquarkOuter, Matrix.mul_apply, Fin.sum_univ_three] at h02

/-- Trace-free $\mathfrak{sl}_3(\mathbb{R})$ color generator extracted from the quark–antiquark
superbracket:
$$M_{\mathfrak{sl}_3}(u, v) = u \otimes v^T - \frac{1}{3} \langle u, v \rangle I_3.$$ -/
def quarkAntiquarkTracelessSL3 (u v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  quarkAntiquarkOuter u v -
    ((1 / 3 : ℝ) * vec3Dot u v) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- Grade-$0$ dilatation / hypercharge trace invariant $\langle u, v \rangle = \sum_{a=0}^2 u_a v_a$. -/
def quarkAntiquarkDilatationTrace (u v : Fin 3 → ℝ) : ℝ :=
  vec3Dot u v

/-- The trace of `quarkAntiquarkTracelessSL3 u v` vanishes identically, so it defines a valid
element of the Peirce stabilizer Lie algebra `SL3`. -/
theorem quarkAntiquarkTracelessSL3_trace_zero (u v : Fin 3 → ℝ) :
    Matrix.trace (quarkAntiquarkTracelessSL3 u v) = 0 := by
  dsimp [quarkAntiquarkTracelessSL3, quarkAntiquarkOuter, vec3Dot,
    Matrix.trace, Matrix.diag]
  simp only [Fin.sum_univ_three, Matrix.one_apply, ↓reduceIte]
  ring

/-- Bundled element of `SL3` generated by the odd quark–antiquark superbracket
$\{\mathfrak{g}_{+1}, \mathfrak{g}_{-1}\} \to \mathfrak{sl}_3(\mathbb{R}) \subset \mathfrak{g}_0$. -/
def quarkAntiquarkToSL3 (u v : Fin 3 → ℝ) : SL3 :=
  ⟨quarkAntiquarkTracelessSL3 u v, quarkAntiquarkTracelessSL3_trace_zero u v⟩

/-- **Closure of the $\{\mathfrak{g}_{+1}, \mathfrak{g}_{-1}\} \to \mathfrak{g}_0$ Superbracket**:
1. The outer product $u \otimes v^T$ decomposes into the trace-free $\mathfrak{sl}_3(\mathbb{R})$
   color generator plus the $\mathfrak{gl}_1(\mathbb{R})$ dilatation trace $\frac{1}{3}\langle u, v \rangle I_3$.
2. The $\mathfrak{sl}_3(\mathbb{R})$ projection has strictly vanishing trace.
3. In `ZornSplitOctonion ℝ`, the product of the projected quark triplet $P_{\mathbf{3}}(z)$ and
   anti-quark antitriplet $P_{\bar{\mathbf{3}}}(z)$ lands in the diagonal leptonic idempotent
   sector with coefficient $+\langle u, v \rangle$. -/
theorem gunaydin_gursey_g1_gm1_superbracket_closure
    (u v : Fin 3 → ℝ) (z : ZornSplitOctonion ℝ) :
    quarkAntiquarkOuter u v =
      quarkAntiquarkTracelessSL3 u v +
        ((1 / 3 : ℝ) * quarkAntiquarkDilatationTrace u v) • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    Matrix.trace (quarkAntiquarkToSL3 u v).1 = 0 ∧
    (zornMul (zornProjQuark z) (zornProjAntiQuark z)).a =
      quarkAntiquarkDilatationTrace z.u z.v ∧
    (zornMul (zornProjAntiQuark z) (zornProjQuark z)).b =
      quarkAntiquarkDilatationTrace z.u z.v := by
  refine ⟨?_, quarkAntiquarkTracelessSL3_trace_zero u v, ?_, ?_⟩
  · ext i j
    dsimp [quarkAntiquarkTracelessSL3, quarkAntiquarkDilatationTrace]
    ring
  · dsimp [zornProjQuark, zornProjAntiQuark, zornMul,
      quarkAntiquarkDilatationTrace, vec3Dot]
    ring
  · dsimp [zornProjQuark, zornProjAntiQuark, zornMul,
      quarkAntiquarkDilatationTrace, vec3Dot]
    ring

/-- Pure quark triplet embedding $\mathbf{u} \mapsto \begin{pmatrix} 0 & \mathbf{u} \\ 0 & 0 \end{pmatrix}$
in `ZornSplitOctonion ℝ`. -/
def embedPureQuarkZorn (u : Fin 3 → ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, u, ![0, 0, 0], 0⟩

/-- Pure anti-quark antitriplet embedding $\mathbf{v} \mapsto \begin{pmatrix} 0 & 0 \\ \mathbf{v} & 0 \end{pmatrix}$
in `ZornSplitOctonion ℝ`. -/
def embedPureAntiQuarkZorn (v : Fin 3 → ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, ![0, 0, 0], v, 0⟩

/-- **Diquark Cross-Product & Baryon Singlet Closure ($\mathfrak{g}_{+1} \times \mathfrak{g}_{+1} \to \mathfrak{g}_{-1}$ and $\mathfrak{g}_{+1}^3 \to \mathfrak{g}_{\pm 2}$)**:
1. Multiplying two pure quark triplets in `ZornSplitOctonion ℝ` produces a pure anti-quark
   antitriplet given by the 3D cross product $\mathbf{u}_1 \times \mathbf{u}_2$:
   `zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂) = embedPureAntiQuarkZorn (vec3Cross u₁ u₂)`.
2. Multiplying a third quark triplet `embedPureQuarkZorn u₃` with this diquark composite lands
   in the upper-left leptonic singlet slot $e_+$ with scalar value $\langle \mathbf{u}_3, \mathbf{u}_1 \times \mathbf{u}_2 \rangle$,
   which vanishes whenever two quark vectors coincide ($\mathbf{u}_1 = \mathbf{u}_2$, Fermi/Pauli exclusion). -/
theorem zorn_quark_diquark_to_antiquark_and_lepton_baryon_closure
    (u₁ u₂ u₃ : Fin 3 → ℝ) :
    zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂) =
      embedPureAntiQuarkZorn (vec3Cross u₁ u₂) ∧
    (zornMul (embedPureQuarkZorn u₃)
      (zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂))).a =
      vec3Dot u₃ (vec3Cross u₁ u₂) ∧
    (zornMul (embedPureQuarkZorn u₃)
      (zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₁))).a = 0 := by
  have h_diq :
      zornMul (embedPureQuarkZorn u₁) (embedPureQuarkZorn u₂) =
        embedPureAntiQuarkZorn (vec3Cross u₁ u₂) := by
    ext k
    · dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Dot]; ring
    · fin_cases k <;>
        (dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Cross]; ring)
    · fin_cases k <;>
        (dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Cross]; ring)
    · dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Dot]; ring
  refine ⟨h_diq, ?_, ?_⟩
  · rw [h_diq]
    dsimp [embedPureQuarkZorn, embedPureAntiQuarkZorn, zornMul, vec3Dot]
    ring
  · dsimp [embedPureQuarkZorn, zornMul, vec3Dot, vec3Cross]
    ring

/-- Full bidirectional odd $\mathfrak{su}(3\vert 1)$ supercolor generator
$\delta_{\epsilon, \bar{\epsilon}}$ coupling the leptonic singlets $\mathfrak{g}_{\pm 2} = (\mathbf{1} \oplus \mathbf{1})$
and the quark/antiquark color triplets $\mathfrak{g}_{\pm 1} = (\mathbf{3} \oplus \bar{\mathbf{3}})$. -/
def oddSupercolorFull (eps epsBar : Fin 3 → ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    GunaydinGurseyMultiplet ℝ :=
  (![∑ a : Fin 3, epsBar a * M.2.1 a, ∑ a : Fin 3, eps a * M.2.2 a],
   (fun a => eps a * M.1 0, fun a => epsBar a * M.1 1))

/-- **Odd Superbracket Closure ($\{\mathfrak{g}_{\pm 1}, \mathfrak{g}_{\pm 1}\} \to \mathfrak{g}_0 \oplus \mathfrak{g}_{\pm 2}$)**:
Applying the bidirectional odd supercolor generator `oddSupercolorFull eps epsBar` twice
closes directly onto the even bosonic gauge socle:
1. Each leptonic singlet coordinate $\ell_0, \ell_1 \in \mathfrak{g}_{\pm 2}$ is scaled by the
   color-singlet contraction $\langle \epsilon, \bar{\epsilon} \rangle = \sum_{a=0}^2 \epsilon_a \bar{\epsilon}_a$,
2. The quark triplet $q \in \mathbf{3}$ is transformed by the rank-1 outer-product matrix
   `quarkAntiquarkOuter eps epsBar`,
3. The anti-quark antitriplet $\bar{q} \in \bar{\mathbf{3}}$ is transformed by the transposed
   outer-product matrix `quarkAntiquarkOuter epsBar eps`. -/
theorem oddSupercolorFull_sq_closes_on_even_bosonic_socle
    (eps epsBar : Fin 3 → ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).1 0 =
      vec3Dot eps epsBar * M.1 0 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).1 1 =
      vec3Dot eps epsBar * M.1 1 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).2.1 =
      (quarkAntiquarkOuter eps epsBar).mulVec M.2.1 ∧
    (oddSupercolorFull eps epsBar (oddSupercolorFull eps epsBar M)).2.2 =
      (quarkAntiquarkOuter epsBar eps).mulVec M.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [oddSupercolorFull, vec3Dot]
    simp only [Fin.sum_univ_three]
    ring
  · dsimp [oddSupercolorFull, vec3Dot]
    simp only [Fin.sum_univ_three]
    ring
  · funext a
    dsimp [oddSupercolorFull, quarkAntiquarkOuter, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_three]
    ring
  · funext a
    dsimp [oddSupercolorFull, quarkAntiquarkOuter, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_three]
    ring

/-!
## Section 3: `super_berezinian_gauge_invariance` & Supersymmetric Souriau–Massieu UV Cancellation
-/

/-- Berezinian superdeterminant $\mathrm{Ber}(A_{\text{bos}}, D_{\text{fer}}) = \det(A_{\text{bos}}) / \det(D_{\text{fer}})$
on the $(2\vert 3)$-graded lepton–quark super-carrier ($\mathbf{1}\oplus\mathbf{1}$ bosonic leptons
over $\mathbf{3}$ fermionic quark color modes). -/
def superBerezinian23
    (A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D_fer : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A_bos.det / D_fer.det

/-- Supertrace $\mathrm{STr}(A_{\text{bos}}, D_{\text{fer}}) = \mathrm{Tr}(A_{\text{bos}}) - \mathrm{Tr}(D_{\text{fer}})$
on the $(2\vert 3)$-graded lepton–quark super-carrier. -/
def superTrace23
    (A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D_fer : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A_bos.trace - D_fer.trace

/-- Diagonal Weyl scale boost matrix $\operatorname{diag}(\lambda, \lambda^{-1})$ on the
leptonic $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$ sector. -/
def leptonWeylScaleMatrix (lam invLam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![lam, 0], ![0, invLam]]

/-- **`super_berezinian_gauge_invariance` (Super-Berezinian Gauge Invariance & UV Zero-Point Cancellation)**:
1. **Multiplicative Homomorphism**:
   $\mathrm{Ber}(A_1 A_2, D_1 D_2) = \mathrm{Ber}(A_1, D_1) \cdot \mathrm{Ber}(A_2, D_2)$.
2. **Weyl $\mathfrak{so}(1,1)$ & Color $\mathrm{SL}(3, \mathbb{R})$ Gauge Invariance**:
   For any Weyl boost $\operatorname{diag}(\lambda, \lambda^{-1})$ ($\lambda \lambda^{-1} = 1$) on
   $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$ and any color transformation $U_C \in M_3(\mathbb{R})$
   with $\det(U_C) = 1$,
   $$\mathrm{Ber}(\operatorname{diag}(\lambda, \lambda^{-1}) A_{\text{bos}}, \, U_C D_{\text{fer}})
     = \mathrm{Ber}(A_{\text{bos}}, D_{\text{fer}}).$$
3. **Trace-Free $\mathfrak{sl}_3(\mathbb{R})$ Supertrace Invariance**:
   Adding any Peirce color generator $M \in \mathrm{SL}_3$ to the fermionic block leaves
   `superTrace23` strictly invariant:
   $\mathrm{STr}(A_{\text{bos}}, D_{\text{fer}} + M.1) = \mathrm{STr}(A_{\text{bos}}, D_{\text{fer}})$.
4. **Logarithmic Berezinian & Supertrace UV Cancellation**:
   Whenever the bosonic and fermionic blocks carry matched determinant scales
   ($\det(A_{\text{bos}}) = \det(D_{\text{fer}}) \neq 0$), the logarithmic Berezinian vanishes
   identically ($\ln \mathrm{Ber}(A_{\text{bos}}, D_{\text{fer}}) = 0$). -/
theorem super_berezinian_gauge_invariance
    (A₁ A₂ A_bos : Matrix (Fin 2) (Fin 2) ℝ)
    (D₁ D₂ D_fer U_C : Matrix (Fin 3) (Fin 3) ℝ)
    (M_color : SL3)
    (lam invLam : ℝ)
    (h_weyl : lam * invLam = 1)
    (h_color_det : U_C.det = 1)
    (h_match_det : A₁.det = D₁.det)
    (hD₁_ne : D₁.det ≠ 0) :
    superBerezinian23 (A₁ * A₂) (D₁ * D₂) =
      superBerezinian23 A₁ D₁ * superBerezinian23 A₂ D₂ ∧
    superBerezinian23 (leptonWeylScaleMatrix lam invLam * A_bos) (U_C * D_fer) =
      superBerezinian23 A_bos D_fer ∧
    superTrace23 A_bos (D_fer + M_color.1) = superTrace23 A_bos D_fer ∧
    Real.log (superBerezinian23 A₁ D₁) = 0 := by
  have h_weyl_det : (leptonWeylScaleMatrix lam invLam).det = 1 := by
    dsimp [leptonWeylScaleMatrix]
    rw [Matrix.det_fin_two_of]
    linarith [h_weyl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [superBerezinian23]
    rw [Matrix.det_mul, Matrix.det_mul, mul_div_mul_comm]
  · dsimp [superBerezinian23]
    rw [Matrix.det_mul, Matrix.det_mul, h_weyl_det, h_color_det, one_mul, one_mul]
  · dsimp [superTrace23]
    rw [Matrix.trace_add, M_color.2, add_zero]
  · dsimp [superBerezinian23]
    rw [h_match_det, div_self hD₁_ne, Real.log_one]

/-- Discrete Supersymmetric Souriau–Massieu Surprisal Potential
$\Phi_{\text{super}}(s_{\text{bos}}, b_{\text{fer}}) = \ln \sum_{j} (\exp(s_{\text{bos}, j}) + b_{\text{fer}, j})$. -/
def superSouriauMassieuPotential {m : ℕ} (s_bos b_fer : Fin m → ℝ) : ℝ :=
  Real.log (∑ j : Fin m, (Real.exp (s_bos j) + b_fer j))

/-- **Supersymmetric Souriau–Massieu UV Defect Cancellation & Moment Map Recovery**:
If a bosonic partition sum suffers a mode-wise additive UV vacuum defect $\Delta_{\text{UV}}(j)$
and the odd Berezinian counterterm $b_{\text{fer}}(j) = -\Delta_{\text{UV}}(j)$ cancels it
(`h_cancel : ∀ j, b_fer j + Δ_UV j = 0`), then:
1. The perturbed supersymmetric partition sum reduces identically to the finite Souriau–Massieu
   free entropy potential $\Phi(s_{\text{bos}})$:
   $$\ln \sum_{j} \big(\exp(s_{\text{bos}, j}) + \Delta_{\text{UV}}(j) + b_{\text{fer}}(j)\big)
     = \Phi(s_{\text{bos}}).$$
2. Its coordinate derivative with respect to $s_{\text{bos}, j}$ recovers the exact canonical
   Souriau attention weight $A_j(s_{\text{bos}})$. -/
theorem superSouriauMassieu_uv_cancellation_and_moment_readout
    {m : ℕ} [Nonempty (Fin m)]
    (s_bos b_fer Δ_UV : Fin m → ℝ) (j : Fin m)
    (h_cancel : ∀ k : Fin m, b_fer k + Δ_UV k = 0) :
    superSouriauMassieuPotential s_bos (fun k => Δ_UV k + b_fer k) =
      souriauMassieuPotential s_bos ∧
    HasDerivAt
      (fun t : ℝ =>
        superSouriauMassieuPotential (Function.update s_bos j t)
          (fun k => Δ_UV k + b_fer k))
      (souriauAttentionWeight s_bos j) (s_bos j) := by
  have h_eq :
      ∀ s : Fin m → ℝ,
        superSouriauMassieuPotential s (fun k => Δ_UV k + b_fer k) =
          souriauMassieuPotential s := by
    intro s
    dsimp [superSouriauMassieuPotential, souriauMassieuPotential, gibbsPartitionSum]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hk := h_cancel k
    linarith
  refine ⟨h_eq s_bos, ?_⟩
  have h_fun :
      (fun t : ℝ =>
        superSouriauMassieuPotential (Function.update s_bos j t)
          (fun k => Δ_UV k + b_fer k)) =
      (fun t : ℝ => souriauMassieuPotential (Function.update s_bos j t)) := by
    funext t
    exact h_eq (Function.update s_bos j t)
  rw [h_fun]
  exact hasDerivAt_souriauMassieuPotential_coord s_bos j

/-!
## Section 4: Canonical Spine Carrier Equivalences & Operation Intertwining (`OpZornMatrix R ≃ GunaydinGurseyMultiplet R ≃ (Fin 8 → R)` and `ZornVectorMatrix R ≃ ZornSplitOctonion R`)

This section explicitly links the noncommutative operator-algebraic spine
(`AlbertCayleyDickson.SplitQuaternion.OpZornMatrix R`, `ArnoldParaKahlerBCFW`, and
`InfoGeometry.Algebra.ZornVectorMatrix R`) with the `Fin 8` / `Fin 3` matrix synthesis carriers
(`ZornSplitOctonion R`, `GunaydinGurseyMultiplet R`, `quarkAntiquarkOuter`, and `superTrace23`).
-/

/-- Canonical 3-vector carrier equivalence between `OpVec3 R` and `Fin 3 → R`. -/
def opVec3Fin3Equiv (R : Type*) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3 R ≃ (Fin 3 → R) where
  toFun u := ![u.x, u.y, u.z]
  invFun f := ⟨f 0, f 1, f 2⟩
  left_inv u := by cases u; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

/-- Canonical 8D split-octonion carrier equivalence between `ZornVectorMatrix R`
(`InfoGeometry.Algebra.ZornAlternativeLaws`) and `ZornSplitOctonion R`
(`InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge`). -/
def zornVectorMatrixSplitOctonionEquiv (R : Type*) :
    InfoGeometry.Algebra.ZornVectorMatrix R ≃ ZornSplitOctonion R where
  toFun X := ⟨X.a, X.v, X.w, X.b⟩
  invFun z := ⟨z.a, z.u, z.v, z.b⟩
  left_inv X := by cases X; rfl
  right_inv z := by cases z; rfl

/-- **`zornVectorMatrixSplitOctonionEquiv` Multiplicative, Norm, & 5-Graded KKT Bridge**:
1. `zornVectorMatrixSplitOctonionEquiv` is an exact algebra and quadratic-norm isomorphism between
   `ZornVectorMatrix R` (`ZornVectorMatrix.mul`, `ZornVectorMatrix.norm`) and `ZornSplitOctonion R`
   (`zornMul`, `zornNorm`).
2. Every element $X \in \mathrm{ZornVectorMatrix}\;R$ satisfies the degree-5 Kantor–Koecher–Tits
   characteristic identity $\mathcal{E}_5^5(X) - 5\,\mathcal{E}_5^3(X) + 4\,\mathcal{E}_5(X) = 0$
   (`InfoGeometry.Algebra.ZornVectorMatrix.zorn_euler_five_grading_kkt_and_supercolor_cancellation`). -/
theorem zornVectorMatrixSplitOctonionEquiv_mul_norm_and_kkt
    {R : Type*} [CommRing R] (X Y : InfoGeometry.Algebra.ZornVectorMatrix R) :
    zornVectorMatrixSplitOctonionEquiv R (InfoGeometry.Algebra.ZornVectorMatrix.mul X Y) =
      zornMul (zornVectorMatrixSplitOctonionEquiv R X) (zornVectorMatrixSplitOctonionEquiv R Y) ∧
    zornNorm (zornVectorMatrixSplitOctonionEquiv R X) =
      InfoGeometry.Algebra.ZornVectorMatrix.norm X ∧
    (let E1 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading X
     let E2 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E1
     let E3 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E2
     let E4 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E3
     let E5 := InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading E4
     E5 + -(E3 + E3 + E3 + E3 + E3) + (E1 + E1 + E1 + E1) = 0) ∧
    InfoGeometry.Algebra.ZornVectorMatrix.zornJacobsonTriple Y (InfoGeometry.Algebra.ZornVectorMatrix.conj X) Y =
      (4 : R) • (InfoGeometry.Algebra.ZornVectorMatrix.trace (X * InfoGeometry.Algebra.ZornVectorMatrix.conj Y) • Y +
        -(InfoGeometry.Algebra.ZornVectorMatrix.norm Y • X)) ∧
    InfoGeometry.Algebra.ZornVectorMatrix.trace ((X * Y) * InfoGeometry.Algebra.ZornVectorMatrix.conj X) =
      InfoGeometry.Algebra.ZornVectorMatrix.trace (X * (Y * InfoGeometry.Algebra.ZornVectorMatrix.conj X)) ∧
    (⟨0, X.v, 0, 0⟩ : InfoGeometry.Algebra.ZornVectorMatrix R) * ⟨0, 0, Y.w, 0⟩ =
      InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero
        (InfoGeometry.Algebra.ZornVec3.dot X.v Y.w) 0 ∧
    InfoGeometry.Algebra.ZornVec3.dot (![0, X.v 1, X.v 2])
      (InfoGeometry.Algebra.ZornVec3.cross (![0, Y.v 1, Y.v 2]) (![0, X.w 1, X.w 2])) = 0 ∧
    (⟨X.a, 0, X.w, 0⟩ : InfoGeometry.Algebra.ZornVectorMatrix R) *
      InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero 1 0 = ⟨X.a, 0, X.w, 0⟩ ∧
    InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero 1 0 * X +
      InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero 0 1 * X = X ∧
    InfoGeometry.Algebra.ZornVectorMatrix.freudenthal56QuarticInvariant X.a X.b 0 0 0 0 =
      -(X.a * X.b) ^ 2 ∧
    InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero X.a 0 *
      InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero 0 X.b = 0 ∧
    ((⟨X.a, X.b, 0, 0, 0⟩ : InfoGeometry.Algebra.ZornVectorMatrix.E8ContactNilradical R) *
      ⟨Y.a, Y.b, 0, 0, 0⟩) * ⟨X.a, Y.b, 0, 0, 0⟩ = 0 ∧
    InfoGeometry.Algebra.ZornVectorMatrix.zornCayleyDicksonConj
      (InfoGeometry.Algebra.ZornVectorMatrix.zornCayleyDicksonConj (X, Y)) = (X, Y) ∧
    InfoGeometry.Algebra.ZornVectorMatrix.zornGaloisZ2
      (InfoGeometry.Algebra.ZornVectorMatrix.zornGaloisZ2 X) = X ∧
    InfoGeometry.Algebra.ZornVectorMatrix.zornGaloisZ3
      (InfoGeometry.Algebra.ZornVectorMatrix.zornSinglet X.a (X.v 0) (X.w 0) X.b) =
      InfoGeometry.Algebra.ZornVectorMatrix.zornSinglet X.a (X.v 0) (X.w 0) X.b ∧
    InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading X +
      InfoGeometry.Algebra.ZornVectorMatrix.zornEuler5Y X +
      InfoGeometry.Algebra.ZornVectorMatrix.zornEuler5Z X = 0 ∧
    (InfoGeometry.Algebra.ZornVectorMatrix.zornSpinX :
      InfoGeometry.Algebra.ZornVectorMatrix R) *
      InfoGeometry.Algebra.ZornVectorMatrix.zornSpinX =
      -InfoGeometry.Algebra.ZornVectorMatrix.one := by
  refine ⟨?_, ?_,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_euler_five_grading_kkt_and_supercolor_cancellation
      X 0 0 0 0 0 0 X.v Y.w).2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.catto_jacobson_triple_weyl_reflection_and_norm_similitude
      X Y 0 0 0 X.v Y.w X.v Y.w X.v Y.w X.v Y.w).2.2.2.2.2.2.2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.albertZorn27D_freudenthal_sharp_and_determinant_law
      0 0 0 X X Y).1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_hansen_conformal_doublet_and_triality_marriage
      X.v Y.w X.v Y.v X.w Y.w).2.2.2.2.2.2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_zero_chiral_volume_and_parabolic_majorana_zero_modes
      (X.v 1) (X.v 2) (Y.v 1) (Y.v 2) (X.w 1) (X.w 2) (X.v 0) (X.v 1) (X.v 2) (Y.w 0)).1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_chevalley_shirokov_spinor_bra_ket_and_associative_contact_sandwich
      X.a Y.a (X.v 0) (X.w 0) (Y.v 0) (Y.w 0) X.b Y.b Y.v X.w).1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_trifactor_loxodromic_compass_doubled_four_potential_and_riccati_fixed_point
      X X.a X.b 0 X.v X.w Y.v).2.2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.freudenthal56Zorn_euler_trace_symplectic_and_quartic_s_duality
      0 0 0 X X Y X.a X.b 0 0 0 0 0 0 0 0 0 0).2.2.2.2.2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_doublet_colimit_riccati_taylor_and_gelfand_retakh_elimination
      X X.a X.b 0 X.v X.w Y.v Y.w).2.2.2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.fiveGraded_E8_nilradical_associativity_and_albert_K0_peirce_split
      ⟨X.a, X.b, 0, 0, 0⟩ ⟨Y.a, Y.b, 0, 0, 0⟩ ⟨X.a, Y.b, 0, 0, 0⟩).2.2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_nambuGorkov_cayley_dickson_and_five_graded_spectral_projectors
      X X Y).1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zorn_cyclotomic_factorizations_and_z6_galois_automorphism_group
      X.a X Y).2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zornSinglet_strict_associativity_and_riccati_reduction
      X.a (X.v 0) (X.w 0) X.b Y.a (Y.v 0) (Y.w 0) Y.b X.a (Y.v 0) (X.w 0) Y.b).1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zornReflZ2_dihedral_S3_and_triality_five_gradings
      X Y).2.2.2.1,
    (InfoGeometry.Algebra.ZornVectorMatrix.zornSpin_square_eq_neg_one (R := R)).1⟩
  · ext k
    · dsimp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
        zornMul, InfoGeometry.Algebra.ZornVec3.dot, vec3Dot]
      simp only [Fin.sum_univ_three]
    · fin_cases k <;>
        simp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
          zornMul, InfoGeometry.Algebra.ZornVec3.cross, vec3Cross]
    · fin_cases k <;>
        simp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
          zornMul, InfoGeometry.Algebra.ZornVec3.cross, vec3Cross]
    · dsimp [zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornVectorMatrix.mul,
        zornMul, InfoGeometry.Algebra.ZornVec3.dot, vec3Dot]
      simp only [Fin.sum_univ_three]
      ring
  · dsimp [zornVectorMatrixSplitOctonionEquiv, zornNorm,
      InfoGeometry.Algebra.ZornVectorMatrix.norm, InfoGeometry.Algebra.ZornVec3.dot, vec3Dot]
    simp only [Fin.sum_univ_three]

/-- Canonical 8D carrier equivalence between the noncommutative operator-algebraic Zorn matrix
`OpZornMatrix R` (`AlbertCayleyDickson.lean`) and the Günaydin–Gürsey lepton–quark multiplet
`GunaydinGurseyMultiplet R = (Fin 2 → R) × (Fin 3 → R) × (Fin 3 → R)` (`Cl55SuperGrassmannianKKTSynthesis.lean`). -/
def opZornGunaydinGurseyEquiv (R : Type*) :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix R ≃
      GunaydinGurseyMultiplet R where
  toFun X := (![X.a, X.b], opVec3Fin3Equiv R X.v, opVec3Fin3Equiv R X.w)
  invFun M := ⟨M.1 0, (opVec3Fin3Equiv R).symm M.2.1, (opVec3Fin3Equiv R).symm M.2.2, M.1 1⟩
  left_inv X := by
    rcases X with ⟨a, ⟨vx, vy, vz⟩, ⟨wx, wy, wz⟩, b⟩
    rfl
  right_inv M := by
    rcases M with ⟨ℓ, q, qbar⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl

/-- Canonical 8D equivalence between `OpZornMatrix R` and the 8-component $\mathrm{Cl}(4,4)$
semi-spinor carrier `Fin 8 → R`. -/
def opZornFin8SemiSpinorEquiv (R : Type*) [Ring R] :
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix R ≃ (Fin 8 → R) :=
  (opZornGunaydinGurseyEquiv R).trans (gunaydinGurseyEquiv R).toEquiv.symm

/-- **Canonical Spine Intertwining Theorem (`OpZornMatrix` ↔ `SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`)**:
1. **Color Outer-Product Intertwining**: Under `opVec3Fin3Equiv ℝ`, the `OpZornMatrix` color
   outer-product entries `opColorOuterMat u v` coincide entrywise with `quarkAntiquarkOuter`:
   `quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 0 0 = opColorOuterMat u v 0 0`,
   `quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 1 1 = opColorOuterMat u v 1 1`,
   `quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 2 2 = opColorOuterMat u v 2 2`.
2. **Dilatation Trace & Quark Trace Intertwining**: Both `OpVec3.dot u v` and
   `opQuarkTrace (opColorOuterMat u v)` equal `quarkAntiquarkDilatationTrace (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)`.
3. **$(2|3)$ Lepton–Quark Supertrace Intertwining & UV Cancellation**:
   `superTrace23 (Matrix.of ![![OpVec3.dot u v, 0], ![0, 0]]) (quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)) = opSuperTrace23 (opGradeZero (OpVec3.dot u v) 0) (opColorOuterMat u v) = 0`.
4. **Euler 5-Grading KKT Polynomial on `OpZornMatrix ℝ`**:
   Every `X : OpZornMatrix ℝ` satisfies $\mathcal{E}_5^5(X) - 5\,\mathcal{E}_5^3(X) + 4\,\mathcal{E}_5(X) = 0$
   (`ArnoldParaKahlerBCFW.operator_super_grassmannian_kkt_and_supercolor_master_bridge`). -/
theorem opZorn_supergrassmannian_color_and_supertrace_intertwining
    (u v : InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3 ℝ)
    (X : InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ) :
    quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 0 0 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v 0 0 ∧
    quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 1 1 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v 1 1 ∧
    quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) 2 2 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v 2 2 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v =
      quarkAntiquarkDilatationTrace (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opQuarkTrace
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v) =
      quarkAntiquarkDilatationTrace (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v) ∧
    superTrace23
        (Matrix.of ![![InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v, 0], ![0, 0]])
        (quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opSuperTrace23
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero
          (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v) 0)
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat u v) ∧
    superTrace23
        (Matrix.of ![![InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v, 0], ![0, 0]])
        (quarkAntiquarkOuter (opVec3Fin3Equiv ℝ u) (opVec3Fin3Equiv ℝ v)) = 0 ∧
    (let E1 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading X
     let E2 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E1
     let E3 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E2
     let E4 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E3
     let E5 := InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading E4
     E5 - (E3 + E3 + E3 + E3 + E3) + (E1 + E1 + E1 + E1) = 0) ∧
    ((InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmS1 :
        InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ) *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmS0) *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmR1 =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opDahmR0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornTrace
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opLineComplex u v *
          InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opLineHodgeDual u v) =
      -InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u u +
        InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot v v ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opSedenionZeroDivPlus u v *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opSedenionZeroDivMinus u v = 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGrassmannLinePlane v 0 X.v -
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGrassmannLinePlane u 0 X.v +
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGrassmannLinePlane u v X.v -
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGrassmannLinePlane u v 0 = 0 ∧
    X + InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opCayleyConj X =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornTrace X)
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornTrace X) ∧
    (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opJacobsonTriple
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opKasparovZornJ u v)
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opKasparovZornJ u v)
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opKasparovZornJ u v)).a = 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opLightconePlus u *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opLightconeMinus v =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero
        (-InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot u v) 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opContactFlowIdempotent u.x u.y u.z *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradePlus2 v.x = 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opAssociator
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opLounestoSpinorLeft u.x u.y)
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opLounestoSpinorRight v.x v.y)
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opLounestoSpinorLeft u.z v.z) = 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornRiccati
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opBruhatTrifactor v 1 0 u) u = 0 ∧
    (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opUnipotentLower (-v) *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opBruhatTrifactor v 1 u.x u) *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opUnipotentUpper (-u) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero 1 u.x ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix.map (RingHom.id ℝ) X = X ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.cdMul u.x
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.cdGenE
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.cdGenE =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.cdEmbed u.x ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.zornGaloisZ2
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.zornGaloisZ2 X) = X ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.trialityPerm
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornRiccati X u) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornRiccati
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.zornGaloisZ3 X)
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.trialityPerm u) ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.zornSingletProj
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.zornOctetProj X) = 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading X +
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEuler5Y X +
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEuler5Z X = 0 ∧
    (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.zornSpinX :
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix ℝ) *
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.zornSpinX = -1 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opCommutator X
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero 1 0) =
      ⟨0, -X.v, X.w, 0⟩ ∧
    Matrix.trace
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matConnesDensityVariation
        (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matConnesB2
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matChernConnesCochain2
        (0 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 ∧
    InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matCoarseGrain
      (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matCoarseGrain 0
        (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matCoarseGrain 0 0)) =
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matCoarseGrain3 0 0 0 0 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_super_grassmannian_kkt_and_supercolor_master_bridge
      X 0 0 0 0 0 0 0 0 0 0 0 0 u v u v u v 1).1.2.2.2.2.2.2.2,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_dahm_projective_line_geometry_pg32_and_sl2h_master_bridge
      u v u v X 0 0 0 0 0 0 0 0).2.2.2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_dahm_maxwell_poynting_hodge_dual_stress_master_bridge
      u v).2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_saniga_holweck_pracna_grassmannian_and_sedenion_zero_divisor_master_bridge
      1 0 u v u u v u v u v).2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_universal_super_grassmannian_and_pasch_tetrahedral_boundary_master_bridge
      (0 : Matrix (Fin 2) (Fin 3) ℝ) (0 : Matrix (Fin 3) (Fin 2) ℝ) u v 0 X.v).2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_catto_e9_e10_kac_moody_and_conway_sloane_freudenthal_master_bridge
      X 0 0 0 u v u v u v u v (0 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 0 0 0 0 0 0 0).1.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_zorn_jacobson_triality_and_72channel_freudenthal_master_bridge
      v u u v u v u v u u u X X 0 0 0 0 0 0 0 0 0).1.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_hansen_cl42_doublet_tower_d4_selection_and_zorn_triality_master_bridge
      (0 : ℝ) (0 : ℝ) (4 : ℝ) (2 : ℝ) 4 u v u v u v).2.2.2.2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_zero_chiral_volume_krein_null_kernel_and_parabolic_majorana_master_bridge
      u.y u.z u.x v.y v.z v.x 0 0 0 u.y u.z u.x v.x).2.2.2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_chevalley_shirokov_spinor_ideals_and_dirac_krein_braket_master_bridge
      X u.x v.x u.x u.y v.x v.y u.z v.z u.x u v).2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_trifactor_loxodromic_compass_doubled_four_potential_and_zorn_riccati_master_bridge
      X 0 0 0 0 1 1 0 u u u v v 1 1).2.2.2.2.2.2.2.2.2.2,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_freudenthal56_colimit_doublet_tower_and_gelfand_retakh_master_bridge
      X u v u u v v 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 u.x 1 1 0).2.2.2.1.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_functorial_category_compass_colimit_and_dilaton_cross_ratio_master_bridge
      (RingHom.id ℝ) (RingHom.id ℝ) X u v u v u v 0 0 0 0 1 1).1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_nambu_gorkov_cayley_dickson_and_five_graded_spectral_projectors_master_bridge
      u.x u.y v.x X).1.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_cyclotomic_quotients_and_z6_galois_automorphism_master_bridge
      u.x u.y v.x 0 0 0 0 0 X X u v).2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_cyclotomic_degree_doubling_cyc6_and_riccati_galois_equivariance_master_bridge
      u.x u.y v.x 0 0 0 0 0 X v u u).2.2.2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_cyclotomic_jordan_norm_singlet_associativity_and_riccati_jacobian_master_bridge
      u.x u.y u.x u.y u.z v.x v.y v.z u.x v.y u.z v.x u.y v.z u.z v.x u.x X u v).2.1.2.2.2.2.2,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_dihedral_S3_octahedral_S4_klein_resolution_and_triality_five_gradings_master_bridge
      X X u v u).2.2.2.2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_quaternion_Q8_spin_double_cover_internal_spinors_and_klein_fusion_master_bridge
      u X X).2.1.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_connes_idempotent_curvature_gauss_codazzi_and_zorn_vacuum_master_bridge
      (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 0 (Matrix.zero_mul 0) X).2.2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_connes_cocycle_adiabatic_double_commutator_and_lie_exactness_master_bridge
      (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 1 0 ⟨Matrix.one_mul 1, Matrix.one_mul 1⟩ (Matrix.zero_mul 0)).2.1.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_connes_bicomplex_chern_connes_cocycle_and_taxonomic_coarse_graining_master_bridge
      0 0 0 0 (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 0 0 0 0 (Matrix.zero_mul 0) ⟨Matrix.zero_mul 0, Matrix.zero_mul 0⟩ (by simp [InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.matInnerDer])).2.1.2.2.2.2.2.2.1,
    (InfoGeometry.Canonical.ArnoldParaKahlerBCFW.operator_three_level_flag_commuting_coarse_graining_and_three_stratum_connes_cocycle_master_bridge
      (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 0 0 ⟨Matrix.zero_mul 0, Matrix.zero_mul 0, Matrix.zero_mul 0, ⟨Matrix.zero_mul 0, Matrix.zero_mul 0⟩, ⟨Matrix.zero_mul 0, Matrix.zero_mul 0⟩⟩).1.2.2.2.2.2.2.2.2.2.2.2.1⟩
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [opVec3Fin3Equiv,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot,
      quarkAntiquarkDilatationTrace, vec3Dot]
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [opVec3Fin3Equiv,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opQuarkTrace,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat,
      quarkAntiquarkDilatationTrace, vec3Dot]
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [superTrace23, Matrix.trace, Matrix.diag, opVec3Fin3Equiv, quarkAntiquarkOuter,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opSuperTrace23,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opZornTrace,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opGradeZero,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opCartanDiag,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opQuarkTrace,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opColorOuterMat,
      Fin.sum_univ_two, Fin.sum_univ_three]
  · rcases u with ⟨ux, uy, uz⟩
    rcases v with ⟨vx, vy, vz⟩
    simp [superTrace23, Matrix.trace, Matrix.diag, opVec3Fin3Equiv, quarkAntiquarkOuter,
      InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpVec3.dot,
      Fin.sum_univ_two, Fin.sum_univ_three]

/-!
## Section 6: Full `(2|3)` Block Supermatrix Berezinian, Grassmann Superalgebra Multiplicativity, White Singlets vs Color Triplets, & 5-Graded Super-Jacobi Closure
-/

/-- Full `(2|3)` block matrix `M = [[A, B], [C, D]]` over a ring `K`. -/
@[ext]
structure SuperBlock23 (K : Type*) where
  A : Matrix (Fin 2) (Fin 2) K
  B : Matrix (Fin 2) (Fin 3) K
  C : Matrix (Fin 3) (Fin 2) K
  D : Matrix (Fin 3) (Fin 3) K

namespace SuperBlock23

def mul {K : Type*} [CommRing K] (M₁ M₂ : SuperBlock23 K) : SuperBlock23 K where
  A := M₁.A * M₂.A + M₁.B * M₂.C
  B := M₁.A * M₂.B + M₁.B * M₂.D
  C := M₁.C * M₂.A + M₁.D * M₂.C
  D := M₁.C * M₂.B + M₁.D * M₂.D

def one (K : Type*) [CommRing K] : SuperBlock23 K where
  A := 1
  B := 0
  C := 0
  D := 1

instance {K : Type*} [CommRing K] : Mul (SuperBlock23 K) := ⟨mul⟩
instance {K : Type*} [CommRing K] : One (SuperBlock23 K) := ⟨one K⟩

def upperBlock {K : Type*} [CommRing K] (B : Matrix (Fin 2) (Fin 3) K) : SuperBlock23 K :=
  ⟨1, B, 0, 1⟩

def lowerBlock {K : Type*} [CommRing K] (C : Matrix (Fin 3) (Fin 2) K) : SuperBlock23 K :=
  ⟨1, 0, C, 1⟩

def diagBlock {K : Type*} [CommRing K] (A : Matrix (Fin 2) (Fin 2) K)
    (D : Matrix (Fin 3) (Fin 3) K) : SuperBlock23 K :=
  ⟨A, 0, 0, D⟩

/-- Full `(2|3)` Schur-complement Berezinian `det(A - B D⁻¹ C) / det(D)` over `ℝ`. -/
def fullBerezinian23 (M : SuperBlock23 ℝ) : ℝ :=
  (M.A - M.B * M.D⁻¹ * M.C).det / M.D.det

/-- `fullBerezinian23` extends `superBerezinian23` on block-diagonal, upper-triangular, and
    lower-triangular `(2|3)` supermatrices. -/
theorem fullBerezinian23_extends (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 3) ℝ)
    (C : Matrix (Fin 3) (Fin 2) ℝ) (D : Matrix (Fin 3) (Fin 3) ℝ) :
    fullBerezinian23 (diagBlock A D) = superBerezinian23 A D ∧
    fullBerezinian23 ⟨A, B, 0, D⟩ = superBerezinian23 A D ∧
    fullBerezinian23 ⟨A, 0, C, D⟩ = superBerezinian23 A D ∧
    fullBerezinian23 (upperBlock B) = 1 ∧
    fullBerezinian23 (lowerBlock C) = 1 := by
  simp [fullBerezinian23, superBerezinian23, diagBlock, upperBlock, lowerBlock]

/-- Exact UDL block factorization and UDL/LDU Berezinian multiplicativity on `SuperBlock23 ℝ`. -/
theorem fullBerezinian23_udl_factorization_and_multiplicativity
    (M : SuperBlock23 ℝ) (hD : M.D.det ≠ 0)
    (B₁ : Matrix (Fin 2) (Fin 3) ℝ) (C₂ : Matrix (Fin 3) (Fin 2) ℝ)
    (A₁ A₂ : Matrix (Fin 2) (Fin 2) ℝ) (D₁ D₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hD₁ : D₁.det ≠ 0) (hD₂ : D₂.det ≠ 0) :
    M = upperBlock (M.B * M.D⁻¹) *
        diagBlock (M.A - M.B * M.D⁻¹ * M.C) M.D *
        lowerBlock (M.D⁻¹ * M.C) ∧
    fullBerezinian23 (upperBlock B₁ * M) =
      fullBerezinian23 (upperBlock B₁) * fullBerezinian23 M ∧
    fullBerezinian23 (M * lowerBlock C₂) =
      fullBerezinian23 M * fullBerezinian23 (lowerBlock C₂) ∧
    fullBerezinian23 (diagBlock A₁ D₁ * M) =
      fullBerezinian23 (diagBlock A₁ D₁) * fullBerezinian23 M ∧
    fullBerezinian23 (M * diagBlock A₂ D₂) =
      fullBerezinian23 M * fullBerezinian23 (diagBlock A₂ D₂) := by
  have hD_inv : M.D * M.D⁻¹ = 1 := Matrix.mul_nonsing_inv M.D (isUnit_iff_ne_zero.mpr hD)
  have hD_inv_l : M.D⁻¹ * M.D = 1 := Matrix.nonsing_inv_mul M.D (isUnit_iff_ne_zero.mpr hD)
  have hD₁_inv : D₁ * D₁⁻¹ = 1 := Matrix.mul_nonsing_inv D₁ (isUnit_iff_ne_zero.mpr hD₁)
  have hD₂_inv : D₂ * D₂⁻¹ = 1 := Matrix.mul_nonsing_inv D₂ (isUnit_iff_ne_zero.mpr hD₂)
  have hmul_sb : ∀ P Q : SuperBlock23 ℝ, P * Q = SuperBlock23.mul P Q := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hmul_sb, hmul_sb]
    apply SuperBlock23.ext <;>
      simp only [SuperBlock23.mul, upperBlock, diagBlock, lowerBlock,
        Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
        Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc M.D⁻¹ M.D (M.D⁻¹ * M.C), hD_inv_l, Matrix.one_mul, sub_add_cancel]
    · rw [hD_inv_l, Matrix.mul_one]
    · rw [← Matrix.mul_assoc M.D M.D⁻¹ M.C, hD_inv, Matrix.one_mul]
  · have hUB : upperBlock B₁ * M = ⟨M.A + B₁ * M.C, M.B + B₁ * M.D, M.C, M.D⟩ := by
      rw [hmul_sb]
      apply SuperBlock23.ext <;>
        simp [SuperBlock23.mul, upperBlock, add_comm]
    rw [hUB]
    simp only [fullBerezinian23, upperBlock, Matrix.mul_zero, sub_zero,
      Matrix.det_one, div_one, one_mul, Matrix.add_mul]
    congr 2
    calc
      M.A + B₁ * M.C - (M.B * M.D⁻¹ * M.C + B₁ * M.D * M.D⁻¹ * M.C) =
          M.A + B₁ * M.C - (M.B * M.D⁻¹ * M.C + B₁ * M.C) := by
        rw [Matrix.mul_assoc B₁ M.D M.D⁻¹, hD_inv, Matrix.mul_one]
      _ = M.A - M.B * M.D⁻¹ * M.C := by abel
  · have hML : M * lowerBlock C₂ = ⟨M.A + M.B * C₂, M.B, M.C + M.D * C₂, M.D⟩ := by
      rw [hmul_sb]
      apply SuperBlock23.ext <;>
        simp [SuperBlock23.mul, lowerBlock]
    rw [hML]
    simp only [fullBerezinian23, lowerBlock, Matrix.zero_mul,
      sub_zero, Matrix.det_one, div_one, mul_one, Matrix.mul_add]
    congr 2
    calc
      M.A + M.B * C₂ - (M.B * M.D⁻¹ * M.C + M.B * M.D⁻¹ * (M.D * C₂)) =
          M.A + M.B * C₂ - (M.B * M.D⁻¹ * M.C + M.B * C₂) := by
        rw [← Matrix.mul_assoc (M.B * M.D⁻¹) M.D C₂, Matrix.mul_assoc M.B M.D⁻¹ M.D,
          hD_inv_l, Matrix.mul_one]
      _ = M.A - M.B * M.D⁻¹ * M.C := by abel
  · have hDM : diagBlock A₁ D₁ * M = ⟨A₁ * M.A, A₁ * M.B, D₁ * M.C, D₁ * M.D⟩ := by
      rw [hmul_sb]
      apply SuperBlock23.ext <;> simp [SuperBlock23.mul, diagBlock]
    rw [hDM]
    simp only [fullBerezinian23, diagBlock, Matrix.mul_zero, Matrix.zero_mul, sub_zero,
      Matrix.det_mul, Matrix.mul_inv_rev]
    have hnum :
        A₁ * M.A - A₁ * M.B * (M.D⁻¹ * D₁⁻¹) * (D₁ * M.C) =
          A₁ * (M.A - M.B * M.D⁻¹ * M.C) := by
      calc
        A₁ * M.A - A₁ * M.B * (M.D⁻¹ * D₁⁻¹) * (D₁ * M.C) =
            A₁ * M.A - A₁ * M.B * M.D⁻¹ * (D₁⁻¹ * D₁) * M.C := by
          simp only [Matrix.mul_assoc]
        _ = A₁ * M.A - A₁ * M.B * M.D⁻¹ * M.C := by
          rw [Matrix.nonsing_inv_mul D₁ (isUnit_iff_ne_zero.mpr hD₁), Matrix.mul_one]
        _ = A₁ * (M.A - M.B * M.D⁻¹ * M.C) := by
          simp only [Matrix.mul_sub, Matrix.mul_assoc]
    rw [hnum, Matrix.det_mul]
    ring
  · have hMD : M * diagBlock A₂ D₂ = ⟨M.A * A₂, M.B * D₂, M.C * A₂, M.D * D₂⟩ := by
      rw [hmul_sb]
      apply SuperBlock23.ext <;> simp [SuperBlock23.mul, diagBlock]
    rw [hMD]
    simp only [fullBerezinian23, diagBlock, Matrix.mul_zero, Matrix.zero_mul, sub_zero,
      Matrix.det_mul, Matrix.mul_inv_rev]
    have hnum :
        M.A * A₂ - M.B * D₂ * (D₂⁻¹ * M.D⁻¹) * (M.C * A₂) =
          (M.A - M.B * M.D⁻¹ * M.C) * A₂ := by
      calc
        M.A * A₂ - M.B * D₂ * (D₂⁻¹ * M.D⁻¹) * (M.C * A₂) =
            M.A * A₂ - M.B * (D₂ * D₂⁻¹) * M.D⁻¹ * M.C * A₂ := by
          simp only [Matrix.mul_assoc]
        _ = M.A * A₂ - M.B * M.D⁻¹ * M.C * A₂ := by rw [hD₂_inv, Matrix.mul_one]
        _ = (M.A - M.B * M.D⁻¹ * M.C) * A₂ := by
          simp only [Matrix.sub_mul, Matrix.mul_assoc]
    rw [hnum, Matrix.det_mul]
    ring

end SuperBlock23

/-- Commutative Grassmann-even subalgebra `Grassmann2Even K ≅ K[ε]/(ε²)` (`c₀ + c₁₂ θ₁∧θ₂`). -/
@[ext]
structure Grassmann2Even (K : Type*) where
  c0 : K
  c12 : K

/-- Grassmann-odd vector space `Grassmann2Odd K = K θ₁ ⊕ K θ₂`. -/
@[ext]
structure Grassmann2Odd (K : Type*) where
  c1 : K
  c2 : K

namespace Grassmann2Odd

variable {K : Type*} [CommRing K]

instance : Zero (Grassmann2Odd K) := ⟨⟨0, 0⟩⟩
instance : Add (Grassmann2Odd K) := ⟨fun x y => ⟨x.c1 + y.c1, x.c2 + y.c2⟩⟩
instance : Neg (Grassmann2Odd K) := ⟨fun x => ⟨-x.c1, -x.c2⟩⟩
instance : Sub (Grassmann2Odd K) := ⟨fun x y => ⟨x.c1 - y.c1, x.c2 - y.c2⟩⟩

@[simp] lemma zero_c1 : (0 : Grassmann2Odd K).c1 = 0 := rfl
@[simp] lemma zero_c2 : (0 : Grassmann2Odd K).c2 = 0 := rfl
@[simp] lemma add_c1 (x y : Grassmann2Odd K) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] lemma add_c2 (x y : Grassmann2Odd K) : (x + y).c2 = x.c2 + y.c2 := rfl

end Grassmann2Odd

namespace Grassmann2Even

variable {K : Type*} [CommRing K]

instance : Zero (Grassmann2Even K) := ⟨⟨0, 0⟩⟩
instance : One (Grassmann2Even K) := ⟨⟨1, 0⟩⟩
instance : Add (Grassmann2Even K) := ⟨fun x y => ⟨x.c0 + y.c0, x.c12 + y.c12⟩⟩
instance : Neg (Grassmann2Even K) := ⟨fun x => ⟨-x.c0, -x.c12⟩⟩
instance : Sub (Grassmann2Even K) := ⟨fun x y => ⟨x.c0 - y.c0, x.c12 - y.c12⟩⟩
instance : Mul (Grassmann2Even K) :=
  ⟨fun x y => ⟨x.c0 * y.c0, x.c0 * y.c12 + x.c12 * y.c0⟩⟩

@[simp] lemma zero_c0 : (0 : Grassmann2Even K).c0 = 0 := rfl
@[simp] lemma zero_c12 : (0 : Grassmann2Even K).c12 = 0 := rfl
@[simp] lemma one_c0 : (1 : Grassmann2Even K).c0 = 1 := rfl
@[simp] lemma one_c12 : (1 : Grassmann2Even K).c12 = 0 := rfl
@[simp] lemma add_c0 (x y : Grassmann2Even K) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] lemma add_c12 (x y : Grassmann2Even K) : (x + y).c12 = x.c12 + y.c12 := rfl
@[simp] lemma neg_c0 (x : Grassmann2Even K) : (-x).c0 = -x.c0 := rfl
@[simp] lemma neg_c12 (x : Grassmann2Even K) : (-x).c12 = -x.c12 := rfl
@[simp] lemma sub_c0 (x y : Grassmann2Even K) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] lemma sub_c12 (x y : Grassmann2Even K) : (x - y).c12 = x.c12 - y.c12 := rfl
@[simp] lemma mul_c0 (x y : Grassmann2Even K) : (x * y).c0 = x.c0 * y.c0 := rfl
@[simp] lemma mul_c12 (x y : Grassmann2Even K) :
    (x * y).c12 = x.c0 * y.c12 + x.c12 * y.c0 := rfl

instance : CommRing (Grassmann2Even K) where
  add_assoc := fun a b c => by ext <;> simp [add_assoc]
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp [add_comm]
  mul_assoc := fun a b c => by ext <;> simp <;> ring
  one_mul := fun a => by ext <;> simp
  mul_one := fun a => by ext <;> simp
  zero_mul := fun a => by ext <;> simp
  mul_zero := fun a => by ext <;> simp
  left_distrib := fun a b c => by ext <;> simp <;> ring
  right_distrib := fun a b c => by ext <;> simp <;> ring
  mul_comm := fun a b => by ext <;> simp <;> ring
  sub_eq_add_neg := fun a b => by ext <;> simp [sub_eq_add_neg]

@[simp] lemma sum_c0 {ι : Type*} (s : Finset ι) (f : ι → Grassmann2Even K) :
    (∑ i ∈ s, f i).c0 = ∑ i ∈ s, (f i).c0 :=
  map_sum (AddMonoidHom.mk ⟨fun x : Grassmann2Even K => x.c0, zero_c0⟩ add_c0) f s

@[simp] lemma sum_c12 {ι : Type*} (s : Finset ι) (f : ι → Grassmann2Even K) :
    (∑ i ∈ s, f i).c12 = ∑ i ∈ s, (f i).c12 :=
  map_sum (AddMonoidHom.mk ⟨fun x : Grassmann2Even K => x.c12, zero_c12⟩ add_c12) f s

end Grassmann2Even

/-- Grassmann odd wedge product `θ₁ ∧ θ₂`: `(u₁ θ₁ + u₂ θ₂) * (v₁ θ₁ + v₂ θ₂) = (u₁ v₂ - u₂ v₁) θ₁₂`. -/
def grassmannOddMul {K : Type*} [CommRing K] (u v : Grassmann2Odd K) : Grassmann2Even K :=
  ⟨0, u.c1 * v.c2 - u.c2 * v.c1⟩

/-- Grassmann even-times-odd module action `(a₀ + a₁₂ θ₁₂) • (v₁ θ₁ + v₂ θ₂) = a₀ v₁ θ₁ + a₀ v₂ θ₂`. -/
def grassmannEvenOddMul {K : Type*} [CommRing K]
    (a : Grassmann2Even K) (v : Grassmann2Odd K) : Grassmann2Odd K :=
  ⟨a.c0 * v.c1, a.c0 * v.c2⟩

/-- Anticommutativity of Grassmann-odd elements: `u * v = -(v * u)`. -/
theorem grassmannOddMul_anticomm {K : Type*} [CommRing K] (u v : Grassmann2Odd K) :
    grassmannOddMul u v = -grassmannOddMul v u := by
  ext <;> simp [grassmannOddMul] <;> ring

/-- Over a field `K`, any `x : Grassmann2Even K` with `x.c0 ≠ 0` has an exact multiplicative inverse. -/
def grassmannEvenInv {K : Type*} [Field K] (x : Grassmann2Even K) : Grassmann2Even K :=
  ⟨x.c0⁻¹, -x.c0⁻¹ * x.c12 * x.c0⁻¹⟩

theorem grassmannEven_mul_inv {K : Type*} [Field K] (x : Grassmann2Even K) (hx : x.c0 ≠ 0) :
    x * grassmannEvenInv x = 1 := by
  ext <;> simp [grassmannEvenInv, hx] <;> field_simp [hx] <;> ring

/-- Full `(2|3)` Grassmann supermatrix `(A, B, C, D)` with even diagonal blocks
    `A ∈ M₂(Grassmann2Even K)`, `D ∈ M₃(Grassmann2Even K)` and odd off-diagonal blocks
    `B ∈ M₂ₓ₃(Grassmann2Odd K)`, `C ∈ M₃ₓ₂(Grassmann2Odd K)`. -/
@[ext]
structure GrassmannSuper23 (K : Type*) where
  A : Matrix (Fin 2) (Fin 2) (Grassmann2Even K)
  B : Matrix (Fin 2) (Fin 3) (Grassmann2Odd K)
  C : Matrix (Fin 3) (Fin 2) (Grassmann2Odd K)
  D : Matrix (Fin 3) (Fin 3) (Grassmann2Even K)

namespace GrassmannSuper23

variable {K : Type*} [Field K]

/-- Odd matrix product `B * C` with entries in `Grassmann2Even K`. -/
def oddMul {m k n : ℕ} (P : Matrix (Fin m) (Fin k) (Grassmann2Odd K))
    (Q : Matrix (Fin k) (Fin n) (Grassmann2Odd K)) : Matrix (Fin m) (Fin n) (Grassmann2Even K) :=
  fun i j => ∑ r : Fin k, grassmannOddMul (P i r) (Q r j)

/-- Even-by-odd matrix product `A * B` with entries in `Grassmann2Odd K`. -/
def evenOddMul {m k n : ℕ} (P : Matrix (Fin m) (Fin k) (Grassmann2Even K))
    (Q : Matrix (Fin k) (Fin n) (Grassmann2Odd K)) : Matrix (Fin m) (Fin n) (Grassmann2Odd K) :=
  fun i j => ⟨∑ r : Fin k, (P i r).c0 * (Q r j).c1, ∑ r : Fin k, (P i r).c0 * (Q r j).c2⟩

/-- Odd-by-even matrix product `B * D` with entries in `Grassmann2Odd K`. -/
def oddEvenMul {m k n : ℕ} (P : Matrix (Fin m) (Fin k) (Grassmann2Odd K))
    (Q : Matrix (Fin k) (Fin n) (Grassmann2Even K)) : Matrix (Fin m) (Fin n) (Grassmann2Odd K) :=
  fun i j => ⟨∑ r : Fin k, (P i r).c1 * (Q r j).c0, ∑ r : Fin k, (P i r).c2 * (Q r j).c0⟩

/-- Supermatrix product on `GrassmannSuper23 K`. -/
def mul (M₁ M₂ : GrassmannSuper23 K) : GrassmannSuper23 K where
  A := M₁.A * M₂.A + oddMul M₁.B M₂.C
  B := evenOddMul M₁.A M₂.B + oddEvenMul M₁.B M₂.D
  C := oddEvenMul M₁.C M₂.A + evenOddMul M₁.D M₂.C
  D := oddMul M₁.C M₂.B + M₁.D * M₂.D

instance : Mul (GrassmannSuper23 K) := ⟨mul⟩

/-- Scalar-part inversion for an invertible matrix over `Grassmann2Even K`:
    `E⁻¹ = E₀⁻¹ - E₀⁻¹ * (E - E₀) * E₀⁻¹` where `E₀` is the body (`c0`) matrix. -/
def bodyMatrix {n : ℕ} (E : Matrix (Fin n) (Fin n) (Grassmann2Even K)) : Matrix (Fin n) (Fin n) K :=
  fun i j => (E i j).c0

def nilpMatrix {n : ℕ} (E : Matrix (Fin n) (Fin n) (Grassmann2Even K)) : Matrix (Fin n) (Fin n) K :=
  fun i j => (E i j).c12

def embedBody {n : ℕ} (E₀ : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) (Grassmann2Even K) :=
  fun i j => ⟨E₀ i j, 0⟩

def embedNilp {n : ℕ} (E₁ : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) (Grassmann2Even K) :=
  fun i j => ⟨0, E₁ i j⟩

lemma eq_embedBody_add_embedNilp {n : ℕ} (E : Matrix (Fin n) (Fin n) (Grassmann2Even K)) :
    E = embedBody (bodyMatrix E) + embedNilp (nilpMatrix E) := by
  ext i j <;> simp [embedBody, embedNilp, bodyMatrix, nilpMatrix]

lemma embedBody_mul_embedBody {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    embedBody A * embedBody B = embedBody (A * B) := by
  ext i j <;> simp [embedBody, Matrix.mul_apply]

lemma embedBody_mul_embedNilp {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    embedBody A * embedNilp B = embedNilp (A * B) := by
  ext i j <;> simp [embedBody, embedNilp, Matrix.mul_apply]

lemma embedNilp_mul_embedBody {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    embedNilp A * embedBody B = embedNilp (A * B) := by
  ext i j <;> simp [embedBody, embedNilp, Matrix.mul_apply]

lemma embedNilp_mul_embedNilp {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    embedNilp A * embedNilp B = 0 := by
  ext i j <;> simp [embedNilp, Matrix.mul_apply]

lemma embedBody_one {n : ℕ} :
    embedBody (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [embedBody, Matrix.one_apply, h]

def evenMatInv {n : ℕ} (E : Matrix (Fin n) (Fin n) (Grassmann2Even K)) :
    Matrix (Fin n) (Fin n) (Grassmann2Even K) :=
  let E₀inv := (bodyMatrix E)⁻¹
  embedBody E₀inv - embedNilp (E₀inv * nilpMatrix E * E₀inv)

lemma evenMatInv_mul {n : ℕ} (E : Matrix (Fin n) (Fin n) (Grassmann2Even K))
    (hE : (bodyMatrix E).det ≠ 0) :
    E * evenMatInv E = 1 ∧ evenMatInv E * E = 1 := by
  have h0r : bodyMatrix E * (bodyMatrix E)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (bodyMatrix E) (isUnit_iff_ne_zero.mpr hE)
  have h0l : (bodyMatrix E)⁻¹ * bodyMatrix E = 1 :=
    Matrix.nonsing_inv_mul (bodyMatrix E) (isUnit_iff_ne_zero.mpr hE)
  have hEeq := eq_embedBody_add_embedNilp E
  dsimp [evenMatInv]
  refine ⟨?_, ?_⟩
  · calc
      E * (embedBody (bodyMatrix E)⁻¹ -
          embedNilp ((bodyMatrix E)⁻¹ * nilpMatrix E * (bodyMatrix E)⁻¹)) =
        (embedBody (bodyMatrix E) + embedNilp (nilpMatrix E)) *
          (embedBody (bodyMatrix E)⁻¹ -
            embedNilp ((bodyMatrix E)⁻¹ * nilpMatrix E * (bodyMatrix E)⁻¹)) := by rw [← hEeq]
      _ = embedBody (bodyMatrix E * (bodyMatrix E)⁻¹) -
            embedNilp (bodyMatrix E * ((bodyMatrix E)⁻¹ * nilpMatrix E * (bodyMatrix E)⁻¹)) +
            (embedNilp (nilpMatrix E * (bodyMatrix E)⁻¹) - 0) := by
        rw [add_mul, mul_sub, mul_sub, embedBody_mul_embedBody, embedBody_mul_embedNilp,
          embedNilp_mul_embedBody, embedNilp_mul_embedNilp]
      _ = embedBody 1 := by
        rw [sub_zero, h0r, ← Matrix.mul_assoc (bodyMatrix E), ← Matrix.mul_assoc (bodyMatrix E), h0r,
          Matrix.one_mul, sub_add_cancel]
      _ = 1 := embedBody_one
  · calc
      (embedBody (bodyMatrix E)⁻¹ -
          embedNilp ((bodyMatrix E)⁻¹ * nilpMatrix E * (bodyMatrix E)⁻¹)) * E =
        (embedBody (bodyMatrix E)⁻¹ -
            embedNilp ((bodyMatrix E)⁻¹ * nilpMatrix E * (bodyMatrix E)⁻¹)) *
          (embedBody (bodyMatrix E) + embedNilp (nilpMatrix E)) := by rw [← hEeq]
      _ = embedBody ((bodyMatrix E)⁻¹ * bodyMatrix E) +
            embedNilp ((bodyMatrix E)⁻¹ * nilpMatrix E) -
            (embedNilp (((bodyMatrix E)⁻¹ * nilpMatrix E * (bodyMatrix E)⁻¹) * bodyMatrix E) + 0) := by
        rw [sub_mul, mul_add, mul_add, embedBody_mul_embedBody, embedBody_mul_embedNilp,
          embedNilp_mul_embedBody, embedNilp_mul_embedNilp]
      _ = embedBody 1 := by
        rw [add_zero, h0l, Matrix.mul_assoc _ (bodyMatrix E)⁻¹ (bodyMatrix E), h0l, Matrix.mul_one,
          add_sub_cancel_right]
      _ = 1 := embedBody_one

lemma bodyMatrix_evenMatInv {n : ℕ} (E : Matrix (Fin n) (Fin n) (Grassmann2Even K)) :
    bodyMatrix (evenMatInv E) = (bodyMatrix E)⁻¹ := by
  ext i j; simp [evenMatInv, bodyMatrix, embedBody, embedNilp]

lemma det_embedBody_add_embedNilp_two
    (E₀ E₁ : Matrix (Fin 2) (Fin 2) K) (hE₀ : E₀.det ≠ 0) :
    (embedBody E₀ + embedNilp E₁).det =
      ⟨E₀.det, 0⟩ * ⟨1, Matrix.trace (E₀⁻¹ * E₁)⟩ := by
  have hadj : E₀⁻¹ = E₀.det⁻¹ • Matrix.adjugate E₀ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [Matrix.det_fin_two] at hE₀
  rw [Matrix.det_fin_two, hadj]
  ext
  · simp [embedBody, embedNilp, Matrix.det_fin_two]
  · simp [embedBody, embedNilp, Matrix.det_fin_two, Matrix.trace, Matrix.diag,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hE₀]
    ring

lemma det_embedBody_add_embedNilp_three
    (E₀ E₁ : Matrix (Fin 3) (Fin 3) K) (hE₀ : E₀.det ≠ 0) :
    (embedBody E₀ + embedNilp E₁).det =
      ⟨E₀.det, 0⟩ * ⟨1, Matrix.trace (E₀⁻¹ * E₁)⟩ := by
  have hadj : E₀⁻¹ = E₀.det⁻¹ • Matrix.adjugate E₀ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have htr :
      E₀.det * Matrix.trace (E₀⁻¹ * E₁) = Matrix.trace (Matrix.adjugate E₀ * E₁) := by
    rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hE₀, one_mul]
  have hdet0 : ((embedBody E₀ + embedNilp E₁).det).c0 = E₀.det := by
    simp [Matrix.det_fin_three, embedBody, embedNilp]
  have hdet12 :
      ((embedBody E₀ + embedNilp E₁).det).c12 = Matrix.trace (Matrix.adjugate E₀ * E₁) := by
    simp only [Matrix.det_fin_three, embedBody, embedNilp, Matrix.add_apply,
      Grassmann2Even.add_c0, Grassmann2Even.add_c12, Grassmann2Even.mul_c0,
      Grassmann2Even.mul_c12, Grassmann2Even.sub_c12,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.adjugate_apply,
      Fin.sum_univ_three]
    simp [Matrix.updateRow_apply]
    ring
  ext
  · simp [hdet0]
  · simp only [Grassmann2Even.mul_c12, mul_zero, zero_mul, add_zero]
    rw [hdet12, ← htr]

/-- Exact Grassmann UDL Berezinian `det(A - B D⁻¹ C) * inv(det D)` in `Grassmann2Even K`. -/
def grassmannBerUDL (M : GrassmannSuper23 K) : Grassmann2Even K :=
  (M.A - oddMul M.B (evenOddMul (evenMatInv M.D) M.C)).det *
    grassmannEvenInv M.D.det

/-- Exact Grassmann LDU Berezinian `det(A) * inv(det(D - C A⁻¹ B))` in `Grassmann2Even K`. -/
def grassmannBerLDU (M : GrassmannSuper23 K) : Grassmann2Even K :=
  M.A.det * grassmannEvenInv (M.D - oddMul M.C (evenOddMul (evenMatInv M.A) M.B)).det

private def oddTrPair {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K))
    (Q : Matrix (Fin n) (Fin m) (Grassmann2Odd K)) : K :=
  ∑ i : Fin m, ∑ r : Fin n, (grassmannOddMul (P i r) (Q r i)).c12

private lemma scalar_pair_anticomm {K : Type*} [CommRing K] (a₁ a₂ b₁ b₂ : K) :
    a₁ * b₂ - a₂ * b₁ = -(b₁ * a₂ - b₂ * a₁) := by
  ring

private lemma scalar_sub_add_split {K : Type*} [CommRing K] (a₁ a₂ b₁ b₂ : K) :
    (a₁ + a₂) - (b₁ + b₂) = (a₁ - b₁) + (a₂ - b₂) := by
  ring

private lemma scalar_mul3_cycle_right {K : Type*} [CommRing K] (a b c : K) :
    a * b * c = a * (b * c) := by
  ring

private lemma oddTrPair_anticomm {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K))
    (Q : Matrix (Fin n) (Fin m) (Grassmann2Odd K)) :
    oddTrPair Q P = -oddTrPair P Q := by
  dsimp [oddTrPair, grassmannOddMul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro r _
  exact scalar_pair_anticomm (Q r i).c1 (Q r i).c2 (P i r).c1 (P i r).c2

private lemma oddTrPair_add_left {m n : ℕ}
    (P₁ P₂ : Matrix (Fin m) (Fin n) (Grassmann2Odd K))
    (Q : Matrix (Fin n) (Fin m) (Grassmann2Odd K)) :
    oddTrPair (P₁ + P₂) Q = oddTrPair P₁ Q + oddTrPair P₂ Q := by
  dsimp [oddTrPair, grassmannOddMul]
  have hsplit : ∀ a₁ a₂ b₁ b₂ : K, (a₁ + a₂) - (b₁ + b₂) = (a₁ - b₁) + (a₂ - b₂) :=
    scalar_sub_add_split
  simp only [Matrix.add_apply, Grassmann2Odd.add_c1, Grassmann2Odd.add_c2,
    add_mul, hsplit, Finset.sum_add_distrib]

private lemma oddTrPair_add_right {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K))
    (Q₁ Q₂ : Matrix (Fin n) (Fin m) (Grassmann2Odd K)) :
    oddTrPair P (Q₁ + Q₂) = oddTrPair P Q₁ + oddTrPair P Q₂ := by
  dsimp [oddTrPair, grassmannOddMul]
  have hsplit : ∀ a₁ a₂ b₁ b₂ : K, (a₁ + a₂) - (b₁ + b₂) = (a₁ - b₁) + (a₂ - b₂) :=
    scalar_sub_add_split
  simp only [Matrix.add_apply, Grassmann2Odd.add_c1, Grassmann2Odd.add_c2,
    mul_add, hsplit, Finset.sum_add_distrib]

private lemma evenOddMul_embedBody_assoc {m n : ℕ}
    (X Y : Matrix (Fin m) (Fin m) K) (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K)) :
    evenOddMul (embedBody X) (evenOddMul (embedBody Y) P) = evenOddMul (embedBody (X * Y)) P := by
  ext i j <;>
  · simp [evenOddMul, embedBody, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro r _
    refine Finset.sum_congr rfl ?_
    intro s _
    ring

private lemma oddEvenMul_embedBody_assoc {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K)) (X Y : Matrix (Fin n) (Fin n) K) :
    oddEvenMul (oddEvenMul P (embedBody X)) (embedBody Y) = oddEvenMul P (embedBody (X * Y)) := by
  ext i j <;>
  · simp [oddEvenMul, embedBody, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro r _
    refine Finset.sum_congr rfl ?_
    intro s _
    ring

private lemma evenOddMul_oddEvenMul {m k : ℕ}
    (X : Matrix (Fin m) (Fin m) K) (P : Matrix (Fin m) (Fin k) (Grassmann2Odd K))
    (Y : Matrix (Fin k) (Fin k) K) :
    evenOddMul (embedBody X) (oddEvenMul P (embedBody Y)) =
      oddEvenMul (evenOddMul (embedBody X) P) (embedBody Y) := by
  ext i j <;>
  · simp [evenOddMul, oddEvenMul, embedBody, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro r _
    refine Finset.sum_congr rfl ?_
    intro s _
    ring

private lemma oddTrPair_evenOdd_oddEven_cycle {m n : ℕ}
    (X : Matrix (Fin m) (Fin m) K) (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K))
    (Q : Matrix (Fin n) (Fin m) (Grassmann2Odd K)) :
    oddTrPair (evenOddMul (embedBody X) P) Q =
      oddTrPair P (oddEvenMul Q (embedBody X)) := by
  dsimp [oddTrPair, evenOddMul, oddEvenMul, embedBody, grassmannOddMul]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;>
  · rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext s
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro r _
    refine Finset.sum_congr rfl ?_
    intro s _
    refine Finset.sum_congr rfl ?_
    intro i _
    ring

private lemma oddTrPair_oddEven_evenOdd_cycle {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K)) (Y : Matrix (Fin n) (Fin n) K)
    (Q : Matrix (Fin n) (Fin m) (Grassmann2Odd K)) :
    oddTrPair (oddEvenMul P (embedBody Y)) Q =
      oddTrPair P (evenOddMul (embedBody Y) Q) := by
  dsimp [oddTrPair, evenOddMul, oddEvenMul, embedBody, grassmannOddMul]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;>
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro s _
    refine Finset.sum_congr rfl ?_
    intro r _
    exact scalar_mul3_cycle_right _ _ _

private lemma trace_oddMul_mul {m k : ℕ}
    (X₀ : Matrix (Fin m) (Fin m) K)
    (P : Matrix (Fin m) (Fin k) (Grassmann2Odd K))
    (R : Matrix (Fin k) (Fin m) (Grassmann2Odd K)) :
    Matrix.trace (X₀ * nilpMatrix (oddMul P R)) =
      oddTrPair (evenOddMul (embedBody X₀) P) R := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, nilpMatrix, oddMul, evenOddMul,
    embedBody, oddTrPair, grassmannOddMul, Grassmann2Even.sum_c12,
    mul_sub, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  congr 1 <;>
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro r _
    refine Finset.sum_congr rfl ?_
    intro k _
    ring

private lemma grassmannBerUDL_formula (M : GrassmannSuper23 K)
    (hA : (bodyMatrix M.A).det ≠ 0) (hD : (bodyMatrix M.D).det ≠ 0) :
    grassmannBerUDL M =
      ⟨(bodyMatrix M.A).det / (bodyMatrix M.D).det, 0⟩ *
        ⟨1, Matrix.trace ((bodyMatrix M.A)⁻¹ * nilpMatrix M.A) -
            Matrix.trace ((bodyMatrix M.D)⁻¹ * nilpMatrix M.D) -
            oddTrPair (evenOddMul (embedBody (bodyMatrix M.A)⁻¹) M.B)
                      (evenOddMul (embedBody (bodyMatrix M.D)⁻¹) M.C)⟩ := by
  let S := M.A - oddMul M.B (evenOddMul (evenMatInv M.D) M.C)
  have hS_body : bodyMatrix S = bodyMatrix M.A := by
    ext i j; simp [S, bodyMatrix, oddMul, grassmannOddMul]
  have hS_nilp : nilpMatrix S =
      nilpMatrix M.A - nilpMatrix (oddMul M.B (evenOddMul (embedBody (bodyMatrix M.D)⁻¹) M.C)) := by
    ext i j
    simp [S, nilpMatrix, oddMul, evenOddMul, evenMatInv, embedBody, embedNilp, grassmannOddMul]
  have hS_eq : S = embedBody (bodyMatrix M.A) + embedNilp (nilpMatrix S) := by
    rw [← hS_body]; exact eq_embedBody_add_embedNilp S
  have hD_eq : M.D = embedBody (bodyMatrix M.D) + embedNilp (nilpMatrix M.D) :=
    eq_embedBody_add_embedNilp M.D
  have hS_det : S.det = ⟨(bodyMatrix M.A).det, 0⟩ * ⟨1, Matrix.trace ((bodyMatrix M.A)⁻¹ * nilpMatrix S)⟩ := by
    nth_rw 1 [hS_eq]; exact det_embedBody_add_embedNilp_two (bodyMatrix M.A) (nilpMatrix S) hA
  have hD_det : M.D.det = ⟨(bodyMatrix M.D).det, 0⟩ * ⟨1, Matrix.trace ((bodyMatrix M.D)⁻¹ * nilpMatrix M.D)⟩ := by
    nth_rw 1 [hD_eq]; exact det_embedBody_add_embedNilp_three (bodyMatrix M.D) (nilpMatrix M.D) hD
  have hinv_D : grassmannEvenInv M.D.det =
      ⟨(bodyMatrix M.D).det⁻¹, 0⟩ * ⟨1, -Matrix.trace ((bodyMatrix M.D)⁻¹ * nilpMatrix M.D)⟩ := by
    rw [hD_det]
    ext
    · simp [grassmannEvenInv]
    · simp [grassmannEvenInv]
      rw [← mul_assoc (bodyMatrix M.D).det⁻¹, inv_mul_cancel₀ hD, one_mul]
      ring
  dsimp [grassmannBerUDL]
  change S.det * grassmannEvenInv M.D.det = _
  rw [hS_det, hinv_D, hS_nilp, Matrix.mul_sub, Matrix.trace_sub,
    trace_oddMul_mul (bodyMatrix M.A)⁻¹ M.B (evenOddMul (embedBody (bodyMatrix M.D)⁻¹) M.C)]
  ext
  · simp [div_eq_mul_inv]
  · simp [div_eq_mul_inv]; ring

private lemma grassmannBerLDU_formula (M : GrassmannSuper23 K)
    (hA : (bodyMatrix M.A).det ≠ 0) (hD : (bodyMatrix M.D).det ≠ 0) :
    grassmannBerLDU M =
      ⟨(bodyMatrix M.A).det / (bodyMatrix M.D).det, 0⟩ *
        ⟨1, Matrix.trace ((bodyMatrix M.A)⁻¹ * nilpMatrix M.A) -
            Matrix.trace ((bodyMatrix M.D)⁻¹ * nilpMatrix M.D) +
            oddTrPair (evenOddMul (embedBody (bodyMatrix M.D)⁻¹) M.C)
                      (evenOddMul (embedBody (bodyMatrix M.A)⁻¹) M.B)⟩ := by
  let S := M.D - oddMul M.C (evenOddMul (evenMatInv M.A) M.B)
  have hS_body : bodyMatrix S = bodyMatrix M.D := by
    ext i j; simp [S, bodyMatrix, oddMul, grassmannOddMul]
  have hS_nilp : nilpMatrix S =
      nilpMatrix M.D - nilpMatrix (oddMul M.C (evenOddMul (embedBody (bodyMatrix M.A)⁻¹) M.B)) := by
    ext i j
    simp [S, nilpMatrix, oddMul, evenOddMul, evenMatInv, embedBody, embedNilp, grassmannOddMul]
  have hS_eq : S = embedBody (bodyMatrix M.D) + embedNilp (nilpMatrix S) := by
    rw [← hS_body]; exact eq_embedBody_add_embedNilp S
  have hA_eq : M.A = embedBody (bodyMatrix M.A) + embedNilp (nilpMatrix M.A) :=
    eq_embedBody_add_embedNilp M.A
  have hA_det : M.A.det = ⟨(bodyMatrix M.A).det, 0⟩ * ⟨1, Matrix.trace ((bodyMatrix M.A)⁻¹ * nilpMatrix M.A)⟩ := by
    nth_rw 1 [hA_eq]; exact det_embedBody_add_embedNilp_two (bodyMatrix M.A) (nilpMatrix M.A) hA
  have hS_det : S.det = ⟨(bodyMatrix M.D).det, 0⟩ * ⟨1, Matrix.trace ((bodyMatrix M.D)⁻¹ * nilpMatrix S)⟩ := by
    nth_rw 1 [hS_eq]; exact det_embedBody_add_embedNilp_three (bodyMatrix M.D) (nilpMatrix S) hD
  have hinv_S : grassmannEvenInv S.det =
      ⟨(bodyMatrix M.D).det⁻¹, 0⟩ * ⟨1, -Matrix.trace ((bodyMatrix M.D)⁻¹ * nilpMatrix S)⟩ := by
    rw [hS_det]
    ext
    · simp [grassmannEvenInv]
    · simp [grassmannEvenInv]
      rw [← mul_assoc (bodyMatrix M.D).det⁻¹, inv_mul_cancel₀ hD, one_mul]
      ring
  dsimp [grassmannBerLDU]
  change M.A.det * grassmannEvenInv S.det = _
  rw [hA_det, hinv_S, hS_nilp, Matrix.mul_sub, Matrix.trace_sub,
    trace_oddMul_mul (bodyMatrix M.D)⁻¹ M.C (evenOddMul (embedBody (bodyMatrix M.A)⁻¹) M.B)]
  ext
  · simp [div_eq_mul_inv]
  · simp [div_eq_mul_inv]; ring

/-- **Exact Full `(2|3)` Grassmann Super-Berezinian UDL = LDU Duality & Multiplicativity Theorem**:
    Over the concrete Grassmann superalgebra `Grassmann2Even K ⊕ Grassmann2Odd K`, for ALL
    invertible `(2|3)` supermatrices `M, M₁, M₂`:
    1. **Exact UDL ↔ LDU Berezinian Duality**: `grassmannBerUDL M = grassmannBerLDU M`.
    2. **Full `(2|3)` Super-Berezinian Multiplicativity**:
       `grassmannBerUDL (M₁ * M₂) = grassmannBerUDL M₁ * grassmannBerUDL M₂`! -/
theorem grassmann_super_berezinian23_duality_and_multiplicativity
    (M M₁ M₂ : GrassmannSuper23 K)
    (hA : (bodyMatrix M.A).det ≠ 0) (hD : (bodyMatrix M.D).det ≠ 0)
    (hA₁ : (bodyMatrix M₁.A).det ≠ 0) (hD₁ : (bodyMatrix M₁.D).det ≠ 0)
    (hA₂ : (bodyMatrix M₂.A).det ≠ 0) (hD₂ : (bodyMatrix M₂.D).det ≠ 0) :
    grassmannBerUDL M = grassmannBerLDU M ∧
    grassmannBerUDL (M₁ * M₂) = grassmannBerUDL M₁ * grassmannBerUDL M₂ := by
  refine ⟨?_, ?_⟩
  · rw [grassmannBerUDL_formula M hA hD, grassmannBerLDU_formula M hA hD, oddTrPair_anticomm]
    ext <;> simp <;> ring
  · have hmul_gs : ∀ P Q : GrassmannSuper23 K, P * Q = GrassmannSuper23.mul P Q := fun _ _ => rfl
    have hM_A_body : bodyMatrix (M₁ * M₂).A = bodyMatrix M₁.A * bodyMatrix M₂.A := by
      rw [hmul_gs]
      ext i j
      simp [GrassmannSuper23.mul, bodyMatrix, oddMul, grassmannOddMul, Matrix.mul_apply]
    have hM_D_body : bodyMatrix (M₁ * M₂).D = bodyMatrix M₁.D * bodyMatrix M₂.D := by
      rw [hmul_gs]
      ext i j
      simp [GrassmannSuper23.mul, bodyMatrix, oddMul, grassmannOddMul, Matrix.mul_apply]
    have hA12 : (bodyMatrix (M₁ * M₂).A).det ≠ 0 := by
      rw [hM_A_body, Matrix.det_mul]; exact mul_ne_zero hA₁ hA₂
    have hD12 : (bodyMatrix (M₁ * M₂).D).det ≠ 0 := by
      rw [hM_D_body, Matrix.det_mul]; exact mul_ne_zero hD₁ hD₂
    rw [grassmannBerUDL_formula (M₁ * M₂) hA12 hD12,
      grassmannBerUDL_formula M₁ hA₁ hD₁, grassmannBerUDL_formula M₂ hA₂ hD₂]
    have hA_nilp : nilpMatrix (M₁ * M₂).A =
        bodyMatrix M₁.A * nilpMatrix M₂.A + nilpMatrix M₁.A * bodyMatrix M₂.A +
        nilpMatrix (oddMul M₁.B M₂.C) := by
      rw [hmul_gs]
      ext i j
      simp [GrassmannSuper23.mul, bodyMatrix, nilpMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hD_nilp : nilpMatrix (M₁ * M₂).D =
        bodyMatrix M₁.D * nilpMatrix M₂.D + nilpMatrix M₁.D * bodyMatrix M₂.D +
        nilpMatrix (oddMul M₁.C M₂.B) := by
      rw [hmul_gs]
      ext i j
      simp [GrassmannSuper23.mul, bodyMatrix, nilpMatrix, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    have hA_inv : (bodyMatrix (M₁ * M₂).A)⁻¹ = (bodyMatrix M₂.A)⁻¹ * (bodyMatrix M₁.A)⁻¹ := by
      rw [hM_A_body, Matrix.mul_inv_rev]
    have hD_inv : (bodyMatrix (M₁ * M₂).D)⁻¹ = (bodyMatrix M₂.D)⁻¹ * (bodyMatrix M₁.D)⁻¹ := by
      rw [hM_D_body, Matrix.mul_inv_rev]
    have hA₁_inv_r : bodyMatrix M₁.A * (bodyMatrix M₁.A)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA₁)
    have hA₂_inv_r : bodyMatrix M₂.A * (bodyMatrix M₂.A)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA₂)
    have hA₁_inv_l : (bodyMatrix M₁.A)⁻¹ * bodyMatrix M₁.A = 1 :=
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA₁)
    have hA₂_inv_l : (bodyMatrix M₂.A)⁻¹ * bodyMatrix M₂.A = 1 :=
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA₂)
    have hD₁_inv_r : bodyMatrix M₁.D * (bodyMatrix M₁.D)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD₁)
    have hD₂_inv_r : bodyMatrix M₂.D * (bodyMatrix M₂.D)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD₂)
    have hD₁_inv_l : (bodyMatrix M₁.D)⁻¹ * bodyMatrix M₁.D = 1 :=
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hD₁)
    have hD₂_inv_l : (bodyMatrix M₂.D)⁻¹ * bodyMatrix M₂.D = 1 :=
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hD₂)
    have htrA :
        Matrix.trace ((bodyMatrix (M₁ * M₂).A)⁻¹ * nilpMatrix (M₁ * M₂).A) =
          Matrix.trace ((bodyMatrix M₁.A)⁻¹ * nilpMatrix M₁.A) +
          Matrix.trace ((bodyMatrix M₂.A)⁻¹ * nilpMatrix M₂.A) +
          oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
                    (oddEvenMul M₂.C (embedBody (bodyMatrix M₂.A)⁻¹)) := by
      rw [hA_inv, hA_nilp, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add]
      have ht1 :
          Matrix.trace (((bodyMatrix M₂.A)⁻¹ * (bodyMatrix M₁.A)⁻¹) *
              (bodyMatrix M₁.A * nilpMatrix M₂.A)) =
            Matrix.trace ((bodyMatrix M₂.A)⁻¹ * nilpMatrix M₂.A) := by
        rw [Matrix.mul_assoc (bodyMatrix M₂.A)⁻¹, ← Matrix.mul_assoc (bodyMatrix M₁.A)⁻¹,
          hA₁_inv_l, Matrix.one_mul]
      have ht2 :
          Matrix.trace (((bodyMatrix M₂.A)⁻¹ * (bodyMatrix M₁.A)⁻¹) *
              (nilpMatrix M₁.A * bodyMatrix M₂.A)) =
            Matrix.trace ((bodyMatrix M₁.A)⁻¹ * nilpMatrix M₁.A) := by
        rw [Matrix.trace_mul_comm ((bodyMatrix M₂.A)⁻¹ * (bodyMatrix M₁.A)⁻¹),
          ← Matrix.mul_assoc, Matrix.mul_assoc (nilpMatrix M₁.A), hA₂_inv_r, Matrix.mul_one,
          Matrix.trace_mul_comm]
      have ht3 :
          Matrix.trace (((bodyMatrix M₂.A)⁻¹ * (bodyMatrix M₁.A)⁻¹) *
              nilpMatrix (oddMul M₁.B M₂.C)) =
            oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
                      (oddEvenMul M₂.C (embedBody (bodyMatrix M₂.A)⁻¹)) := by
        rw [trace_oddMul_mul ((bodyMatrix M₂.A)⁻¹ * (bodyMatrix M₁.A)⁻¹) M₁.B M₂.C,
          ← evenOddMul_embedBody_assoc, oddTrPair_evenOdd_oddEven_cycle]
      rw [ht1, ht2, ht3]; ring
    have htrD :
        Matrix.trace ((bodyMatrix (M₁ * M₂).D)⁻¹ * nilpMatrix (M₁ * M₂).D) =
          Matrix.trace ((bodyMatrix M₁.D)⁻¹ * nilpMatrix M₁.D) +
          Matrix.trace ((bodyMatrix M₂.D)⁻¹ * nilpMatrix M₂.D) +
          oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C)
                    (oddEvenMul M₂.B (embedBody (bodyMatrix M₂.D)⁻¹)) := by
      rw [hD_inv, hD_nilp, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add]
      have ht1 :
          Matrix.trace (((bodyMatrix M₂.D)⁻¹ * (bodyMatrix M₁.D)⁻¹) *
              (bodyMatrix M₁.D * nilpMatrix M₂.D)) =
            Matrix.trace ((bodyMatrix M₂.D)⁻¹ * nilpMatrix M₂.D) := by
        rw [Matrix.mul_assoc (bodyMatrix M₂.D)⁻¹, ← Matrix.mul_assoc (bodyMatrix M₁.D)⁻¹,
          hD₁_inv_l, Matrix.one_mul]
      have ht2 :
          Matrix.trace (((bodyMatrix M₂.D)⁻¹ * (bodyMatrix M₁.D)⁻¹) *
              (nilpMatrix M₁.D * bodyMatrix M₂.D)) =
            Matrix.trace ((bodyMatrix M₁.D)⁻¹ * nilpMatrix M₁.D) := by
        rw [Matrix.trace_mul_comm ((bodyMatrix M₂.D)⁻¹ * (bodyMatrix M₁.D)⁻¹),
          ← Matrix.mul_assoc, Matrix.mul_assoc (nilpMatrix M₁.D), hD₂_inv_r, Matrix.mul_one,
          Matrix.trace_mul_comm]
      have ht3 :
          Matrix.trace (((bodyMatrix M₂.D)⁻¹ * (bodyMatrix M₁.D)⁻¹) *
              nilpMatrix (oddMul M₁.C M₂.B)) =
            oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C)
                      (oddEvenMul M₂.B (embedBody (bodyMatrix M₂.D)⁻¹)) := by
        rw [trace_oddMul_mul ((bodyMatrix M₂.D)⁻¹ * (bodyMatrix M₁.D)⁻¹) M₁.C M₂.B,
          ← evenOddMul_embedBody_assoc, oddTrPair_evenOdd_oddEven_cycle]
      rw [ht1, ht2, ht3]; ring
    have evenOddMul_add : ∀ {m k n : ℕ} (X : Matrix (Fin m) (Fin k) (Grassmann2Even K))
        (P Q : Matrix (Fin k) (Fin n) (Grassmann2Odd K)),
        evenOddMul X (P + Q) = evenOddMul X P + evenOddMul X Q := by
      intro m k n X P Q
      ext i j <;> simp [evenOddMul, mul_add, Finset.sum_add_distrib]
    have evenOddMul_one : ∀ {m n : ℕ} (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K)),
        evenOddMul (embedBody (1 : Matrix (Fin m) (Fin m) K)) P = P := by
      intro m n P
      ext i j <;> simp [evenOddMul, embedBody, Matrix.one_apply]
    have oddEvenMul_one : ∀ {m n : ℕ} (P : Matrix (Fin m) (Fin n) (Grassmann2Odd K)),
        oddEvenMul P (embedBody (1 : Matrix (Fin n) (Fin n) K)) = P := by
      intro m n P
      ext i j <;> simp [oddEvenMul, embedBody, Matrix.one_apply]
    have h_B12 :
        evenOddMul (embedBody (bodyMatrix (M₁ * M₂).A)⁻¹) (M₁ * M₂).B =
          evenOddMul (embedBody (bodyMatrix M₂.A)⁻¹) M₂.B +
          evenOddMul (embedBody (bodyMatrix M₂.A)⁻¹)
            (oddEvenMul (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
              (embedBody (bodyMatrix M₂.D))) := by
      have hB : (M₁ * M₂).B =
          evenOddMul (embedBody (bodyMatrix M₁.A)) M₂.B +
          oddEvenMul M₁.B (embedBody (bodyMatrix M₂.D)) := rfl
      rw [hA_inv, hB, evenOddMul_add, ← evenOddMul_embedBody_assoc,
        evenOddMul_embedBody_assoc (bodyMatrix M₁.A)⁻¹ (bodyMatrix M₁.A), hA₁_inv_l,
        evenOddMul_one, ← evenOddMul_embedBody_assoc (bodyMatrix M₂.A)⁻¹ (bodyMatrix M₁.A)⁻¹,
        evenOddMul_oddEvenMul (bodyMatrix M₁.A)⁻¹ M₁.B (bodyMatrix M₂.D)]
    have h_C12 :
        evenOddMul (embedBody (bodyMatrix (M₁ * M₂).D)⁻¹) (M₁ * M₂).C =
          evenOddMul (embedBody (bodyMatrix M₂.D)⁻¹)
            (oddEvenMul (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C)
              (embedBody (bodyMatrix M₂.A))) +
          evenOddMul (embedBody (bodyMatrix M₂.D)⁻¹) M₂.C := by
      have hC : (M₁ * M₂).C =
          oddEvenMul M₁.C (embedBody (bodyMatrix M₂.A)) +
          evenOddMul (embedBody (bodyMatrix M₁.D)) M₂.C := rfl
      rw [hD_inv, hC, evenOddMul_add,
        ← evenOddMul_embedBody_assoc (bodyMatrix M₂.D)⁻¹ (bodyMatrix M₁.D)⁻¹,
        evenOddMul_oddEvenMul (bodyMatrix M₁.D)⁻¹ M₁.C (bodyMatrix M₂.A),
        ← evenOddMul_embedBody_assoc (bodyMatrix M₂.D)⁻¹ (bodyMatrix M₁.D)⁻¹,
        evenOddMul_embedBody_assoc (bodyMatrix M₁.D)⁻¹ (bodyMatrix M₁.D), hD₁_inv_l,
        evenOddMul_one]
    have h_pair12 :
        oddTrPair (evenOddMul (embedBody (bodyMatrix (M₁ * M₂).A)⁻¹) (M₁ * M₂).B)
                  (evenOddMul (embedBody (bodyMatrix (M₁ * M₂).D)⁻¹) (M₁ * M₂).C) =
          oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
                    (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C) +
          oddTrPair (evenOddMul (embedBody (bodyMatrix M₂.A)⁻¹) M₂.B)
                    (evenOddMul (embedBody (bodyMatrix M₂.D)⁻¹) M₂.C) +
          oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
                    (oddEvenMul M₂.C (embedBody (bodyMatrix M₂.A)⁻¹)) -
          oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C)
                    (oddEvenMul M₂.B (embedBody (bodyMatrix M₂.D)⁻¹)) := by
      rw [h_B12, h_C12, oddTrPair_add_left, oddTrPair_add_right, oddTrPair_add_right]
      -- Simplify each of the 4 cross terms
      have t21 :
          oddTrPair (evenOddMul (embedBody (bodyMatrix M₂.A)⁻¹) M₂.B)
            (evenOddMul (embedBody (bodyMatrix M₂.D)⁻¹)
              (oddEvenMul (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C)
                (embedBody (bodyMatrix M₂.A)))) =
            -oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C)
              (oddEvenMul M₂.B (embedBody (bodyMatrix M₂.D)⁻¹)) := by
        rw [oddTrPair_evenOdd_oddEven_cycle, evenOddMul_oddEvenMul, oddEvenMul_embedBody_assoc,
          hA₂_inv_r, oddEvenMul_one, oddTrPair_anticomm, oddTrPair_evenOdd_oddEven_cycle]
      have t12 :
          oddTrPair
            (evenOddMul (embedBody (bodyMatrix M₂.A)⁻¹)
              (oddEvenMul (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
                (embedBody (bodyMatrix M₂.D))))
            (evenOddMul (embedBody (bodyMatrix M₂.D)⁻¹) M₂.C) =
            oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
              (oddEvenMul M₂.C (embedBody (bodyMatrix M₂.A)⁻¹)) := by
        rw [oddTrPair_evenOdd_oddEven_cycle, oddTrPair_oddEven_evenOdd_cycle,
          ← evenOddMul_oddEvenMul, evenOddMul_embedBody_assoc, hD₂_inv_r, evenOddMul_one]
      have t11 :
          oddTrPair
            (evenOddMul (embedBody (bodyMatrix M₂.A)⁻¹)
              (oddEvenMul (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
                (embedBody (bodyMatrix M₂.D))))
            (evenOddMul (embedBody (bodyMatrix M₂.D)⁻¹)
              (oddEvenMul (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C)
                (embedBody (bodyMatrix M₂.A)))) =
            oddTrPair (evenOddMul (embedBody (bodyMatrix M₁.A)⁻¹) M₁.B)
              (evenOddMul (embedBody (bodyMatrix M₁.D)⁻¹) M₁.C) := by
        rw [oddTrPair_evenOdd_oddEven_cycle, evenOddMul_oddEvenMul, oddEvenMul_embedBody_assoc,
          hA₂_inv_r, oddEvenMul_one, oddTrPair_oddEven_evenOdd_cycle,
          evenOddMul_embedBody_assoc, hD₂_inv_r, evenOddMul_one]
      rw [t21, t12, t11]
      ring
    rw [htrA, htrD, h_pair12, hM_A_body, hM_D_body]
    simp only [Matrix.det_mul]
    ext
    · simp [div_mul_div_comm]
    · simp; try (field_simp [hD₁, hD₂]; ring)

end GrassmannSuper23

/-! ### White Vacuum Singlets vs Color Triplets/Antitriplets across `Cl55`, `NCZorn`, `ZornVectorMatrix`, `ZornSplitOctonion`, and 5-Graded Super-Jacobi Closure -/

/-- Canonical multiplicative & additive equivalence `NCZorn R ≃ ZornVectorMatrix R`. -/
def ncZornVectorMatrixEquiv (R : Type*) :
    InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn R ≃
      InfoGeometry.Algebra.ZornVectorMatrix R where
  toFun X := ⟨X.a, X.u, X.v, X.b⟩
  invFun Y := ⟨Y.a, Y.v, Y.w, Y.b⟩
  left_inv X := by cases X; rfl
  right_inv Y := by cases Y; rfl

/-- Canonical 8D chain equivalence `NCZorn R ≃ ZornSplitOctonion R` via `ZornVectorMatrix R`. -/
def ncZornSplitOctonionEquiv (R : Type*) :
    InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn R ≃ ZornSplitOctonion R :=
  (ncZornVectorMatrixEquiv R).trans (zornVectorMatrixSplitOctonionEquiv R)

/-- $\mathbb{Z}_2 \times \mathbb{Z}_2$-graded super-Lie bracket `[X, Y]_s = X * Y - ε(g₁, g₂) (Y * X)`
    in any associative `ℝ`-algebra. -/
def z2z2SuperBracket {A : Type*} [Ring A] [Algebra ℝ A]
    (g₁ g₂ : Z2Z2ColorGrade) (X Y : A) : A :=
  X * Y - z2z2KoszulSign g₁ g₂ • (Y * X)

/-- Addition of `Z2Z2ColorGrade` in `Fin 2 × Fin 2`. -/
def addZ2Z2Grade (g₁ g₂ : Z2Z2ColorGrade) : Z2Z2ColorGrade :=
  (g₁.1 + g₂.1, g₁.2 + g₂.2)

private lemma z2z2KoszulSign_add_right (g₁ g₂ g₃ : Z2Z2ColorGrade) :
    z2z2KoszulSign g₁ (addZ2Z2Grade g₂ g₃) =
      z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₁ g₃ := by
  rcases g₁ with ⟨a₁, b₁⟩
  rcases g₂ with ⟨a₂, b₂⟩
  rcases g₃ with ⟨a₃, b₃⟩
  dsimp [z2z2KoszulSign, z2z2Pairing, addZ2Z2Grade]
  fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂ <;>
    fin_cases a₃ <;> fin_cases b₃ <;> norm_num

/-- **Exact $\mathbb{Z}_2 \times \mathbb{Z}_2$ Colored Super-Jacobi Identity & Super-Skewsymmetry**:
    For all homogeneous operators `(X, g₁), (Y, g₂), (Z, g₃)` in any associative `ℝ`-algebra:
    1. `[X, Y]_s = -ε(g₁, g₂) • [Y, X]_s`.
    2. `ε(g₁, g₃) • [X, [Y, Z]_s]_s + ε(g₂, g₁) • [Y, [Z, X]_s]_s + ε(g₃, g₂) • [Z, [X, Y]_s]_s = 0`! -/
theorem z2z2_colored_super_jacobi {A : Type*} [Ring A] [Algebra ℝ A]
    (g₁ g₂ g₃ : Z2Z2ColorGrade) (X Y Z : A) :
    z2z2SuperBracket g₁ g₂ X Y =
      -(z2z2KoszulSign g₁ g₂ • z2z2SuperBracket g₂ g₁ Y X) ∧
    z2z2KoszulSign g₁ g₃ •
        z2z2SuperBracket g₁ (addZ2Z2Grade g₂ g₃) X (z2z2SuperBracket g₂ g₃ Y Z) +
      z2z2KoszulSign g₂ g₁ •
        z2z2SuperBracket g₂ (addZ2Z2Grade g₃ g₁) Y (z2z2SuperBracket g₃ g₁ Z X) +
      z2z2KoszulSign g₃ g₂ •
        z2z2SuperBracket g₃ (addZ2Z2Grade g₁ g₂) Z (z2z2SuperBracket g₁ g₂ X Y) = 0 := by
  have h12 := (z2z2_color_supersymmetry_sign_laws g₁ g₂).2.1
  have h13 := (z2z2_color_supersymmetry_sign_laws g₁ g₃).2.1
  have h21 := (z2z2_color_supersymmetry_sign_laws g₂ g₁).2.1
  have h23 := (z2z2_color_supersymmetry_sign_laws g₂ g₃).2.1
  have h31 := (z2z2_color_supersymmetry_sign_laws g₃ g₁).2.1
  have h32 := (z2z2_color_supersymmetry_sign_laws g₃ g₂).2.1
  have hs12 : z2z2KoszulSign g₁ g₂ = z2z2KoszulSign g₂ g₁ :=
    (z2z2_color_supersymmetry_sign_laws g₁ g₂).1
  have hs13 : z2z2KoszulSign g₁ g₃ = z2z2KoszulSign g₃ g₁ :=
    (z2z2_color_supersymmetry_sign_laws g₁ g₃).1
  have hs23 : z2z2KoszulSign g₂ g₃ = z2z2KoszulSign g₃ g₂ :=
    (z2z2_color_supersymmetry_sign_laws g₂ g₃).1
  refine ⟨?_, ?_⟩
  · dsimp [z2z2SuperBracket]
    rw [smul_sub, smul_smul, ← hs12, h12, one_smul]
    abel
  · dsimp [z2z2SuperBracket]
    rw [z2z2KoszulSign_add_right g₁ g₂ g₃,
      z2z2KoszulSign_add_right g₂ g₃ g₁,
      z2z2KoszulSign_add_right g₃ g₁ g₂]
    simp only [mul_sub, sub_mul, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    have ha : (z2z2KoszulSign g₁ g₃ * (z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₁ g₃)) =
        z2z2KoszulSign g₁ g₂ := by
      calc z2z2KoszulSign g₁ g₃ * (z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₁ g₃)
          = (z2z2KoszulSign g₁ g₃ * z2z2KoszulSign g₁ g₃) * z2z2KoszulSign g₁ g₂ := by ring
      _ = z2z2KoszulSign g₁ g₂ := by rw [h13, one_mul]
    have hb : (z2z2KoszulSign g₂ g₁ * (z2z2KoszulSign g₂ g₃ * z2z2KoszulSign g₂ g₁)) =
        z2z2KoszulSign g₂ g₃ := by
      calc z2z2KoszulSign g₂ g₁ * (z2z2KoszulSign g₂ g₃ * z2z2KoszulSign g₂ g₁)
          = (z2z2KoszulSign g₂ g₁ * z2z2KoszulSign g₂ g₁) * z2z2KoszulSign g₂ g₃ := by ring
      _ = z2z2KoszulSign g₂ g₃ := by rw [h21, one_mul]
    have hc : (z2z2KoszulSign g₃ g₂ * (z2z2KoszulSign g₃ g₁ * z2z2KoszulSign g₃ g₂)) =
        z2z2KoszulSign g₃ g₁ := by
      calc z2z2KoszulSign g₃ g₂ * (z2z2KoszulSign g₃ g₁ * z2z2KoszulSign g₃ g₂)
          = (z2z2KoszulSign g₃ g₂ * z2z2KoszulSign g₃ g₂) * z2z2KoszulSign g₃ g₁ := by ring
      _ = z2z2KoszulSign g₃ g₁ := by rw [h32, one_mul]
    have hab : (z2z2KoszulSign g₁ g₃ * (z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₁ g₃ * z2z2KoszulSign g₂ g₃)) =
        z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₂ g₃ := by
      calc _ = (z2z2KoszulSign g₁ g₃ * z2z2KoszulSign g₁ g₃) *
              (z2z2KoszulSign g₁ g₂ * z2z2KoszulSign g₂ g₃) := by ring
      _ = _ := by rw [h13, one_mul]
    have hbc : (z2z2KoszulSign g₂ g₁ * (z2z2KoszulSign g₂ g₃ * z2z2KoszulSign g₂ g₁ * z2z2KoszulSign g₃ g₁)) =
        z2z2KoszulSign g₂ g₃ * z2z2KoszulSign g₃ g₁ := by
      calc _ = (z2z2KoszulSign g₂ g₁ * z2z2KoszulSign g₂ g₁) *
              (z2z2KoszulSign g₂ g₃ * z2z2KoszulSign g₃ g₁) := by ring
      _ = _ := by rw [h21, one_mul]
    have hca : (z2z2KoszulSign g₃ g₂ * (z2z2KoszulSign g₃ g₁ * z2z2KoszulSign g₃ g₂ * z2z2KoszulSign g₁ g₂)) =
        z2z2KoszulSign g₃ g₁ * z2z2KoszulSign g₁ g₂ := by
      calc _ = (z2z2KoszulSign g₃ g₂ * z2z2KoszulSign g₃ g₂) *
              (z2z2KoszulSign g₃ g₁ * z2z2KoszulSign g₁ g₂) := by ring
      _ = _ := by rw [h32, one_mul]
    rw [ha, hb, hc, hab, hbc, hca, ← hs13, ← hs12, ← hs23]
    simp only [mul_assoc]
    rw [mul_comm (z2z2KoszulSign g₂ g₃) (z2z2KoszulSign g₁ g₃),
      mul_comm (z2z2KoszulSign g₂ g₃) (z2z2KoszulSign g₁ g₂),
      mul_comm (z2z2KoszulSign g₁ g₃) (z2z2KoszulSign g₁ g₂)]
    try simp only [neg_one_zsmul, neg_smul, one_smul]
    abel

/-- **Cross-Module Unification of White Vacuum Singlets vs Color Triplets/Antitriplets across
    `Cl55SpinorCartanFock`, `ZornGaugeEmergence`, and `SuperGrassmannianFiveGradedColorSupersymmetrySynthesis`**. -/
theorem white_singlets_vs_color_triplets_unification
    (X_sl3 : Matrix (Fin 3) (Fin 3) ℝ) (hTr : Matrix.trace X_sl3 = 0)
    (X Y : InfoGeometry.Physics.NoncommutativeZornBdGDerivations.NCZorn ℝ)
    (a b : ℝ) (u v : Fin 3 → ℝ) :
    (ncZornVectorMatrixEquiv ℝ (X * Y) =
      ncZornVectorMatrixEquiv ℝ X * ncZornVectorMatrixEquiv ℝ Y) ∧
    (ncZornSplitOctonionEquiv ℝ (X * Y) =
      zornMul (ncZornSplitOctonionEquiv ℝ X) (ncZornSplitOctonionEquiv ℝ Y)) ∧
    (ncZornVectorMatrixEquiv ℝ InfoGeometry.Algebra.ZornGaugeEmergence.vacuumP1 =
      InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero 1 0) ∧
    (ncZornVectorMatrixEquiv ℝ (InfoGeometry.Algebra.ZornGaugeEmergence.embedTriplet u) =
      ⟨0, u, 0, 0⟩) ∧
    (ncZornSplitOctonionEquiv ℝ (InfoGeometry.Algebra.ZornGaugeEmergence.embedTriplet u) =
      embedPureQuarkZorn u) ∧
    (ncZornSplitOctonionEquiv ℝ (InfoGeometry.Algebra.ZornGaugeEmergence.embedAntitriplet v) =
      embedPureAntiQuarkZorn v) ∧
    InfoGeometry.Algebra.ZornGaugeEmergence.StabilizesVacuum
      (InfoGeometry.Algebra.ZornGaugeEmergence.sl3Derivation X_sl3 hTr) ∧
    (InfoGeometry.Algebra.ZornGaugeEmergence.sl3Derivation X_sl3 hTr).toFun
      (InfoGeometry.Algebra.ZornGaugeEmergence.embedTriplet u) =
      InfoGeometry.Algebra.ZornGaugeEmergence.embedTriplet (X_sl3.mulVec u) ∧
    (InfoGeometry.Algebra.ZornGaugeEmergence.sl3Derivation X_sl3 hTr).toFun
      (InfoGeometry.Algebra.ZornGaugeEmergence.embedAntitriplet v) =
      InfoGeometry.Algebra.ZornGaugeEmergence.embedAntitriplet (-(X_sl3.transpose.mulVec v)) ∧
    (InfoGeometry.Physics.Cl55SpinorCartanFock.colorGluonT3 *
        (InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj +
          InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj) = 0 ∧
     InfoGeometry.Physics.Cl55SpinorCartanFock.colorGluon3Y *
        (InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj +
          InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj) = 0) ∧
    (InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading
        (InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero a b) = 0 ∧
     InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading (⟨0, u, 0, 0⟩ :
        InfoGeometry.Algebra.ZornVectorMatrix ℝ) = ⟨0, ![-(2 * u 0), u 1, u 2], 0, 0⟩ ∧
     InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading (⟨0, 0, v, 0⟩ :
        InfoGeometry.Algebra.ZornVectorMatrix ℝ) = ⟨0, 0, ![2 * v 0, -v 1, -v 2], 0⟩) := by
  have hmul_zvm :
      ncZornVectorMatrixEquiv ℝ (X * Y) =
        ncZornVectorMatrixEquiv ℝ X * ncZornVectorMatrixEquiv ℝ Y := by
    have hmul_nc : X * Y = InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul X Y := rfl
    have hmul_v :
        ∀ P Q : InfoGeometry.Algebra.ZornVectorMatrix ℝ,
          P * Q = InfoGeometry.Algebra.ZornVectorMatrix.mul P Q := fun _ _ => rfl
    rw [hmul_nc, hmul_v]
    ext k
    · simp [ncZornVectorMatrixEquiv,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC,
        InfoGeometry.Algebra.ZornVectorMatrix.mul,
        InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
    · fin_cases k <;>
        (simp [ncZornVectorMatrixEquiv,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC,
          InfoGeometry.Algebra.ZornVectorMatrix.mul,
          InfoGeometry.Algebra.ZornVec3.cross]; ring)
    · fin_cases k <;>
        (simp [ncZornVectorMatrixEquiv,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
          InfoGeometry.Physics.NoncommutativeZornBdGDerivations.crossNC,
          InfoGeometry.Algebra.ZornVectorMatrix.mul,
          InfoGeometry.Algebra.ZornVec3.cross]; ring)
    · simp [ncZornVectorMatrixEquiv,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.ncZornMul,
        InfoGeometry.Physics.NoncommutativeZornBdGDerivations.dotNC,
        InfoGeometry.Algebra.ZornVectorMatrix.mul,
        InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]; ring
  have hmul_so :
      ncZornSplitOctonionEquiv ℝ (X * Y) =
        zornMul (ncZornSplitOctonionEquiv ℝ X) (ncZornSplitOctonionEquiv ℝ Y) := by
    dsimp [ncZornSplitOctonionEquiv]
    rw [hmul_zvm]
    exact (zornVectorMatrixSplitOctonionEquiv_mul_norm_and_kkt
      (ncZornVectorMatrixEquiv ℝ X) (ncZornVectorMatrixEquiv ℝ Y)).1
  have hrep := InfoGeometry.Algebra.ZornGaugeEmergence.sl3Derivation_representation
    X_sl3 X_sl3 hTr hTr X u v
  refine ⟨hmul_zvm, hmul_so, ?_, ?_, ?_, ?_, hrep.1, hrep.2.2.1, hrep.2.2.2.1,
    InfoGeometry.Physics.Cl55SpinorCartanFock.colorGluon_cartan_white_singlets_neutrality,
    ?_, ?_, ?_⟩
  · ext k <;> rfl
  · ext k <;> rfl
  · ext k <;> simp [ncZornSplitOctonionEquiv, ncZornVectorMatrixEquiv,
      zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornGaugeEmergence.embedTriplet,
      embedPureQuarkZorn]
    fin_cases k <;> rfl
  · ext k <;> simp [ncZornSplitOctonionEquiv, ncZornVectorMatrixEquiv,
      zornVectorMatrixSplitOctonionEquiv, InfoGeometry.Algebra.ZornGaugeEmergence.embedAntitriplet,
      embedPureAntiQuarkZorn]
    fin_cases k <;> rfl
  · ext k
    · rfl
    · simp [InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading,
        InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero]
      fin_cases k <;> rfl
    · simp [InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading,
        InfoGeometry.Algebra.ZornVectorMatrix.zornGradeZero]
      fin_cases k <;> rfl
    · rfl
  · ext k
    · rfl
    · simp [InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading]
    · simp [InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading]
      fin_cases k <;> rfl
    · rfl
  · ext k
    · rfl
    · simp [InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading]
      fin_cases k <;> rfl
    · simp [InfoGeometry.Algebra.ZornVectorMatrix.zornEulerFiveGrading]
    · rfl

end

/-- Closed `2 × 2` matrix non-commutativity witness over arbitrary nontrivial commutative ring `K`. -/
theorem superGrassmannian_mat2K_noncomm {K : Type*} [CommRing K] [Nontrivial K] :
    ∃ A B : Matrix (Fin 2) (Fin 2) K, A * B ≠ B * A := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Closed `3 × 3` matrix non-commutativity witness over arbitrary nontrivial commutative ring `K`. -/
theorem superGrassmannian_mat3K_noncomm {K : Type*} [CommRing K] [Nontrivial K] :
    ∃ A B : Matrix (Fin 3) (Fin 3) K, A * B ≠ B * A := by
  refine ⟨Matrix.single 0 1 1, Matrix.single 1 0 1, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h
  simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne] at h00

/-- Closed `3 × 3` real matrix non-commutativity witness. -/
theorem superGrassmannian_mat3R_noncomm :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.single 0 1 1, Matrix.single 1 0 1, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne] at h00

end InfoGeometry.Synthesis.SuperGrassmannianFiveGradedColorSupersymmetrySynthesis

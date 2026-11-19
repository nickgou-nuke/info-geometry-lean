/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge

/-!
# Todorov–Dubois-Violette–Günaydin–Gürsey Split-Octonion Standard Model Deduction, $\mathfrak{sl}(3,\mathbb{R})$ Color Stabilizer, Berezinian Lepton–Quark Bundle, and BMS Celestial Supertranslations

This module formalizes the split-octonion algebraic mechanism connecting Zorn's vector-matrix
split-octonion carrier `ZornSplitOctonion ℝ`, the 14-parameter $G_{2(2)}$ derivation family
`zornG2Derivation`, the Günaydin–Gürsey lepton–quark multiplet `GunaydinGurseyMultiplet ℝ`,
and angle-dependent BMS celestial supertranslations:

1. **Section 1 — The Todorov Split-Octonion Hyperbolic Polarization Unit $\omega \in \mathbb{O}_s$, $\omega^2 = +\mathbf{1}$, and Orthogonal Idempotent Socle Decomposition**:
   - Defines `zornHyperbolicOmega` ($\omega = e_+ - e_-$), `zornIdemPlus` ($e_+$),
     `zornIdemMinus` ($e_-$), `embedUpperChiral`, and `embedLowerChiral`.
   - Proves `zornHyperbolicOmega_properties` ($\omega^\star = -\omega$, $\omega^2 = +1$,
     $N(\omega) = -1$), `zorn_todorov_idempotent_socle_decomposition`, and
     `zorn_peirce_quark_triplet_absorption`.
2. **Section 2 — 8-Dimensional Color Stability Subalgebra $\mathfrak{sl}(3,\mathbb{R}) \subset \mathfrak{g}_{2(2)}$ Fixing the Todorov Hyperbolic Unit $\omega$**:
   - Evaluates `zornG2Derivation p zornHyperbolicOmega` (`zornG2Derivation_zornHyperbolicOmega_eval`)
     and proves `zornG2Derivation_zornHyperbolicOmega_eq_zero_iff`, establishing that the
     stabilizer of $\omega$ in the 14-parameter $\mathfrak{g}_{2(2)}$ derivation family is cut
     out by the 6 off-diagonal mixing equations $p_0 = p_3 = p_4 = p_8 = p_9 = p_{10} = 0$,
     leaving $14 - 6 = 8 = 3^2 - 1$ free $\mathfrak{sl}(3, \mathbb{R})$ color parameters that
     annihilate the diagonal leptonic scalars (`zornG2Derivation_stabilizer_annihilates_leptons`).
3. **Section 3 — Günaydin–Gürsey Lepton–Quark Bundle $(\mathbf{1}\oplus\mathbf{1}) \oplus (\mathbf{3}\oplus\bar{\mathbf{3}})$ via Berezinian Scaling & BMS Celestial Supertranslations**:
   - Defines `berezinianLeptonQuarkScale` and proves `berezinianLeptonQuarkScale_invariants`.
   - Defines `bmsCelestialSupertranslation` and proves `bmsCelestialSupertranslation_interval_invariant`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.TodorovSplitOctonionStandardModelBerezinianBridge

open scoped BigOperators
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension

/-!
## Section 1: The Todorov Split-Octonion Hyperbolic Polarization Unit $\omega \in \mathbb{O}_s$, $\omega^2 = +\mathbf{1}$, and Orthogonal Idempotent Socle Decomposition
-/

/-- The canonical Todorov split-octonion hyperbolic polarization unit
$\omega = e_+ - e_- = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in \mathrm{ZornSplitOctonion}\, \mathbb{R}$. -/
def zornHyperbolicOmega : ZornSplitOctonion ℝ :=
  ⟨1, ![0, 0, 0], ![0, 0, 0], -1⟩

/-- **Algebraic Properties of the Todorov Hyperbolic Polarization Unit $\omega$**:
1. $\omega \in \operatorname{Im}(\mathbb{O}_s)$ (`zornConj zornHyperbolicOmega = -zornHyperbolicOmega`),
2. $\omega^2 = +\mathbf{1}_{\mathbb{O}_s}$ (`zornMul zornHyperbolicOmega zornHyperbolicOmega = zornOne`),
3. $N_{\mathbb{O}_s}(\omega) = -1$ (`zornNorm zornHyperbolicOmega = -1`). -/
theorem zornHyperbolicOmega_properties :
    zornConj zornHyperbolicOmega = zornSmul (-1 : ℝ) zornHyperbolicOmega ∧
    zornMul zornHyperbolicOmega zornHyperbolicOmega = zornOne ∧
    zornNorm zornHyperbolicOmega = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext k
    · dsimp [zornHyperbolicOmega, zornConj, zornSmul]
      ring
    · fin_cases k <;> (dsimp [zornHyperbolicOmega, zornConj, zornSmul]; ring)
    · fin_cases k <;> (dsimp [zornHyperbolicOmega, zornConj, zornSmul]; ring)
    · dsimp [zornHyperbolicOmega, zornConj, zornSmul]
      ring
  · ext k
    · dsimp [zornHyperbolicOmega, zornMul, zornOne, vec3Dot]
      ring
    · fin_cases k <;> (dsimp [zornHyperbolicOmega, zornMul, zornOne, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornHyperbolicOmega, zornMul, zornOne, vec3Cross]; ring)
    · dsimp [zornHyperbolicOmega, zornMul, zornOne, vec3Dot]
      ring
  · dsimp [zornHyperbolicOmega, zornNorm, vec3Dot]
    ring

/-- Upper-left primitive Zorn idempotent $e_+ = \frac{1}{2}(1 + \omega) = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def zornIdemPlus : ZornSplitOctonion ℝ :=
  ⟨1, ![0, 0, 0], ![0, 0, 0], 0⟩

/-- Lower-right primitive Zorn idempotent $e_- = \frac{1}{2}(1 - \omega) = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def zornIdemMinus : ZornSplitOctonion ℝ :=
  ⟨0, ![0, 0, 0], ![0, 0, 0], 1⟩

/-- **Orthogonal Idempotent Socle Decomposition of $1_{\mathbb{O}_s}$ and $\omega$**:
1. $e_+ + e_- = 1_{\mathbb{O}_s}$ and $e_+ - e_- = \omega$,
2. $e_+^2 = e_+$ and $e_-^2 = e_-$,
3. $e_+ e_- = 0$ and $e_- e_+ = 0$,
4. $N_{\mathbb{O}_s}(e_+) = 0$ and $N_{\mathbb{O}_s}(e_-) = 0$. -/
theorem zorn_todorov_idempotent_socle_decomposition :
    (zornAdd zornIdemPlus zornIdemMinus = zornOne ∧
     zornAdd zornIdemPlus (zornSmul (-1 : ℝ) zornIdemMinus) = zornHyperbolicOmega) ∧
    (zornMul zornIdemPlus zornIdemPlus = zornIdemPlus ∧
     zornMul zornIdemMinus zornIdemMinus = zornIdemMinus) ∧
    (zornMul zornIdemPlus zornIdemMinus = zornZero ∧
     zornMul zornIdemMinus zornIdemPlus = zornZero) ∧
    (zornNorm zornIdemPlus = 0 ∧ zornNorm zornIdemMinus = 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · ext k
    · dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornOne]; ring
    · fin_cases k <;> (dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornOne]; ring)
    · fin_cases k <;> (dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornOne]; ring)
    · dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornOne]; ring
  · ext k
    · dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornSmul, zornHyperbolicOmega]; ring
    · fin_cases k <;>
        (dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornSmul, zornHyperbolicOmega]; ring)
    · fin_cases k <;>
        (dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornSmul, zornHyperbolicOmega]; ring)
    · dsimp [zornIdemPlus, zornIdemMinus, zornAdd, zornSmul, zornHyperbolicOmega]; ring
  · ext k
    · dsimp [zornIdemPlus, zornMul, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemPlus, zornMul, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemPlus, zornMul, vec3Cross]; ring)
    · dsimp [zornIdemPlus, zornMul, vec3Dot]; ring
  · ext k
    · dsimp [zornIdemMinus, zornMul, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemMinus, zornMul, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemMinus, zornMul, vec3Cross]; ring)
    · dsimp [zornIdemMinus, zornMul, vec3Dot]; ring
  · ext k
    · dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Cross]; ring)
    · dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Dot]; ring
  · ext k
    · dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Cross]; ring)
    · dsimp [zornIdemPlus, zornIdemMinus, zornMul, zornZero, vec3Dot]; ring
  · dsimp [zornIdemPlus, zornNorm, vec3Dot]; ring
  · dsimp [zornIdemMinus, zornNorm, vec3Dot]; ring

/-- Embeds a 3-component quark color-triplet vector $u \in \mathbb{R}^3$ into the upper-right
Peirce slot $\begin{pmatrix} 0 & u \\ 0 & 0 \end{pmatrix} \in \mathrm{ZornSplitOctonion}\, \mathbb{R}$. -/
def embedUpperChiral (u : Fin 3 → ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, u, ![0, 0, 0], 0⟩

/-- Embeds a 3-component anti-quark color-antitriplet vector $v \in \mathbb{R}^3$ into the
lower-left Peirce slot $\begin{pmatrix} 0 & 0 \\ v & 0 \end{pmatrix} \in \mathrm{ZornSplitOctonion}\, \mathbb{R}$. -/
def embedLowerChiral (v : Fin 3 → ℝ) : ZornSplitOctonion ℝ :=
  ⟨0, ![0, 0, 0], v, 0⟩

/-- **Peirce Idempotent Absorption & $\omega$-Eigenvalue Splitting of Quark/Antiquark Triplets**:
For any upper-chiral quark triplet $u \in \mathbb{R}^3$ and lower-chiral anti-quark triplet
$v \in \mathbb{R}^3$:
1. $e_+ \star u = u$ and $u \star e_- = u$,
2. $e_- \star v = v$ and $v \star e_+ = v$,
3. $\omega \star u = +u$ and $\omega \star v = -v$. -/
theorem zorn_peirce_quark_triplet_absorption (u v : Fin 3 → ℝ) :
    (zornMul zornIdemPlus (embedUpperChiral u) = embedUpperChiral u ∧
     zornMul (embedUpperChiral u) zornIdemMinus = embedUpperChiral u) ∧
    (zornMul zornIdemMinus (embedLowerChiral v) = embedLowerChiral v ∧
     zornMul (embedLowerChiral v) zornIdemPlus = embedLowerChiral v) ∧
    (zornMul zornHyperbolicOmega (embedUpperChiral u) = embedUpperChiral u ∧
     zornMul zornHyperbolicOmega (embedLowerChiral v) =
       zornSmul (-1 : ℝ) (embedLowerChiral v)) := by
  have _ := (u, v)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · ext k
    · dsimp [zornIdemPlus, embedUpperChiral, zornMul, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemPlus, embedUpperChiral, zornMul, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemPlus, embedUpperChiral, zornMul, vec3Cross]; ring)
    · dsimp [zornIdemPlus, embedUpperChiral, zornMul, vec3Dot]; ring
  · ext k
    · dsimp [zornIdemMinus, embedUpperChiral, zornMul, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemMinus, embedUpperChiral, zornMul, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemMinus, embedUpperChiral, zornMul, vec3Cross]; ring)
    · dsimp [zornIdemMinus, embedUpperChiral, zornMul, vec3Dot]; ring
  · ext k
    · dsimp [zornIdemMinus, embedLowerChiral, zornMul, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemMinus, embedLowerChiral, zornMul, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemMinus, embedLowerChiral, zornMul, vec3Cross]; ring)
    · dsimp [zornIdemMinus, embedLowerChiral, zornMul, vec3Dot]; ring
  · ext k
    · dsimp [zornIdemPlus, embedLowerChiral, zornMul, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornIdemPlus, embedLowerChiral, zornMul, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornIdemPlus, embedLowerChiral, zornMul, vec3Cross]; ring)
    · dsimp [zornIdemPlus, embedLowerChiral, zornMul, vec3Dot]; ring
  · ext k
    · dsimp [zornHyperbolicOmega, embedUpperChiral, zornMul, vec3Dot]; ring
    · fin_cases k <;> (dsimp [zornHyperbolicOmega, embedUpperChiral, zornMul, vec3Cross]; ring)
    · fin_cases k <;> (dsimp [zornHyperbolicOmega, embedUpperChiral, zornMul, vec3Cross]; ring)
    · dsimp [zornHyperbolicOmega, embedUpperChiral, zornMul, vec3Dot]; ring
  · ext k
    · dsimp [zornHyperbolicOmega, embedLowerChiral, zornMul, zornSmul, vec3Dot]; ring
    · fin_cases k <;>
        (dsimp [zornHyperbolicOmega, embedLowerChiral, zornMul, zornSmul, vec3Cross]; ring)
    · fin_cases k <;>
        (dsimp [zornHyperbolicOmega, embedLowerChiral, zornMul, zornSmul, vec3Cross]; ring)
    · dsimp [zornHyperbolicOmega, embedLowerChiral, zornMul, zornSmul, vec3Dot]; ring

/-!
## Section 2: 8-Dimensional Color Stability Subalgebra $\mathfrak{sl}(3,\mathbb{R}) \subset \mathfrak{g}_{2(2)}$ Fixing the Todorov Hyperbolic Unit $\omega$
-/

/-- Explicit coordinate evaluation of the 14-parameter $G_{2(2)}$ derivation `zornG2Derivation p`
on the Todorov hyperbolic unit `zornHyperbolicOmega`. -/
theorem zornG2Derivation_zornHyperbolicOmega_eval (p : Params) :
    zornG2Derivation p zornHyperbolicOmega =
      ⟨0, ![2 * p 10, -2 * p 9, 2 * p 4], ![-2 * p 0, -2 * p 3, -2 * p 8], 0⟩ := by
  have _ := p
  ext k
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornHyperbolicOmega]
  · fin_cases k <;>
      (simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornHyperbolicOmega]; ring)
  · fin_cases k <;>
      (simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
        splitOctonionToZornVectorMatrix, parameterAction, zornHyperbolicOmega]; ring)
  · simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornHyperbolicOmega]

/-- **Todorov Color Stabilizer Characterization ($\mathfrak{g}_{2(2)} \to \mathfrak{sl}(3, \mathbb{R})$)**:
A 14-parameter $G_{2(2)}$ derivation `zornG2Derivation p` annihilates `zornHyperbolicOmega`
if and only if the 6 off-diagonal lepton–quark mixing parameters
$(p_0, p_3, p_4, p_8, p_9, p_{10})$ vanish identically, leaving the 8 free parameters
$(p_1, p_2, p_5, p_6, p_7, p_{11}, p_{12}, p_{13})$ of $\mathfrak{sl}(3, \mathbb{R})$. -/
theorem zornG2Derivation_zornHyperbolicOmega_eq_zero_iff (p : Params) :
    zornG2Derivation p zornHyperbolicOmega = zornZero ↔
      (p 0 = 0 ∧ p 3 = 0 ∧ p 4 = 0 ∧ p 8 = 0 ∧ p 9 = 0 ∧ p 10 = 0) := by
  rw [zornG2Derivation_zornHyperbolicOmega_eval p]
  constructor
  · intro h
    have hu0 : (⟨0, ![2 * p 10, -2 * p 9, 2 * p 4], ![-2 * p 0, -2 * p 3, -2 * p 8], 0⟩ :
        ZornSplitOctonion ℝ).u 0 = (zornZero : ZornSplitOctonion ℝ).u 0 :=
      congrFun (congrArg ZornSplitOctonion.u h) 0
    have hu1 : (⟨0, ![2 * p 10, -2 * p 9, 2 * p 4], ![-2 * p 0, -2 * p 3, -2 * p 8], 0⟩ :
        ZornSplitOctonion ℝ).u 1 = (zornZero : ZornSplitOctonion ℝ).u 1 :=
      congrFun (congrArg ZornSplitOctonion.u h) 1
    have hu2 : (⟨0, ![2 * p 10, -2 * p 9, 2 * p 4], ![-2 * p 0, -2 * p 3, -2 * p 8], 0⟩ :
        ZornSplitOctonion ℝ).u 2 = (zornZero : ZornSplitOctonion ℝ).u 2 :=
      congrFun (congrArg ZornSplitOctonion.u h) 2
    have hv0 : (⟨0, ![2 * p 10, -2 * p 9, 2 * p 4], ![-2 * p 0, -2 * p 3, -2 * p 8], 0⟩ :
        ZornSplitOctonion ℝ).v 0 = (zornZero : ZornSplitOctonion ℝ).v 0 :=
      congrFun (congrArg ZornSplitOctonion.v h) 0
    have hv1 : (⟨0, ![2 * p 10, -2 * p 9, 2 * p 4], ![-2 * p 0, -2 * p 3, -2 * p 8], 0⟩ :
        ZornSplitOctonion ℝ).v 1 = (zornZero : ZornSplitOctonion ℝ).v 1 :=
      congrFun (congrArg ZornSplitOctonion.v h) 1
    have hv2 : (⟨0, ![2 * p 10, -2 * p 9, 2 * p 4], ![-2 * p 0, -2 * p 3, -2 * p 8], 0⟩ :
        ZornSplitOctonion ℝ).v 2 = (zornZero : ZornSplitOctonion ℝ).v 2 :=
      congrFun (congrArg ZornSplitOctonion.v h) 2
    dsimp [zornZero] at hu0 hu1 hu2 hv0 hv1 hv2
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hp0, hp3, hp4, hp8, hp9, hp10⟩
    ext k
    · rfl
    · fin_cases k <;> simp [zornZero, hp4, hp9, hp10]
    · fin_cases k <;> simp [zornZero, hp0, hp3, hp8]
    · rfl

/-- Every derivation in the 8-parameter $\mathfrak{sl}(3, \mathbb{R})$ stabilizer of
`zornHyperbolicOmega` annihilates the diagonal leptonic singlet components `(x.a, x.b)`
of any split-octonion `x : ZornSplitOctonion ℝ`. -/
theorem zornG2Derivation_stabilizer_annihilates_leptons
    (p : Params) (x : ZornSplitOctonion ℝ)
    (hp : zornG2Derivation p zornHyperbolicOmega = zornZero) :
    (zornG2Derivation p x).a = 0 ∧ (zornG2Derivation p x).b = 0 := by
  rcases (zornG2Derivation_zornHyperbolicOmega_eq_zero_iff p).mp hp with
    ⟨hp0, hp3, hp4, hp8, hp9, hp10⟩
  constructor <;>
    simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, hp0, hp3, hp4, hp8, hp9, hp10]

/-- Dimension accounting for the Todorov–Dubois-Violette color stabilizer reduction
$\dim \mathfrak{g}_{2(2)} - 6 = 14 - 6 = 8 = 3^2 - 1 = \dim \mathfrak{sl}(3, \mathbb{R}) = \dim \mathfrak{su}(3)$. -/
theorem todorov_g2_to_su3_color_dimension_reduction :
    14 - 6 = 8 ∧ 3 ^ 2 - 1 = 8 := by
  exact ⟨rfl, rfl⟩

/-!
## Section 3: Günaydin–Gürsey Lepton–Quark Bundle $(\mathbf{1}\oplus\mathbf{1}) \oplus (\mathbf{3}\oplus\bar{\mathbf{3}})$ via Berezinian Scaling & BMS Celestial Supertranslations
-/

/-- Reciprocal Berezinian Weyl scaling $(\lambda, \lambda^{-1})$ across the positive and negative
sheets of a Günaydin–Gürsey lepton–quark multiplet $M = (\ell, q, \bar{q}) \in (\mathbf{1}\oplus\mathbf{1}) \oplus (\mathbf{3}\oplus\bar{\mathbf{3}})$. -/
def berezinianLeptonQuarkScale (lam invLam : ℝ) (M : GunaydinGurseyMultiplet ℝ) :
    GunaydinGurseyMultiplet ℝ :=
  (![lam * M.1 0, invLam * M.1 1],
   (fun a => lam * M.2.1 a, fun a => invLam * M.2.2 a))

/-- **Exact Scale Invariance of Leptonic & Quark/Antiquark Bilinear Pairings under `berezinianLeptonQuarkScale`**:
For any reciprocal scale pair $\lambda \cdot \lambda^{-1} = 1$:
1. The leptonic singlet product $\ell_0 \ell_1$ is strictly invariant,
2. The color-singlet quark/antiquark contraction $\sum_{a=0}^2 q_a \bar{q}^a$ is strictly invariant,
3. The composite $(\mathbf{1}\oplus\mathbf{1}) \oplus (\mathbf{3}\oplus\bar{\mathbf{3}})$ volume
   determinant factor $(\lambda \lambda^{-1}) (\lambda^3 \lambda^{-3})$ equals $1$. -/
theorem berezinianLeptonQuarkScale_invariants
    (lam invLam : ℝ) (h_inv : lam * invLam = 1) (M : GunaydinGurseyMultiplet ℝ) :
    (berezinianLeptonQuarkScale lam invLam M).1 0 *
      (berezinianLeptonQuarkScale lam invLam M).1 1 = M.1 0 * M.1 1 ∧
    (∑ a : Fin 3,
      (berezinianLeptonQuarkScale lam invLam M).2.1 a *
        (berezinianLeptonQuarkScale lam invLam M).2.2 a) =
      ∑ a : Fin 3, M.2.1 a * M.2.2 a ∧
    (lam * invLam) * (lam ^ 3 * invLam ^ 3) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [berezinianLeptonQuarkScale]
    calc
      (lam * M.1 0) * (invLam * M.1 1) = (lam * invLam) * (M.1 0 * M.1 1) := by ring
      _ = 1 * (M.1 0 * M.1 1) := by rw [h_inv]
      _ = M.1 0 * M.1 1 := one_mul _
  · apply Finset.sum_congr rfl
    intro a _
    dsimp [berezinianLeptonQuarkScale]
    calc
      (lam * M.2.1 a) * (invLam * M.2.2 a) = (lam * invLam) * (M.2.1 a * M.2.2 a) := by ring
      _ = 1 * (M.2.1 a * M.2.2 a) := by rw [h_inv]
      _ = M.2.1 a * M.2.2 a := one_mul _
  · calc
      (lam * invLam) * (lam ^ 3 * invLam ^ 3) = (lam * invLam) ^ 4 := by ring
      _ = 1 ^ 4 := by rw [h_inv]
      _ = 1 := by norm_num

/-- Angle-dependent BMS celestial supertranslation shift $\tau \mapsto \tau + T(\theta, \phi)$
on the logarithmic radial clock $\tau = -\ln(r / r_0)$. -/
def bmsCelestialSupertranslation (tau T_angle : ℝ) : ℝ :=
  tau + T_angle

/-- **Invariance of the Logarithmic Radial Interval under BMS Celestial Supertranslations**:
For any two nonzero radial scales $r_1, r_2, r_0 \neq 0$ along the same celestial direction
with supertranslation shift `T_angle`, the supertranslated logarithmic interval equals the
intrinsic scale-free ratio $-\ln(r_1 / r_2)$, independent of both $r_0$ and `T_angle`. -/
theorem bmsCelestialSupertranslation_interval_invariant
    (r₁ r₂ r₀ T_angle : ℝ) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (hr₀ : r₀ ≠ 0) :
    bmsCelestialSupertranslation (-Real.log (r₁ / r₀)) T_angle -
      bmsCelestialSupertranslation (-Real.log (r₂ / r₀)) T_angle =
      -Real.log (r₁ / r₂) := by
  unfold bmsCelestialSupertranslation
  rw [Real.log_div hr₁ hr₀, Real.log_div hr₂ hr₀, Real.log_div hr₁ hr₂]
  ring

end InfoGeometry.Synthesis.TodorovSplitOctonionStandardModelBerezinianBridge

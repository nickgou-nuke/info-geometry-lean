/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset
import InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Owner Alignment, Three-Regime `Solve et Coagula` Matrix Triad, & Apollonian Strip

Isolated canonical leaf synthesis uniting the Peirce-spine and root `IndefiniteReciprocalTotalityPoset`
owners with the complete three-regime matrix triad and the Klein-bottle KMS / centered Riemann strip /
Apollonian bisector bridge:

1. **Owner Operator & Poset Alignment** (`solveEtCoagula_owner_operator_alignment`,
   `archetypeToCoagulaEquiv`, `solveEtCoagula_poset_isomorphism`):
   Identifies all 14 operators of `ReciprocalTotalityAporiaPoset` and `IndefiniteReciprocalTotalityPoset`
   over any associative unital ring `[Ring E]` and constructs an explicit covering-edge and transitive
   causal-order isomorphism `ArchetypePosetNode ≃ CoagulaNode`.
2. **Elliptic `M₂(ℚ)` Witness & Three-Regime Matrix Triad** (`cutP0Q`, `totalityOmegaEll`,
   `concrete_mat2Q_elliptic_positive_witness`, `solveEtCoagula_three_regime_matrix_triad`):
   Combines the elliptic positive-aporia `M₂(ℚ)` realization (`𝒜₀ = !![1/4, 0; 0, 0]`,
   `M = !![1/4, 0; 0, 1/4]`, `Σ₀ = 0`, `B² = 1`), the parabolic one-way null-horizon `M₂(ℤ)` realization
   plus general `[CommRing R] [Nontrivial R]` Krein-self-adjoint Jordan non-diagonalizability, and the
   hyperbolic Krein `M₂(ℤ)` / positive Mannheim `V₀` realization.
3. **Klein-Bottle KMS Glide, Centered Strip `V₄`, & Apollonian Bisector**
   (`kleinBottleKMSGlide`, `stripT`, `stripP`, `stripPT`, `apollonianCayley`,
   `kleinBottle_kms_centeredStrip_apollonian_bridge`):
   Formalizes the fixed-point-free orientation-reversing KMS glide `(u, τ) ↦ (-u, τ + β/2)`,
   the centered strip Klein four-group `V₄ = {1, P, T, PT}`, the Apollonian radical bisector
   `|w - 1/2|² - |w + 1/2|² = -2 Re w`, Cayley pole inversion, and Li's single-pole unit-circle
   nonnegativity `(1 - z).re + (1 - star z).re = (1 - z.re)^2 + z.im^2 ≥ 0`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityThreeRegimeSynthesis

section OwnerAlignment

open InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset
open InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset

/-- Unconditional 14-operator definitional alignment uniting `ReciprocalTotalityAporiaPoset` and
`IndefiniteReciprocalTotalityPoset` over any non-commutative unital ring `[Ring E]`. -/
theorem solveEtCoagula_owner_operator_alignment {E : Type*} [Ring E] (P Ω : E) :
    Q P = shadowQ P ∧
    Gamma P = polarityGamma P ∧
    T P Ω = consciousThesis P Ω ∧
    X P Ω = outwardProj P Ω ∧
    Y P Ω = inwardIntrusion P Ω ∧
    G P Ω = autonomousGround P Ω ∧
    F P Ω = integrativeBridge P Ω ∧
    M P Ω = substantiveGravity P Ω ∧
    K P Ω = directionalTension P Ω ∧
    aporia P Ω = socraticAporia P Ω ∧
    groundAporia P Ω = shadowAporia P Ω ∧
    Sigma0 P Ω = dogmaticTruncation P Ω ∧
    B P Ω = doubledBridge P Ω ∧
    JOmega Ω = reciprocalTotality Ω := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;>
  · simp only [Sigma0, dogmaticTruncation, B, doubledBridge, JOmega, reciprocalTotality,
      T, consciousThesis, G, autonomousGround, Q, shadowQ, F, integrativeBridge,
      X, outwardProj, Y, inwardIntrusion, two_nsmul, two_mul]

/-- Explicit 16-node bijection `ArchetypePosetNode ≃ CoagulaNode`. -/
def archetypeToCoagulaEquiv : ArchetypePosetNode ≃ CoagulaNode where
  toFun
    | .N0_Omega => .N0_Omega
    | .N1a_P => .N1a_ThesisP
    | .N1b_Q => .N1b_ShadowQ
    | .N1c_Gamma => .N1c_PolarityGamma
    | .N2a_T => .N2a_ConsistencyT
    | .N2b_X => .N2b_OutwardX
    | .N2c_Y => .N2c_InwardY
    | .N2d_G => .N2d_AutonomousG
    | .N3a_Holonomy => .N3a_Holonomies
    | .N3b_F => .N3b_BridgeF
    | .N3c_M => .N3c_GravityM
    | .N3d_K => .N3d_TensionK
    | .N4a_Aporia => .N4a_AporiaA0
    | .N4b_Sigma0 => .N4b_TruncationSigma0
    | .N5_MetaTower => .N5_MetaTower
    | .N6_JOmega => .N6_ReciprocalJOmega
  invFun
    | .N0_Omega => .N0_Omega
    | .N1a_ThesisP => .N1a_P
    | .N1b_ShadowQ => .N1b_Q
    | .N1c_PolarityGamma => .N1c_Gamma
    | .N2a_ConsistencyT => .N2a_T
    | .N2b_OutwardX => .N2b_X
    | .N2c_InwardY => .N2c_Y
    | .N2d_AutonomousG => .N2d_G
    | .N3a_Holonomies => .N3a_Holonomy
    | .N3b_BridgeF => .N3b_F
    | .N3c_GravityM => .N3c_M
    | .N3d_TensionK => .N3d_K
    | .N4a_AporiaA0 => .N4a_Aporia
    | .N4b_TruncationSigma0 => .N4b_Sigma0
    | .N5_MetaTower => .N5_MetaTower
    | .N6_ReciprocalJOmega => .N6_JOmega
  left_inv u := by cases u <;> rfl
  right_inv v := by cases v <;> rfl

private lemma transGen_iff_of_equiv {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (e : α ≃ β) (he : ∀ a b : α, r a b ↔ s (e a) (e b))
    (u v : α) :
    Relation.TransGen r u v ↔ Relation.TransGen s (e u) (e v) := by
  constructor
  · intro h
    induction h with
    | single huv => exact Relation.TransGen.single ((he _ _).mp huv)
    | tail _ hbc ih => exact ih.tail ((he _ _).mp hbc)
  · intro h
    have hback : ∀ x y : β, Relation.TransGen s x y →
        Relation.TransGen r (e.symm x) (e.symm y) := by
      intro x y hxy
      induction hxy with
      | single h0 =>
          refine Relation.TransGen.single ((he (e.symm _) (e.symm _)).mpr ?_)
          simpa only [Equiv.apply_symm_apply] using h0
      | tail _ hbc ih =>
          refine ih.tail ((he (e.symm _) (e.symm _)).mpr ?_)
          simpa only [Equiv.apply_symm_apply] using hbc
    simpa only [Equiv.symm_apply_apply] using hback (e u) (e v) h

/-- Exact covering-edge and transitive causal-poset order isomorphism uniting
`ArchetypePosetNode` (`ReciprocalTotalityAporiaPoset`) and `CoagulaNode`
(`IndefiniteReciprocalTotalityPoset`). -/
theorem solveEtCoagula_poset_isomorphism (u v : ArchetypePosetNode) :
    (coverRel u v = true ↔
      CoagulaCovers (archetypeToCoagulaEquiv u) (archetypeToCoagulaEquiv v)) ∧
    (causalPrec u v ↔
      Relation.TransGen CoagulaCovers
        (archetypeToCoagulaEquiv u) (archetypeToCoagulaEquiv v)) := by
  have hedgeC : ∀ a b : ArchetypePosetNode,
      coverRel a b = true ↔
        CoagulaCovers (archetypeToCoagulaEquiv a) (archetypeToCoagulaEquiv b) := by
    intro a b
    constructor
    · intro h
      cases a <;> cases b <;>
        first
        | exact absurd h (by decide)
        | constructor
    · intro h
      have hback : ∀ x y : CoagulaNode, CoagulaCovers x y →
          coverRel (archetypeToCoagulaEquiv.symm x) (archetypeToCoagulaEquiv.symm y) = true := by
        intro x y hxy
        cases hxy <;> decide
      simpa only [Equiv.symm_apply_apply] using
        hback (archetypeToCoagulaEquiv a) (archetypeToCoagulaEquiv b) h
  exact ⟨hedgeC u v, transGen_iff_of_equiv archetypeToCoagulaEquiv hedgeC u v⟩

end OwnerAlignment

section ThreeRegime

open InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset

/-- Rational projection cut `P₀ ∈ M₂(ℚ)`. -/
def cutP0Q : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]

/-- Elliptic / positive-superposition totality idempotent `Ω_ell ∈ M₂(ℚ)`. -/
def totalityOmegaEll : Matrix (Fin 2) (Fin 2) ℚ := !![(1 / 2 : ℚ), 1 / 2; 1 / 2, 1 / 2]

/-- Concrete `M₂(ℚ)` realization of the elliptic positive-aporia regime (`𝒜₀ = !![1/4, 0; 0, 0]`,
`M = !![1/4, 0; 0, 1/4]`, `Σ₀ = 0`, `B² = 1`, `J_{Ω_ell} = !![0, 1; 1, 0]`). -/
theorem concrete_mat2Q_elliptic_positive_witness :
    cutP0Q * cutP0Q = cutP0Q ∧
    totalityOmegaEll * totalityOmegaEll = totalityOmegaEll ∧
    _root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm cutP0Q totalityOmegaEll ≠ 0 ∧
    aporia cutP0Q totalityOmegaEll = !![(1 / 4 : ℚ), 0; 0, 0] ∧
    aporia cutP0Q totalityOmegaEll ≠ 0 ∧
    M cutP0Q totalityOmegaEll = !![(1 / 4 : ℚ), 0; 0, 1 / 4] ∧
    Sigma0 cutP0Q totalityOmegaEll = 0 ∧
    B cutP0Q totalityOmegaEll * B cutP0Q totalityOmegaEll = 1 ∧
    JOmega totalityOmegaEll = !![0, 1; 1, 0] ∧
    JOmega totalityOmegaEll * JOmega totalityOmegaEll = 1 ∧
    JOmega totalityOmegaEll ≠ Gamma cutP0Q := by
  have hP2 : cutP0Q * cutP0Q = cutP0Q := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [cutP0Q, Matrix.mul_apply, Fin.sum_univ_two]
  have hΩ2 : totalityOmegaEll * totalityOmegaEll = totalityOmegaEll := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [totalityOmegaEll, Matrix.mul_apply, Fin.sum_univ_two]
  have hcomm : _root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm cutP0Q totalityOmegaEll ≠ 0 := by
    intro h0
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) h0
    norm_num [_root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm, cutP0Q, totalityOmegaEll,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hT : T cutP0Q totalityOmegaEll = !![(1 / 2 : ℚ), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [T, cutP0Q, totalityOmegaEll, Matrix.mul_apply, Fin.sum_univ_two]
  have hG : G cutP0Q totalityOmegaEll = !![0, 0; 0, (1 / 2 : ℚ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [G, Q, cutP0Q, totalityOmegaEll, Matrix.mul_apply, Fin.sum_univ_two]
  have hX : X cutP0Q totalityOmegaEll = !![0, 0; (1 / 2 : ℚ), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [X, Q, cutP0Q, totalityOmegaEll, Matrix.mul_apply, Fin.sum_univ_two]
  have hY : Y cutP0Q totalityOmegaEll = !![0, (1 / 2 : ℚ); 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Y, Q, cutP0Q, totalityOmegaEll, Matrix.mul_apply, Fin.sum_univ_two]
  have hApEq : aporia cutP0Q totalityOmegaEll = !![(1 / 4 : ℚ), 0; 0, 0] := by
    rw [aporia, hT]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hApNe : aporia cutP0Q totalityOmegaEll ≠ 0 := by
    intro h0
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h0
    norm_num [hApEq] at h00
  have hM : M cutP0Q totalityOmegaEll = !![(1 / 4 : ℚ), 0; 0, 1 / 4] := by
    rw [M, hX, hY]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hSig : Sigma0 cutP0Q totalityOmegaEll = 0 := by
    rw [Sigma0, hT, hG]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Q, cutP0Q]
  have hB : B cutP0Q totalityOmegaEll = !![0, (1 : ℚ); 1, 0] := by
    rw [B, F, hX, hY]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hBsq : B cutP0Q totalityOmegaEll * B cutP0Q totalityOmegaEll = 1 := by
    rw [hB]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hJ : JOmega totalityOmegaEll = !![0, (1 : ℚ); 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [JOmega, totalityOmegaEll]
  have hJsq : JOmega totalityOmegaEll * JOmega totalityOmegaEll = 1 := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hJne : JOmega totalityOmegaEll ≠ Gamma cutP0Q := by
    intro h0
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h0
    norm_num [hJ, Gamma, Q, cutP0Q] at h00
  exact ⟨hP2, hΩ2, hcomm, hApEq, hApNe, hM, hSig, hBsq, hJ, hJsq, hJne⟩

/-- Complete three-regime matrix triad uniting:
1. Elliptic / Positive `M₂(ℚ)` (`𝒜₀ = !![1/4, 0; 0, 0]`, `M = !![1/4, 0; 0, 1/4]`, `Σ₀ = 0`, `B² = 1`),
2. Parabolic / Jordan `M₂(ℤ)` null-horizon (`𝒜₀ = 0`, `B² = 0`, `B ≠ 0`, `[P₀, J_{Ω_par}] ≠ 0`) plus
   general `[CommRing R] [Nontrivial R]` Krein-self-adjoint Jordan non-diagonalizability, and
3. Hyperbolic / Krein `M₂(ℤ)` (`det η₀ = -2`, `1 - Σ₀² = -8 I₂`, positive Mannheim `V₀ = !![6, 4; 4, 3]`). -/
theorem solveEtCoagula_three_regime_matrix_triad
    {R : Type*} [CommRing R] [Nontrivial R] (μ : R) :
    -- 1. Elliptic / Positive M₂(ℚ) regime
    (cutP0Q * cutP0Q = cutP0Q ∧
     totalityOmegaEll * totalityOmegaEll = totalityOmegaEll ∧
     _root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm cutP0Q totalityOmegaEll ≠ 0 ∧
     aporia cutP0Q totalityOmegaEll = !![(1 / 4 : ℚ), 0; 0, 0] ∧
     aporia cutP0Q totalityOmegaEll ≠ 0 ∧
     M cutP0Q totalityOmegaEll = !![(1 / 4 : ℚ), 0; 0, 1 / 4] ∧
     Sigma0 cutP0Q totalityOmegaEll = 0 ∧
     B cutP0Q totalityOmegaEll * B cutP0Q totalityOmegaEll = 1 ∧
     JOmega totalityOmegaEll = !![0, 1; 1, 0] ∧
     JOmega totalityOmegaEll * JOmega totalityOmegaEll = 1 ∧
     JOmega totalityOmegaEll ≠ Gamma cutP0Q) ∧
    -- 2. Parabolic / Jordan M₂(ℤ) null-horizon regime & Krein EP2 non-diagonalizability
    ((totalityOmegaPar * totalityOmegaPar = totalityOmegaPar ∧
      T cutP0 totalityOmegaPar = cutP0 ∧
      G cutP0 totalityOmegaPar = 0 ∧
      X cutP0 totalityOmegaPar = 0 ∧
      Y cutP0 totalityOmegaPar = !![0, 1; 0, 0] ∧
      Y cutP0 totalityOmegaPar ≠ 0 ∧
      aporia cutP0 totalityOmegaPar = 0 ∧
      groundAporia cutP0 totalityOmegaPar = 0 ∧
      M cutP0 totalityOmegaPar = 0 ∧
      K cutP0 totalityOmegaPar = 0 ∧
      B cutP0 totalityOmegaPar * B cutP0 totalityOmegaPar = 0 ∧
      1 - Sigma0 cutP0 totalityOmegaPar * Sigma0 cutP0 totalityOmegaPar = 0 ∧
      B cutP0 totalityOmegaPar = !![0, 2; 0, 0] ∧
      B cutP0 totalityOmegaPar ≠ 0 ∧
      JOmega totalityOmegaPar = !![1, 2; 0, -1] ∧
      JOmega totalityOmegaPar * JOmega totalityOmegaPar = 1 ∧
      _root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm cutP0 (JOmega totalityOmegaPar) =
        !![0, 2; 0, 0] ∧
      _root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm cutP0 (JOmega totalityOmegaPar) ≠ 0 ∧
      JOmega totalityOmegaPar ≠ Gamma cutP0) ∧
     (let η : Matrix (Fin 2) (Fin 2) R := kreinNullEta
      let H : Matrix (Fin 2) (Fin 2) R := jordanBlock2 μ
      let v₀ : Fin 2 → R := ![1, 0]
      let N : Matrix (Fin 2) (Fin 2) R := H - μ • (1 : Matrix (Fin 2) (Fin 2) R)
      η.transpose = η ∧ η * η = 1 ∧ η.det = -1 ∧ η * H = H.transpose * η ∧
        Matrix.trace H ^ 2 - 4 * H.det = 0 ∧ H.mulVec v₀ = μ • v₀ ∧ v₀ ⬝ᵥ η.mulVec v₀ = 0 ∧
        N * N = 0 ∧ N ≠ 0 ∧
        ∀ (S Sinv : Matrix (Fin 2) (Fin 2) R), S * Sinv = 1 →
          ∀ c : R, S * H * Sinv ≠ c • (1 : Matrix (Fin 2) (Fin 2) R))) ∧
    -- 3. Hyperbolic / Krein M₂(ℤ) regime + Mannheim V-metric restoration
    (cutP0 * cutP0 = cutP0 ∧
     totalityOmega0 * totalityOmega0 = totalityOmega0 ∧
     _root_.InfoGeometry.OperatorAlgebra.PeirceSpine.comm cutP0 kreinEta0 = 0 ∧
     kreinEta0.transpose = kreinEta0 ∧
     kreinEta0.det = -2 ∧
     kreinEta0 * totalityOmega0 = !![4, 2; 2, 1] ∧
     kreinEta0 * totalityOmega0 = totalityOmega0.transpose * kreinEta0 ∧
     (JOmega totalityOmega0).transpose * kreinEta0 * JOmega totalityOmega0 = kreinEta0 ∧
     aporia cutP0 totalityOmega0 = !![-2, 0; 0, 0] ∧
     1 - Sigma0 cutP0 totalityOmega0 * Sigma0 cutP0 totalityOmega0 = !![-8, 0; 0, -8] ∧
     JOmega totalityOmega0 = !![3, 2; -4, -3] ∧
     mannheimV0 = !![6, 4; 4, 3] ∧
     mannheimV0.transpose = mannheimV0 ∧
     mannheimV0.det = 2 ∧
     (∀ x y : ℤ, 6 * x ^ 2 + 8 * x * y + 3 * y ^ 2 = (2 * x + y) ^ 2 + 2 * (x + y) ^ 2) ∧
     (∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) → 0 < (2 * x + y) ^ 2 + 2 * (x + y) ^ 2)) :=
  ⟨concrete_mat2Q_elliptic_positive_witness,
   ⟨concrete_mat2Z_parabolic_jordan_horizon_witness,
    krein_exceptional_point_jordan_non_diagonalizable μ⟩,
   concrete_mat2Z_krein_mannheim_V_metric_witness⟩

end ThreeRegime

section KleinBottleAndApollonianStrip

/-- Klein-bottle KMS half-period glide reflection `σ(u, τ) = (-u, τ + β/2)` on `ℝ × ℝ`. -/
def kleinBottleKMSGlide (β : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2 + β / 2)

/-- Frequency/time-reversal reflection `T(u, t) = (u, -t)` on the centered Riemann strip. -/
def stripT (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

/-- Horizon/scale reflection `P(u, t) = (-u, t)` across `u = 0` (`Re s = 1/2`). -/
def stripP (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)

/-- Functional-equation inversion `PT(u, t) = (-u, -t)` (`s ↦ 1 - s`). -/
def stripPT (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, -p.2)

/-- Apollonian Cayley–Möbius map `w ↦ (w - 1/2) / (w + 1/2)` anchoring poles `P_± = ±1/2`. -/
def apollonianCayley (w : ℂ) : ℂ := (w - (1 / 2 : ℂ)) / (w + (1 / 2 : ℂ))

/-- Formalizes the Klein-bottle KMS half-period glide reflection (fixed-point-free, orientation-
reversing, squaring to full `β`-translation), the centered strip Klein four-group `V₄ = {1, P, T, PT}`
preserving the mirror axis `u = 0`, the Apollonian bipolar radical bisector identity
`|w - 1/2|² - |w + 1/2|² = -2 Re w`, Cayley pole inversion, and Li's single-pole unit-circle
nonnegativity. -/
theorem kleinBottle_kms_centeredStrip_apollonian_bridge
    (β : ℝ) (hβ : β ≠ 0) (p : ℝ × ℝ) (w : ℂ)
    (hw1 : w ≠ (1 / 2 : ℂ)) (hw2 : w ≠ -(1 / 2 : ℂ))
    (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 = 1) :
    kleinBottleKMSGlide β p ≠ p ∧
    kleinBottleKMSGlide β (kleinBottleKMSGlide β p) = (p.1, p.2 + β) ∧
    Matrix.det !![(-1 : ℝ), 0; 0, 1] = -1 ∧
    stripT (stripT p) = p ∧
    stripP (stripP p) = p ∧
    stripPT (stripPT p) = p ∧
    stripP (stripT p) = stripPT p ∧
    stripT (stripP p) = stripPT p ∧
    (stripP p = p ↔ p.1 = 0) ∧
    Complex.normSq (w - (1 / 2 : ℂ)) - Complex.normSq (w + (1 / 2 : ℂ)) = -2 * w.re ∧
    (Complex.normSq (w - (1 / 2 : ℂ)) = Complex.normSq (w + (1 / 2 : ℂ)) ↔ w.re = 0) ∧
    apollonianCayley (1 / 2 : ℂ) = 0 ∧
    apollonianCayley (-w) * apollonianCayley w = 1 ∧
    (1 - z).re + (1 - star z).re = (1 - z.re) ^ 2 + z.im ^ 2 ∧
    0 ≤ (1 - z).re + (1 - star z).re := by
  have hglide_ne : kleinBottleKMSGlide β p ≠ p := by
    intro hp
    have hsnd := congrArg Prod.snd hp
    simp only [kleinBottleKMSGlide] at hsnd
    have hβ0 : β = 0 := by linarith
    exact hβ hβ0
  have hglide_sq : kleinBottleKMSGlide β (kleinBottleKMSGlide β p) = (p.1, p.2 + β) := by
    ext <;> simp [kleinBottleKMSGlide]
    ring
  have hdet : Matrix.det !![(-1 : ℝ), 0; 0, 1] = -1 := by
    simp [Matrix.det_fin_two]
  have hTT : stripT (stripT p) = p := by ext <;> simp [stripT]
  have hPP : stripP (stripP p) = p := by ext <;> simp [stripP]
  have hPTPT : stripPT (stripPT p) = p := by ext <;> simp [stripPT]
  have hPT1 : stripP (stripT p) = stripPT p := by ext <;> simp [stripP, stripT, stripPT]
  have hPT2 : stripT (stripP p) = stripPT p := by ext <;> simp [stripP, stripT, stripPT]
  have hPfix : stripP p = p ↔ p.1 = 0 := by
    constructor
    · intro hp
      have hfst := congrArg Prod.fst hp
      simp only [stripP] at hfst
      linarith
    · intro hx
      ext <;> simp [stripP, hx]
  have hapol_diff :
      Complex.normSq (w - (1 / 2 : ℂ)) - Complex.normSq (w + (1 / 2 : ℂ)) = -2 * w.re := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
    ring
  have hapol_eq :
      Complex.normSq (w - (1 / 2 : ℂ)) = Complex.normSq (w + (1 / 2 : ℂ)) ↔ w.re = 0 := by
    rw [← sub_eq_zero, hapol_diff]
    constructor <;> intro h <;> linarith
  have hcay0 : apollonianCayley (1 / 2 : ℂ) = 0 := by
    simp [apollonianCayley]
  have hcay_inv : apollonianCayley (-w) * apollonianCayley w = 1 := by
    have hden1 : -w + (1 / 2 : ℂ) ≠ 0 := by
      intro h0
      apply hw1
      linear_combination -h0
    have hden2 : w + (1 / 2 : ℂ) ≠ 0 := by
      intro h0
      apply hw2
      linear_combination h0
    have hnum : (-w - (1 / 2 : ℂ)) * (w - (1 / 2 : ℂ)) =
        (-w + (1 / 2 : ℂ)) * (w + (1 / 2 : ℂ)) := by ring
    rw [apollonianCayley, apollonianCayley, div_mul_div_comm, hnum,
      div_self (mul_ne_zero hden1 hden2)]
  have hli_eq : (1 - z).re + (1 - star z).re = (1 - z.re) ^ 2 + z.im ^ 2 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    linarith [hz]
  have hli_nonneg : 0 ≤ (1 - z).re + (1 - star z).re := by
    rw [hli_eq]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨hglide_ne, hglide_sq, hdet, hTT, hPP, hPTPT, hPT1, hPT2, hPfix,
    hapol_diff, hapol_eq, hcay0, hcay_inv, hli_eq, hli_nonneg⟩

end KleinBottleAndApollonianStrip

end InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityThreeRegimeSynthesis

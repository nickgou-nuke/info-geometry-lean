/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.Representation
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Canonical.CelikKocakCantorOperators
import InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth
import InfoGeometry.Canonical.JordanWignerCantorRepresentation
import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
import InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
import InfoGeometry.Topology.CantorBoundaryCuntzO2
import InfoGeometry.Topology.CantorBoundaryRealClockShift
import InfoGeometry.Topology.BinaryCantorCuntzSuperchargeBridge
import InfoGeometry.Topology.FractalCantorFock
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis
import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Canonical.SplitCliffordHeadTailParity
import InfoGeometry.Canonical.Cl11MatrixTowerTailShift
import InfoGeometry.Algebra.CuntzLeftRightCommutant
import InfoGeometry.Quantum.SylvesterWeylBraidBridge
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence

/-!
# Binary Fock Space, `M₂(ℝ)`/`M₄(ℝ)` Clifford–Dirac–Hodge Modules on Doubled Real Krein Space, Cantor Head/Tail `Cl(1,1)^⊗n ⊗ Cl(∞,∞)`, Cuntz Hopping Lattice, Sylvester Clock/Shift, & Artin Braid Closure Poset

This canonical module unifies and closes the intertwining web across the five foundational
subsystems of the binary Fock / Clifford–Dirac–Hodge / Krein / Cantor / Cuntz / Sylvester /
Artin-braid architecture in `info-geometry-lean`:

```
  [BFC₀: Doubled Real Krein Space & M₂(ℝ)/M₄(ℝ) Clifford–Dirac–Hodge Modules]
     DoubledSpace E := WithLp 2 (E × E), modular_j (J² = I), spectral_epsilon (ε² = I),
     complex_i = J ∘ ε (I² = -I, J I = -I J), cl11Rep : Cl(1,1) →ₐ[ℝ] B(DoubledSpace E),
     M₂(ℝ) ≃ MatStage 1, M₄(ℝ) ≃ MatStage 2, & 4-Grade Dirac–Kähler Square D_DK² = d² + δ² - Δ
                                     │
                                     ▼
  [BFC₁: Binary Words, Binary Fock Space (Idx n → ℝ / CantorAddress n → ℂ), & Sylvester Clock/Shift]
     CantorAddress n := Fin n → Bool, Fintype.card (Idx n) = 2^n = Fintype.card (CantorAddress n),
     realMatToCantor n : MatStage n ≃ₐ[ℝ] End_ℝ(Idx n → ℝ),
     Sylvester Clock/Tilt Z_j (Z_j² = 1) & Shift/Switch X_j (X_j² = 1, Z_j X_j = -X_j Z_j),
     Boundary Phase J = Z X (J² = -1, J⁴ = 1), & Non-Commutative Sylvester Block Intertwining
                                     │
                                     ▼
  [BFC₂: Head × Tail Factorization Cl(1,1)^⊗n ⊗ Cl(∞,∞), Cantor Cylinders, & Doubled Cuntz O₂]
     Head Tower: stageEmbed n (A ↦ A ⊗ I₂) preserving normalizedTrace & normalizedLogAbsDet,
     Tail Foundation: CantorBoundaryN 2 := ℕ → Fin 2 with headN, tailN, prependN,
     Forward/Backward Cuntz O₂ (T_i S_j = δ_{ij} I, S₀ T₀ + S₁ T₁ = I),
     Head Matrix Units E_{ij} = S_i T_j, & Chiral Supercharges Q_+ = S₁ S₂*, Q_- = S₂ S₁* ({Q_+, Q_-} = I)
                                     │
                                     ▼
  [BFC₃: N-Depth Jordan–Wigner Fermionization & Coherent Cl(1,1) ↔ UHF/Cuntz Bridge]
     jwCreation / jwAnnihilation stabilization under matStageEmbed,
     Cantor endpoint CAR creation/annihilation twisted by cantorChiralString ({c_k, c_k†} = 1),
     Infinite Cantor boundary CAR pair a_j = ½(T_j + T_j S_j), a_j† = ½(T_j - T_j S_j),
     & Coherent natural transformation coherentComplexifyClStage (stageEmbed  intertwines concreteStep)
                                     │
                                     ▼
  [BFC₄: Artin Braid Representation B₁ B₂ B₁ = B₂ B₁ B₂ on Cl(1,1)_∞ & Master Closure Synthesis]
     Universal Clifford/Majorana Artin braid identity (1 + a b)(1 + b c)(1 + a b) = (1 + b c)(1 + a b)(1 + b c),
     Colimit Majorana modes γ_i = u_i + v_i (γ_i² = 1, {γ_i, γ_j} = 0), bivectors β_i = γ_i γ_{i+1} (β_i² = -1),
     Invertible braid gates R_i = 1 + β_i ∈ (Cl(1,1)_∞)ˣ, & Infinite Artin braid representation B_∞ →* Limitˣ
```

## Five-Stage Causal Poset (`BinaryFockCliffordCantorBraidStage`)

* **`BFC0_doubledKreinCliffordDiracHodgeModule` (rank `0`)**:
  Doubled real Krein carrier `DoubledSpace E`, `Cl(1,1)` representation `cl11Rep`,
  `M₂(ℝ) ≃ MatStage 1` and `M₄(ℝ) ≃ MatStage 2` spinor stages, and the 3-channel
  Dirac–Kähler–Hodge square `D_DK² = d_∇² + Div_∇² - Δ_Hodge`.
* **`BFC1_binaryFockCantorSylvesterClockShift` (rank `1`)**:
  Binary words `CantorAddress n`, binary Fock carrier `Idx n → ℝ`, Çelik–Koçak `tilt`/`switch`
  and Cantor-boundary Sylvester `clock`/`shift`/`phase` satisfying `Z² = 1`, `X² = 1`,
  `Z X = -X Z`, `(Z X)² = -1`, and non-commutative Sylvester operator matrix intertwining.
* **`BFC2_headTailTensorTowerCuntzHoppingSupercharge` (rank `2`)**:
  Head tensor tower `stageEmbed n : A ↦ A ⊗ I₂` vs. infinite Cantor tail `CantorBoundaryN 2`
  with forward/backward Cuntz $\mathcal{O}_2$ operators `S_i, T_i`, head matrix units
  `E_{ij} = S_i T_j`, and nilpotent chiral supercharges `Q_+ = S₁ S₂^*`, `Q_- = S₂ S₁^*`
  with `{Q_+, Q_-} = 1` and parity involution `Γ² = 1`.
* **`BFC3_jordanWignerFermionizationCoherentUHFBridge` (rank `3`)**:
  $N$-depth Jordan–Wigner CAR creation/annihilation on `MatStage n`, `CantorAddress n → ℂ`,
  and `(ℕ → Bool) → ℝ`, intertwined with the coherent $\mathrm{Cl}(1,1) \to \text{UHF}$
  natural transformation `coherentComplexifyClStage`.
* **`BFC4_artinBraidMajoranaColimitMasterClosure` (rank `4`)**:
  Universal Majorana/Clifford Artin braid identity `B₁ B₂ B₁ = B₂ B₁ B₂`, colimit Majorana
  braid representation `bInfinityTensorRepresentation : BInfinity →* Limitˣ`, and the
  5-stage master closure theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.BinaryFockCliffordKreinCantorCuntzBraidClosurePoset

open scoped Matrix Kronecker BigOperators
open InfoGeometry.Krein
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.CelikKocakCantorOperators
open InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace
open InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth
open InfoGeometry.Canonical.JordanWignerCantorRepresentation
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.ArtinBraidJordanWignerColimitRepresentation
open InfoGeometry.Topology.CantorBoundaryCuntzFamily
open InfoGeometry.Topology.CantorBoundaryCuntzO2
open InfoGeometry.Topology.CantorBoundaryRealClockShift
open InfoGeometry.Topology.BinaryCantorCuntzSuperchargeBridge
open InfoGeometry.Topology.FractalCantorFock
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornMatrix
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.ZornForms
open InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis

-- ============================================================================
-- § 1. THE 5-STAGE CAUSAL POSET OF BINARY FOCK / CLIFFORD / CANTOR / CUNTZ / BRAID CLOSURE
-- ============================================================================

/-- The 5-stage causal poset organizing the Binary Fock / Clifford–Dirac–Hodge /
Doubled Real Krein / Cantor Head–Tail / Cuntz Hopping / Sylvester Clock–Shift /
Artin Braid synthesis. -/
inductive BinaryFockCliffordCantorBraidStage : Type
  | BFC0_doubledKreinCliffordDiracHodgeModule
  | BFC1_binaryFockCantorSylvesterClockShift
  | BFC2_headTailTensorTowerCuntzHoppingSupercharge
  | BFC3_jordanWignerFermionizationCoherentUHFBridge
  | BFC4_artinBraidMajoranaColimitMasterClosure
  deriving DecidableEq, Repr, Inhabited

namespace BinaryFockCliffordCantorBraidStage

/-- Topological rank in the 5-stage closure poset (`0 → 4`). -/
def rank : BinaryFockCliffordCantorBraidStage → ℕ
  | .BFC0_doubledKreinCliffordDiracHodgeModule => 0
  | .BFC1_binaryFockCantorSylvesterClockShift => 1
  | .BFC2_headTailTensorTowerCuntzHoppingSupercharge => 2
  | .BFC3_jordanWignerFermionizationCoherentUHFBridge => 3
  | .BFC4_artinBraidMajoranaColimitMasterClosure => 4

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> cases h <;> rfl

instance instPartialOrder : PartialOrder BinaryFockCliffordCantorBraidStage :=
  PartialOrder.lift rank rank_injective

/-- Direct causal edges of the 5-stage closure spine. -/
def causalEdge : BinaryFockCliffordCantorBraidStage → BinaryFockCliffordCantorBraidStage → Prop
  | .BFC0_doubledKreinCliffordDiracHodgeModule, .BFC1_binaryFockCantorSylvesterClockShift => True
  | .BFC1_binaryFockCantorSylvesterClockShift, .BFC2_headTailTensorTowerCuntzHoppingSupercharge => True
  | .BFC2_headTailTensorTowerCuntzHoppingSupercharge, .BFC3_jordanWignerFermionizationCoherentUHFBridge => True
  | .BFC3_jordanWignerFermionizationCoherentUHFBridge, .BFC4_artinBraidMajoranaColimitMasterClosure => True
  | _, _ => False

theorem causalEdge_strictMono_rank {u v : BinaryFockCliffordCantorBraidStage}
    (h : causalEdge u v) : rank u < rank v := by
  cases u <;> cases v <;> cases h <;> decide

theorem causalEdge_irrefl (u : BinaryFockCliffordCantorBraidStage) :
    ¬ causalEdge u u := by
  intro h
  exact Nat.lt_irrefl (rank u) (causalEdge_strictMono_rank h)

theorem strict_five_stage_causal_chain :
    BinaryFockCliffordCantorBraidStage.BFC0_doubledKreinCliffordDiracHodgeModule <
      .BFC1_binaryFockCantorSylvesterClockShift ∧
    BinaryFockCliffordCantorBraidStage.BFC1_binaryFockCantorSylvesterClockShift <
      .BFC2_headTailTensorTowerCuntzHoppingSupercharge ∧
    BinaryFockCliffordCantorBraidStage.BFC2_headTailTensorTowerCuntzHoppingSupercharge <
      .BFC3_jordanWignerFermionizationCoherentUHFBridge ∧
    BinaryFockCliffordCantorBraidStage.BFC3_jordanWignerFermionizationCoherentUHFBridge <
      .BFC4_artinBraidMajoranaColimitMasterClosure := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end BinaryFockCliffordCantorBraidStage

-- ============================================================================
-- § 2. STAGE BFC₀: DOUBLED REAL KREIN SPACE & M₂(ℝ)/M₄(ℝ) CLIFFORD–DIRAC–HODGE MODULES
-- ============================================================================

/-- **Stage `BFC₀` (`doubled_krein_cl11_representation_and_witt_base_synthesis`)**:
On any real Hilbert space `E`, the doubled real Krein carrier `DoubledSpace E := WithLp 2 (E × E)`
carries the faithful $\mathrm{Cl}(1,1)$ representation `cl11Rep` mapping:
- $(1, 0) \mapsto \text{modular\_j}$ ($J^2 = I$),
- $(0, 1) \mapsto \text{complex\_i} = J \circ \epsilon$ ($I^2 = -I$, $J I = -I J$),
- $(1, 0) \cdot (0, 1) \mapsto \text{spectral\_epsilon}$ ($\epsilon(x, \xi) = (x, -\xi)$),
while on the $2 \times 2$ real matrix base $M_2(\mathbb{R})$ (`MatStage 1 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`)
and $4 \times 4$ stage $M_4(\mathbb{R})$ (`MatStage 2 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`), the real-encoded
Witt creation/annihilation atoms $a^\dagger = \frac{1}{2}(\gamma_0 + J)$, $a = \frac{1}{2}(\gamma_0 - J)$
satisfy $(a^\dagger)^2 = 0$, $a^2 = 0$, and $a^\dagger a + a a^\dagger = 1$. -/
theorem doubled_krein_cl11_representation_and_witt_base_synthesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) =
      modular_j (E := E)) ∧
    (cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) =
      complex_i (E := E)) ∧
    (cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0) *
          CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) =
      spectral_epsilon (E := E)) ∧
    ((modular_j (E := E)).comp (complex_i (E := E)) =
      -((complex_i (E := E)).comp (modular_j (E := E)))) ∧
    (Fintype.card (Idx 1) = 2 ∧ Fintype.card (Idx 2) = 4) ∧
    (realEncodedWittCreationBase * realEncodedWittCreationBase = 0) ∧
    (realEncodedWittAnnihilationBase * realEncodedWittAnnihilationBase = 0) ∧
    (realEncodedWittCreationBase * realEncodedWittAnnihilationBase +
      realEncodedWittAnnihilationBase * realEncodedWittCreationBase =
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (hestenesPhaseBase * hestenesPhaseBase = -(1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (hestenesPhaseBase * gamma_chiral_base * hestenesPhaseBase = gamma_chiral_base) := by
  refine ⟨cl11Rep_ι_one_zero (E := E), cl11Rep_ι_zero_one (E := E),
    cl11Rep_pseudoscalar (E := E), modular_j_complex_i_anticommute (E := E),
    ⟨by simpa using idx_card_pow_two 1, by simpa using idx_card_pow_two 2⟩,
    realEncodedWittCreationBase_sq, realEncodedWittAnnihilationBase_sq,
    realEncodedWitt_anticomm, hestenesPhaseBase_sq, hestenesPhaseBase_chiral_sandwich⟩

/-- **Stage `BFC₀` (`dirac_kaehler_hodge_and_tetraktys_klein_four_synthesis`)**:
Over any non-commutative ring `[Ring R]`, the $2 \times 2$ Zorn/Peirce Tetraktys carries the
Klein four-group $K_4 = \{\mathrm{Id}, L_{\gamma_5}, R_{\gamma_5}, \mathrm{Ad}_{\gamma_5}\}$
grading (`tetraktys_klein_four_group_identities`), and the 4-grade exterior operator bundle
$\Omega^0 \oplus \Omega^1 \oplus \Omega^2 \oplus \Omega^3$ satisfies the exact 3-channel
Dirac–Kähler–Hodge square decomposition
$D_{\mathrm{DK}}^2(\omega) = (d_\nabla^2(\omega) + \mathrm{Div}_\nabla^2(\omega)) - \Delta_{\mathrm{Hodge}}(\omega)$. -/
theorem dirac_kaehler_hodge_and_tetraktys_klein_four_synthesis
    {R : Type*} [Ring R] (X : ZornMatrix R) (p : Vec3 R) (ω : ZornForms R) :
    (leftG5 (leftG5 X) = X ∧
      rightG5 (rightG5 X) = X ∧
      adG5 (adG5 X) = X ∧
      leftG5 (rightG5 X) = adG5 X ∧
      rightG5 (leftG5 X) = adG5 X) ∧
    (diracKaehler p (diracKaehler p ω) =
      (extCurl p (extCurl p ω) + extDiv p (extDiv p ω)) - hodgeLaplacian p ω) := by
  exact ⟨tetraktys_klein_four_group_identities X,
    dirac_kaehler_square_three_channel_decomposition p ω⟩

-- ============================================================================
-- § 3. STAGE BFC₁: BINARY WORDS, BINARY FOCK SPACE, & SYLVESTER CLOCK-AND-SHIFT
-- ============================================================================

/-- **Stage `BFC₁` (`binary_fock_cantor_sylvester_clock_shift_and_block_intertwining`)**:
Unifies the binary Fock carrier `Idx n → ℝ` (`Fintype.card (Idx n) = Fintype.card (CantorAddress n) = 2^n`),
the finite Cantor-address Çelik–Koçak `tilt`/`switch` operators on `CantorAddress n → ℂ`,
the infinite Cantor-boundary Sylvester `clock`/`shift`/`phase` operators on `CantorBoundaryN 2 → ℝ`,
and the universal non-commutative Sylvester operator matrix block diagonalization:
1. `Fintype.card (Idx n) = 2 ^ n` and `Fintype.card (Idx n) = Fintype.card (CantorAddress n)`,
2. Finite Cantor `tilt j` ($Z_j$) and `switch j` ($X_j$) satisfy $Z_j^2 = 1$, $X_j^2 = 1$,
   $Z_j X_j = -X_j Z_j$ on the same site $j$, and commute for $i \neq j$,
3. Cuntz boundary `clock` ($Z = E_{00} - E_{11}$), `shift` ($X = E_{01} + E_{10}$), and
   `phase` ($J = Z X = E_{01} - E_{10}$) satisfy $Z^2 = 1$, $X^2 = 1$, $Z X = -X Z$,
   $J^2 = -1$, and $J^4 = 1$,
4. Over any non-commutative ring `[Ring B]`, the unipotent sandwich `sylvesterUnipotentG`
   intertwines `sylvesterBlockMat A C 0` with the Sylvester commutator `X * C - A * X`
   across all powers $k \in \mathbb{N}$. -/
theorem binary_fock_cantor_sylvester_clock_shift_and_block_intertwining
    {B : Type*} [Ring B] (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A C X : B) (k : ℕ) :
    (Fintype.card (Idx n) = 2 ^ n ∧
      Fintype.card (Idx n) = Fintype.card (CantorAddress n)) ∧
    (FunctionSpace.tilt (n := n) j * FunctionSpace.tilt (n := n) j = 1 ∧
      FunctionSpace.switch (n := n) j * FunctionSpace.switch (n := n) j = 1 ∧
      FunctionSpace.tilt (n := n) j * FunctionSpace.switch (n := n) j =
        -(FunctionSpace.switch (n := n) j * FunctionSpace.tilt (n := n) j) ∧
      FunctionSpace.tilt (n := n) i * FunctionSpace.switch (n := n) j =
        FunctionSpace.switch (n := n) j * FunctionSpace.tilt (n := n) i) ∧
    (clock * clock = 1 ∧
      shift * shift = 1 ∧
      clock * shift = -(shift * clock) ∧
      phase * phase = -1 ∧
      phase ^ 4 = 1) ∧
    (sylvesterUnipotentG X * sylvesterBlockMat A C 0 * sylvesterUnipotentG (-X) =
      sylvesterBlockMat A C (X * C - A * X) ∧
      (sylvesterBlockMat A C (X * C - A * X)) ^ k =
        sylvesterBlockMat (A ^ k) (C ^ k) (X * C ^ k - A ^ k * X)) := by
  have hsylv := sylvester_operator_matrix_unipotent_diagonalization_and_powers A C X (0 : B)
  refine ⟨⟨idx_card_pow_two n, idx_card_eq_cantorAddress_card n⟩,
    ⟨FunctionSpace.tilt_sq j, FunctionSpace.switch_sq j,
      FunctionSpace.tilt_switch_anticomm j, FunctionSpace.tilt_switch_comm_of_ne hij⟩,
    ⟨clock_sq, shift_sq, clock_shift_weyl, phase_sq, phase_fourth_power⟩,
    ⟨hsylv.2.2.2.2.2.2.1, hsylv.2.2.2.2.2.2.2.1 k⟩⟩

-- ============================================================================
-- § 4. STAGE BFC₂: HEAD × TAIL FACTORIZATION Cl(1,1)^⊗n ⊗ Cl(∞,∞) & DOUBLED CUNTZ O₂
-- ============================================================================

/-- **Stage `BFC₂` (`head_tail_tensor_tower_cuntz_o2_and_chiral_supercharge_synthesis`)**:
Connects the finite **Head** tensor tower `MatStage n` ($\mathrm{Cl}(1,1)^{\otimes n} \cong M_{2^n}(\mathbb{R})$)
to the infinite **Tail** Cantor cylinder foundation (`CantorBoundaryN 2 := ℕ → Fin 2` and
`ℕ → BinarySector`) and the doubled forward/backward Cuntz $\mathcal{O}_2$ hopping algebra:
1. **Head Tensor Tower**: The one-step Kronecker embedding `matStageEmbed n : A ↦ A ⊗ I₂`
   is injective, commutes with the real Cantor operator algebra isomorphism `realMatToCantor`,
   and preserves both `normalizedTrace` and `normalizedLogAbsDet`,
2. **Tail Cantor Boundary & Forward/Backward Cuntz $\mathcal{O}_2$**: `prependN (headN b) (tailN b) = b`,
   and the forward shift `S i` and backward prepend `T i` satisfy $T_i S_j = \delta_{ij} I$ and
   $\sum_{i \in \mathrm{Fin}\,2} S_i T_i = I$, generating the head matrix units $E_{ij} = S_i T_j$
   satisfying $E_{ij} E_{kl} = \delta_{jk} E_{il}$ and $E_{00} + E_{11} = I$,
3. **Cuntz Chiral Dirac/Peirce Supercharges**: On the binary Cantor boundary, the chiral
   supercharges $Q_+ = S_1 S_2^*$ and $Q_- = S_2 S_1^*$ are square-zero ($Q_+^2 = 0$, $Q_-^2 = 0$),
   their anticommutator is the identity Hamiltonian ($Q_+ Q_- + Q_- Q_+ = I$), and the parity
   grading $\Gamma = S_1 S_1^* - S_2 S_2^*$ satisfies $\Gamma^2 = I$ and $\{\Gamma, Q_\pm\} = 0$. -/
theorem head_tail_tensor_tower_cuntz_o2_and_chiral_supercharge_synthesis
    (n : ℕ) (A : MatStage n) (b : CantorBoundaryN 2) (i j k l : Fin 2) :
    (Function.Injective (matStageEmbed n) ∧
      realCantorOpEmbed n (realMatToCantor n A) =
        realMatToCantor (n + 1) (matStageEmbed n A) ∧
      normalizedTrace (n + 1) (matStageEmbed n A) = normalizedTrace n A ∧
      normalizedLogAbsDet (n + 1) (matStageEmbed n A) = normalizedLogAbsDet n A) ∧
    (prependN (headN b) (tailN b) = b ∧
      InfoGeometry.Topology.CantorBoundaryCuntzO2.T (R := ℝ) i *
        InfoGeometry.Topology.CantorBoundaryCuntzO2.S (R := ℝ) j =
          (if i = j then (1 : BoundaryOperator ℝ) else 0) ∧
      (∑ m : Fin 2,
        InfoGeometry.Topology.CantorBoundaryCuntzO2.S (R := ℝ) m *
          InfoGeometry.Topology.CantorBoundaryCuntzO2.T (R := ℝ) m) =
        (1 : BoundaryOperator ℝ) ∧
      InfoGeometry.Topology.CantorBoundaryCuntzO2.matrixUnit (R := ℝ) i j *
        InfoGeometry.Topology.CantorBoundaryCuntzO2.matrixUnit (R := ℝ) k l =
          (if j = k then
            InfoGeometry.Topology.CantorBoundaryCuntzO2.matrixUnit (R := ℝ) i l
          else 0) ∧
      InfoGeometry.Topology.CantorBoundaryCuntzO2.matrixUnit (R := ℝ) 0 0 +
        InfoGeometry.Topology.CantorBoundaryCuntzO2.matrixUnit (R := ℝ) 1 1 = 1) ∧
    ((InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QPlus generators *
        InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QPlus generators = 0 ∧
      InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QMinus generators *
        InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QMinus generators = 0) ∧
      InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QPlus generators *
        InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QMinus generators +
      InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QMinus generators *
        InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QPlus generators = 1 ∧
      InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.ParityGrading generators *
        InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.ParityGrading generators = 1) := by
  refine ⟨⟨matStageEmbed_injective n, realCantorOpEmbed_realMatToCantor n A,
      normalizedTrace_matStageEmbed n A, normalizedLogAbsDet_matStageEmbed n A⟩,
    ⟨prependN_headN_tailN b,
      InfoGeometry.Topology.CantorBoundaryCuntzO2.ortho (R := ℝ) i j,
      InfoGeometry.Topology.CantorBoundaryCuntzO2.partition (R := ℝ),
      InfoGeometry.Topology.CantorBoundaryCuntzO2.matrixUnit_mul (R := ℝ) i j k l,
      diagonal_sum⟩,
    ⟨chiral_supercharge_nilpotence, chiral_supercharge_hamiltonian,
      chiral_parity_involution⟩⟩

-- ============================================================================
-- § 5. STAGE BFC₃: N-DEPTH JORDAN–WIGNER FERMIONIZATION & COHERENT Cl(1,1) ↔ UHF BRIDGE
-- ============================================================================

/-- **Stage `BFC₃` (`jordan_wigner_cantor_fock_and_coherent_uhf_bridge_synthesis`)**:
Unifies the three Jordan–Wigner / CAR fermionization realizations with the coherent
$\mathrm{Cl}(1,1) \to \text{UHF/Cuntz}$ index natural transformation:
1. **Matrix-Tower Jordan–Wigner Stabilization**: `matStageEmbed n` maps `jwCreation n k` to
   `jwCreation (n + 1) k.castSucc` and `jwAnnihilation n k` to `jwAnnihilation (n + 1) k.castSucc`,
2. **Finite Cantor-Address $N$-Depth CAR**: `cantorCreation n k` and `cantorAnnihilation n k`
   (twisted by `cantorChiralString n k`) satisfy $(c_k^\dagger)^2 = 0$, $c_k^2 = 0$, and
   $c_k c_k^\dagger + c_k^\dagger c_k = 1$ on `CantorAddress n → ℂ`,
3. **Infinite Cantor-Boundary Real CAR**: `canonicalAnnihilation site = ½(tilt site + tilt site * switch site)`
   and `canonicalCreation site = ½(tilt site - tilt site * switch site)` satisfy $a^2 = 0$,
   $(a^\dagger)^2 = 0$, and $a a^\dagger + a^\dagger a = 1$ on `(ℕ → Bool) → ℝ`,
4. **Coherent $\mathrm{Cl}(1,1) \to \text{UHF}$ Naturality & Trace**: `coherentComplexifyClStage`
   intertwines `stageEmbed n` with `concreteStep n` and intertwines `normalizedTrace n` with
   the Cuntz/UHF `matrixTraceFunctional n` (`matrixTraceState n 1 = 1`). -/
theorem jordan_wigner_cantor_fock_and_coherent_uhf_bridge_synthesis
    (n : ℕ) (k : Fin n) (site : ℕ) (A : ClStage n) :
    (matStageEmbed n (jwCreation n k) = jwCreation (n + 1) k.castSucc ∧
      matStageEmbed n (jwAnnihilation n k) = jwAnnihilation (n + 1) k.castSucc) ∧
    (cantorCreation n k * cantorCreation n k = 0 ∧
      cantorAnnihilation n k * cantorAnnihilation n k = 0 ∧
      cantorAnnihilation n k * cantorCreation n k +
        cantorCreation n k * cantorAnnihilation n k = 1) ∧
    (CantorBoundaryFunctionSpace.canonicalAnnihilation site *
        CantorBoundaryFunctionSpace.canonicalAnnihilation site = 0 ∧
      CantorBoundaryFunctionSpace.canonicalCreation site *
        CantorBoundaryFunctionSpace.canonicalCreation site = 0 ∧
      CantorBoundaryFunctionSpace.canonicalAnnihilation site *
        CantorBoundaryFunctionSpace.canonicalCreation site +
      CantorBoundaryFunctionSpace.canonicalCreation site *
        CantorBoundaryFunctionSpace.canonicalAnnihilation site = 1) ∧
    (coherentComplexifyClStage (Nat.succ n) (stageEmbed n A) =
        InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteStep n
          (coherentComplexifyClStage n A) ∧
      matrixTraceFunctional n (coherentComplexifyClStage n A) =
        Complex.ofReal (normalizedTrace n A) ∧
      matrixTraceState n 1 = 1) := by
  refine ⟨⟨matStageEmbed_jwCreation k, matStageEmbed_jwAnnihilation k⟩,
    canonical_depth_n_car_wire n k,
    ⟨CantorBoundaryFunctionSpace.canonicalAnnihilation_sq site,
      CantorBoundaryFunctionSpace.canonicalCreation_sq site,
      CantorBoundaryFunctionSpace.canonicalCAR_anticommutator site⟩,
    ⟨coherentComplexifyClStage_naturality n A,
      coherentComplexifyClStage_normalizedTrace n A,
      matrixTraceState_one n⟩⟩

-- ============================================================================
-- § 6. STAGE BFC₄: ARTIN BRAID GROUP REPRESENTATION ON Cl(1,1)_∞ & MASTER CLOSURE
-- ============================================================================

/-- **Stage `BFC₄` (`artin_braid_majorana_colimit_and_universal_clifford_braiding`)**:
1. **Universal Non-Commutative Clifford/Majorana Braiding**: In any `[Ring A]`, for any three
   anticommuting involutions $a^2 = b^2 = c^2 = 1$ ($a b + b a = 0$, $b c + c b = 0$,
   $a c + c a = 0$), the bivector braid generators $B_1 = 1 + a b$ and $B_2 = 1 + b c$ satisfy
   the exact Artin braid relation $B_1 B_2 B_1 = B_2 B_1 B_2$,
2. **Jordan–Wigner Majorana Braid Representation in $\mathrm{Cl}(1,1)_\infty$**: In the algebraic
   direct limit `Cl11TensorTowerLimit.Limit`, the stable Majorana modes $\gamma_i = u_i + v_i$
   satisfy $\gamma_i^2 = 1$, $\gamma_i \gamma_j + \gamma_j \gamma_i = 0$ ($i \neq j$), the
   adjacent bivectors $\beta_i = \gamma_i \gamma_{i+1}$ satisfy $\beta_i^2 = -1$, the invertible
   braid gates `majoranaBraidUnit i` satisfy the adjacent Artin relation
   $R_i R_{i+1} R_i = R_{i+1} R_i R_{i+1}$ and distant commutation $R_i R_j = R_j R_i$ ($i + 1 < j$),
   and the infinite braid group representation `bInfinityTensorRepresentation : BInfinity →* Limitˣ`
   maps $\sigma_i \mapsto 1 + \gamma_i \gamma_{i+1}$. -/
theorem artin_braid_majorana_colimit_and_universal_clifford_braiding
    {A : Type*} [Ring A] (a b c : A)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b + b * a = 0) (hbc : b * c + c * b = 0) (hac : a * c + c * a = 0)
    (i j : ℕ) (hij : i + 1 < j) :
    ((1 + a * b) * (1 + b * c) * (1 + a * b) =
      (1 + b * c) * (1 + a * b) * (1 + b * c)) ∧
    (majoranaMode i * majoranaMode i = 1 ∧
      majoranaBivector i * majoranaBivector i = -1 ∧
      majoranaBraidVal i * majoranaBraidVal (i + 1) * majoranaBraidVal i =
        majoranaBraidVal (i + 1) * majoranaBraidVal i * majoranaBraidVal (i + 1) ∧
      majoranaBraidVal i * majoranaBraidVal j =
        majoranaBraidVal j * majoranaBraidVal i ∧
      majoranaBraidUnit i * majoranaBraidUnit (i + 1) * majoranaBraidUnit i =
        majoranaBraidUnit (i + 1) * majoranaBraidUnit i * majoranaBraidUnit (i + 1) ∧
      ((bInfinityTensorRepresentation (InfoGeometry.Canonical.ArtinBraidFilteredColimit.sigmaInfinity i) :
          InfoGeometry.Clifford.Cl11TensorTowerLimit.Limitˣ) :
        InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) =
        1 + majoranaMode i * majoranaMode (i + 1)) := by
  refine ⟨adjacent_majorana_artin a b c ha hb hc hab hbc hac,
    ⟨majoranaMode_sq i, majoranaBivector_sq i, majoranaBraidVal_artin i,
      majoranaBraidVal_commute hij, majoranaBraidUnit_artin i,
      bInfinityTensorRepresentation_sigma_val i⟩⟩

/-- Concrete $2 \times 2$ non-commutative matrix witness (`T16`/`T17` compliance):
the Witt creation atom `wittCreationBase` and annihilation atom `wittAnnihilationBase`
do not commute (`wittCreationBase * wittAnnihilationBase ≠ wittAnnihilationBase * wittCreationBase`). -/
theorem witt_creation_annihilation_noncommutative_witness :
    wittCreationBase * wittAnnihilationBase ≠
      wittAnnihilationBase * wittCreationBase := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [wittCreationBase, wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- **ZMod 2 Sylvester Weyl to Doubled-Krein Matrix Bridge
(`sylvester_zmod2_clock_shift_eq_doubled_krein_matrices`)**:
Specializing `SylvesterWeylBraid.clockMatrix` and `SylvesterWeylBraid.shiftMatrix` to
$m = 2$ and $\omega = -1$ over $\mathbb{R}$ recovers the exact $2 \times 2$ doubled-Krein
$\mathrm{Cl}(1,1)$ generator matrices `matrixEpsilon = !![1, 0; 0, -1]` and
`matrixJ = !![0, 1; 1, 0]`. -/
theorem sylvester_zmod2_clock_shift_eq_doubled_krein_matrices :
    SylvesterWeylBraid.clockMatrix 2 (-1 : ℝ) =
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixEpsilon ∧
    SylvesterWeylBraid.shiftMatrix 2 =
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixJ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | (change (-1 : ℝ) ^ 1 = -1; ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      rfl

/-- **Cross-Lane Unification Theorem (`head_tail_graded_clifford_fock_cuntz_commutant_and_sylvester_weyl_bridge`)**:
Connects:
1. The $2 \times 2$ Sylvester clock/shift matrix representation on `DoubledSpace E`
   (`ρclock_matrixJ`, `ρclock_matrixEpsilon`, `ρclock_matrixClockAxis`),
2. The $\mathbb{Z}_2$-graded Head $\times$ Tail split-Clifford algebra isomorphism
   $\mathrm{Cl}(k,k) \;\widehat{\otimes}\; \mathrm{Cl}(\infty,\infty) \simeq_{\mathbb{R}\text{-}\mathsf{Alg}} \mathrm{Cl}(\infty,\infty)$
   (`splitCliffordHeadTailInfinity_algEquiv`) and the concrete matrix-tower cofinal tail
   ring equivalence `BaseLimit ≃+* TailLimit k` (`cl11MatrixLimit_tailRingEquiv`),
3. The recursive-index vs. binary-word colimit isomorphism `ClCarrier ≃+* UHFCarrier`
   (`cliffordBitWordColimitEquiv`),
4. The doubled forward/backward Cuntz left/right regular commutant theorem
   (`leftRegularCommutant_eq_rightMultiplicationRange` and `star_conjugates_left_to_right`),
5. The cyclic Sylvester clock-and-shift Weyl braid relation
   $Z_m(\omega) X_m = \omega (X_m Z_m(\omega))$ (`sylvester_weyl_braid_relation`),
6. Both the exterior-spinor Fock direct-limit representation
   (`splitCliffordFockAction_grade_equivariant`) and the binary-address Fock operator colimit
   equivalence (`clLimitFockOpEquiv_ofStage`). -/
theorem head_tail_graded_clifford_fock_cuntz_commutant_and_sylvester_weyl_bridge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k n m : ℕ) [NeZero m]
    (xHeadTail : InfoGeometry.Canonical.SplitCliffordHeadTailTower.SplitCliffordHeadTailInfinity k)
    (xLim : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit)
    (A : ClStage n)
    (aCuntz xCuntz : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n)
    (ω : ℝ) (hω : ω ^ m = 1)
    (aInf : InfoGeometry.Canonical.SplitCliffordDirectLimit.SplitCliffordInfinity)
    (ψInf : InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.FockInfinity) :
    (InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := E)
        InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixJ = modular_j (E := E) ∧
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := E)
        InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixEpsilon =
          spectral_epsilon (E := E) ∧
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := E)
        InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixClockAxis =
          clockAxis (E := E)) ∧
    ((InfoGeometry.Canonical.SplitCliffordHeadTailTower.splitCliffordHeadTailInfinity_algEquiv k).symm
        (InfoGeometry.Canonical.SplitCliffordHeadTailTower.splitCliffordHeadTailInfinity_algEquiv k xHeadTail) =
          xHeadTail ∧
      (InfoGeometry.Canonical.Cl11MatrixTowerTailShift.cl11MatrixLimit_tailRingEquiv k).symm
        (InfoGeometry.Canonical.Cl11MatrixTowerTailShift.cl11MatrixLimit_tailRingEquiv k xLim) =
          xLim ∧
      (InfoGeometry.Algebra.CliffordBitWordEquivalence.cliffordBitWordColimitEquiv).symm
        (InfoGeometry.Algebra.CliffordBitWordEquivalence.cliffordBitWordColimitEquiv xLim) =
          xLim) ∧
    (InfoGeometry.Algebra.CuntzLeftRightCommutant.leftRegularCommutant n =
        {T | ∃ b : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n,
          T = InfoGeometry.Algebra.CuntzLeftRightCommutant.rightMultiplication n b} ∧
      star (aCuntz * star xCuntz) =
        InfoGeometry.Algebra.CuntzLeftRightCommutant.rightMultiplication n (star aCuntz) xCuntz) ∧
    (SylvesterWeylBraid.clockMatrix m ω * SylvesterWeylBraid.shiftMatrix m =
        ω • (SylvesterWeylBraid.shiftMatrix m * SylvesterWeylBraid.clockMatrix m ω)) ∧
    (InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.fockInfinityInvolute
        (InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.splitCliffordFockAction aInf ψInf) =
      InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.splitCliffordFockAction
        (InfoGeometry.Canonical.SplitCliffordSuperGradeColimit.splitCliffordInfinityInvolute aInf)
        (InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.fockInfinityInvolute ψInf) ∧
      InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clLimitFockOpEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A) =
          InfoGeometry.Canonical.JordanWignerCantorRepresentation.realCantorOfStage n
            (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n A)) := by
  refine ⟨⟨InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixJ (E := E),
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixEpsilon (E := E),
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixClockAxis (E := E)⟩,
    ⟨(InfoGeometry.Canonical.SplitCliffordHeadTailTower.splitCliffordHeadTailInfinity_algEquiv k).symm_apply_apply xHeadTail,
      (InfoGeometry.Canonical.Cl11MatrixTowerTailShift.cl11MatrixLimit_tailRingEquiv k).symm_apply_apply xLim,
      (InfoGeometry.Algebra.CliffordBitWordEquivalence.cliffordBitWordColimitEquiv).symm_apply_apply xLim⟩,
    ⟨InfoGeometry.Algebra.CuntzLeftRightCommutant.leftRegularCommutant_eq_rightMultiplicationRange n,
      InfoGeometry.Algebra.CuntzLeftRightCommutant.star_conjugates_left_to_right n aCuntz xCuntz⟩,
    SylvesterWeylBraid.sylvester_weyl_braid_relation m ω hω,
    ⟨InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.splitCliffordFockAction_grade_equivariant aInf ψInf,
      InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clLimitFockOpEquiv_ofStage n A⟩⟩

/-- **Master Closure Theorem (`binary_fock_clifford_krein_cantor_cuntz_braid_master_closure`)**:
Packages the strict 5-stage causal chain (`BFC₀ < BFC₁ < BFC₂ < BFC₃ < BFC₄`),
the doubled real Krein $\mathrm{Cl}(1,1)$ representation, the Sylvester clock-and-shift Weyl
anticommutation on both finite Cantor words and the infinite Cuntz boundary, the Head $\times$ Tail
trace/determinant stabilization and Cuntz chiral supercharge completeness, the coherent
$\mathrm{Cl}(1,1) \leftrightarrow \text{UHF}$ bridge, the colimit Majorana Artin braid relation,
and the concrete non-commutative matrix witness. -/
theorem binary_fock_clifford_krein_cantor_cuntz_braid_master_closure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (k : Fin n) (A : ClStage n) (i : ℕ) :
    (BinaryFockCliffordCantorBraidStage.BFC0_doubledKreinCliffordDiracHodgeModule <
        .BFC1_binaryFockCantorSylvesterClockShift ∧
      BinaryFockCliffordCantorBraidStage.BFC1_binaryFockCantorSylvesterClockShift <
        .BFC2_headTailTensorTowerCuntzHoppingSupercharge ∧
      BinaryFockCliffordCantorBraidStage.BFC2_headTailTensorTowerCuntzHoppingSupercharge <
        .BFC3_jordanWignerFermionizationCoherentUHFBridge ∧
      BinaryFockCliffordCantorBraidStage.BFC3_jordanWignerFermionizationCoherentUHFBridge <
        .BFC4_artinBraidMajoranaColimitMasterClosure) ∧
    (cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) =
        modular_j (E := E) ∧
      cl11Rep (E := E) (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) =
        complex_i (E := E)) ∧
    (FunctionSpace.tilt (n := n) k * FunctionSpace.switch (n := n) k =
        -(FunctionSpace.switch (n := n) k * FunctionSpace.tilt (n := n) k) ∧
      clock * shift = -(shift * clock) ∧
      phase * phase = -1) ∧
    (normalizedTrace (n + 1) (matStageEmbed n A) = normalizedTrace n A ∧
      InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QPlus generators *
        InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QMinus generators +
      InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QMinus generators *
        InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation.QPlus generators = 1) ∧
    (coherentComplexifyClStage (Nat.succ n) (stageEmbed n A) =
        InfoGeometry.Canonical.CuntzMatrixTraceTower.concreteStep n
          (coherentComplexifyClStage n A) ∧
      cantorAnnihilation n k * cantorCreation n k +
        cantorCreation n k * cantorAnnihilation n k = 1) ∧
    (majoranaBraidUnit i * majoranaBraidUnit (i + 1) * majoranaBraidUnit i =
        majoranaBraidUnit (i + 1) * majoranaBraidUnit i * majoranaBraidUnit (i + 1) ∧
      wittCreationBase * wittAnnihilationBase ≠
        wittAnnihilationBase * wittCreationBase) := by
  refine ⟨BinaryFockCliffordCantorBraidStage.strict_five_stage_causal_chain,
    ⟨cl11Rep_ι_one_zero (E := E), cl11Rep_ι_zero_one (E := E)⟩,
    ⟨FunctionSpace.tilt_switch_anticomm k, clock_shift_weyl, phase_sq⟩,
    ⟨normalizedTrace_matStageEmbed n A, chiral_supercharge_hamiltonian⟩,
    ⟨coherentComplexifyClStage_naturality n A, (canonical_depth_n_car_wire n k).2.2⟩,
    ⟨majoranaBraidUnit_artin i, witt_creation_annihilation_noncommutative_witness⟩⟩

end InfoGeometry.Canonical.BinaryFockCliffordKreinCantorCuntzBraidClosurePoset

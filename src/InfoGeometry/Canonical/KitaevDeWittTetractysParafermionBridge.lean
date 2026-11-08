/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevLocalGapOmegaSpectrumPoset
import InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset
import InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset
import InfoGeometry.Parafermion.ParafermionBraidBrownGaussPoset
import InfoGeometry.Parafermion.TetraktysRealCarryMatrix
import InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset
import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron

/-!
# Canonical Bridge: Kitaev Local-Gap $\Omega$-Spectrum, ABS Clifford Mass Dichotomy, Real DeWitt Tetractys Parafermions, and $\mathfrak{sp}(4, \mathbb{R})$ Positive Grassmannian / Amplituhedron

This canonical bridge module unifies the four operator-algebraic, topological-matter, and positive-geometry spines:
1. **Kitaev Local-Gap & $\Omega$-Spectrum Poset ($\mathfrak{KL}_1 \prec \dots \prec \mathfrak{KL}_{11}$)**:
   Square-first vs. truncate-first Peirce collar healing
   $$\Pi_P(-A^2 - \mu_0)\Pi_P - \bigl(-(\Pi_P A \Pi_P)^2 - \mu_0 \Pi_P\bigr) = -N_+ N_-,$$
   4-Majorana open Kitaev chain healing, BDI Pfaffian $\det(A) = \mathrm{Pf}(A)^2$, mod-8
   Fidkowski–Kitaev stack index reduction, and $\zeta_{\text{real}} \in \mathrm{Sp}(4, \mathbb{Z}) \cap \mathrm{O}(4, \mathbb{Z})$.
2. **Atiyah–Bott–Shapiro Clifford Extension, $\mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{16}$, & Klein-Bottle $\mathrm{Mat}_{32}$ Dichotomy ($\mathfrak{KL}_{12} \prec \dots \prec \mathfrak{KL}_{18}$)**:
   Single- vs. two-flavor mass rotor dichotomy, Class DIII Kramers TRS mass blocking,
   $\mathcal{C}\ell(1,1)$ projective Klein four-group $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$,
   and the $\mathcal{A}_{\mathrm{Klein}} \cong \mathrm{Mat}_{32}(K)$ universal square law
   $\mathcal{D}_{\mathrm{Klein}}(D, M)^2 = I_2 \otimes (D^2 - M^2) + \sigma_x \otimes (D M - M D)$.
3. **Real DeWitt Split Tetractys & $i$-Free $\mathbb{Z}_4$ Parafermion Braid Poset ($\mathfrak{DT}_1 \prec \dots \prec \mathfrak{DT}_7$ & $\mathfrak{PB}_1 \prec \dots \prec \mathfrak{PB}_7$)**:
   Single-bit DeWitt Split Tetractys $\{1, S_P, \Phi, J = S_P\Phi\}$ ($S_P^2 = 1, \Phi^2 = 1, J^2 = -1, N_\pm^2 = 0$),
   division-free 2-bit binary-carry 8th root of unity $\zeta_{\text{real}} = P_2 \Phi_2 + (1 - P_2) J_1 \Phi_2$
   ($\zeta_{\text{real}}^2 = J_1, \zeta_{\text{real}}^4 = -1, \zeta_{\text{real}}^8 = +1$), real Brown–Gauss sum
   $1 + \zeta_{\text{real}} + \zeta_{\text{real}}^4 + \zeta_{\text{real}}^9 = 2\zeta_{\text{real}}$ ($c_- = 1$),
   $\mathbb{Z}_4$ parafermion braid unitarity $(2U_{\text{real}})(2U_{\text{real}}^{-1}) = 4$, and the $\mathbb{Z}_4$
   nilpotent super-Grassmannian unipotent gate $(6\mathcal{E}_4(+\eta))(6\mathcal{E}_4(-\eta)) = 36$.
4. **Row 3 & Row 4 of the DeWitt Split Tetractys: $\mathfrak{sl}_2(\mathbb{R})$ Triad, Chevalley–Peirce Nilpotent Ladder, $\mathfrak{sp}(4, \mathbb{R})$ $10 \oplus 6$ Split, $\mathrm{TP}_2$ Positive Grassmannian $\mathrm{Gr}_+(2, 4)$, & Moment-Curve Amplituhedron Positivity ($\mathfrak{TP}_1 \prec \dots \prec \mathfrak{TP}_7$)**:
   Completes the $\mathfrak{sl}_2(\mathbb{R})$ Lie bracket closure and quadratic Casimir $S_P^2 + \Phi^2 - J^2 = 3I$,
   the Chevalley–Peirce raising/lowering ladder $[S_P, N_\pm] = \pm 2N_\pm, [N_+, N_-] = S_P$,
   the Two-Bit Tetractys $1 + 2 + 3 + 4 = 10 = \dim \mathfrak{sp}(4, \mathbb{R})$ and $(3+1)\otimes(3+1) = 10 \oplus 6 = 16$,
   the double-bivector real boost law $(J_1 J_2)^2 = +1$, symplectic commutator closure
   $[\Omega S_1, \Omega S_2] = \Omega(S_1 \Omega S_2 - S_2 \Omega S_1)$, Total Positivity ($\mathrm{TP}_2$) of
   $\mathcal{G}_+(t, s) = \mathcal{E}_+(t)\mathcal{E}_-(s)$, strict Plücker positivity on $\mathrm{Gr}_+(2, 4)$,
   and the 6-factor Vandermonde positivity $\langle Z(t_0) Z(t_1) Z(t_2) Z(t_3) \rangle = \prod_{0 \le i < j \le 3}(t_j - t_i) > 0$.

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- `canonical_kitaev_dewitt_tetractys_finite_matrix_bridge`:
  Simultaneously certifies the finite integer-matrix realizations across $2 \times 2$ (`Matrix (Fin 2) (Fin 2) ℤ`),
  $4 \times 4$ (`Matrix (Fin 4) (Fin 4) ℤ`), $8 \times 8$ (`WeylMat`), and $16 \times 16$ (`Mat16 ℤ`), including
  $\zeta_{\text{real}} \in \mathrm{Sp}(4, \mathbb{Z}) \cap \mathrm{O}(4, \mathbb{Z})$ (`zetaRealMat4ᵀ * zetaRealMat4 = I4`
  and `zetaRealMat4ᵀ * diracMass2 * zetaRealMat4 = diracMass2`).

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `canonical_kitaev_dewitt_tetractys_universal_ring_bridge`:
  In any associative ring `[Ring B]` and commutative ring `[CommRing K]`, unifies the square-first Peirce
  collar healing law, the DeWitt Split Tetractys $\{1, S_P, \Phi, J = S_P\Phi\}$, the 2-bit real 8th root carry
  $\zeta_{\text{real}}^2 = J_1$, the real Brown–Gauss sum and $\mathbb{Z}_4$ braid unitarity in `[Ring B]`,
  the $\eta^4 = 0$ unipotent exponential gate, and the $\mathcal{D}_{\mathrm{Klein}}^2$ mass-gap shield.
- `canonical_tetractys_sp4_positive_grassmannian_amplituhedron_bridge`:
  Unifies the Row 3 $\mathfrak{sl}_2(\mathbb{R})$ Lie triad closure and Casimir $S_P^2 + \Phi^2 - J^2 = 3I$,
  the Row 4 Chevalley–Peirce nilpotent ladder $[S_P, N_\pm] = \pm 2N_\pm, [N_+, N_-] = S_P$ and first-order
  unipotent shear multiplication $(1 + N_+)(1 + N_-) = 1 + N_+ + N_- + N_+ N_-$, the Two-Bit $10 \oplus 6 = 16$
  split and $\mathfrak{sp}(4, \mathbb{R})$ commutator closure, $\mathrm{TP}_2$ unipotent Gaussian positivity,
  strict Plücker positivity on $\mathrm{Gr}_+(2, 4)$, and the 6-factor Vandermonde Amplituhedron positivity.

### BUCKET 3: OPEN CLOSURE DEBT
- None (`0 sorry`, `0 admit`, `0 custom axioms`, `0 structure wrappers`).
-/

namespace InfoGeometry.Canonical.KitaevDeWittTetractysParafermionBridge

open KitaevLocalGapOmegaSpectrumPoset
open InfoGeometry.KitaevLocalGapOmegaSpectrum.KitaevABSCliffordExtensionMassDichotomyPoset
open InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset
open InfoGeometry.Parafermion.ParafermionBraidBrownGaussPoset
open InfoGeometry.Parafermion.TetraktysRealCarryMatrix
open InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine

open scoped Kronecker

universe u

/-- **Theorem 1 (`canonical_kitaev_dewitt_tetractys_finite_matrix_bridge`)**:
Unified finite integer-matrix certification across dimensions $2$, $4$, $8$, and $16$:
1. **Single-Bit $2 \times 2$ Integer DeWitt Tetractys**:
   `dtMatS0 * dtMatPhi0 = dtMatJ0`, `dtMatJ0 * dtMatJ0 = -1`, `dtMatS0 * dtMatJ0 * dtMatS0 = -dtMatJ0`,
   and `(1 + tetraktysJ0) * (1 + tetraktysJ0) = (2 : ℤ) • tetraktysJ0`.
2. **Two-Bit $4 \times 4$ Integer Binary-Carry 8th Root of Unity ($\zeta_{\text{real}} \in \mathrm{Sp}(4, \mathbb{Z}) \cap \mathrm{O}(4, \mathbb{Z})$) & $\mathfrak{sp}(4, \mathbb{Z})$ Real Boost**:
   `realEighthRootCarry dtMatP2 dtMatPhi2 dtMatJ1 = dtMatZetaReal`,
   `dtMatZetaReal * dtMatZetaReal = dtMatJ1`, `(dtMatZetaReal * dtMatZetaReal) * (dtMatZetaReal * dtMatZetaReal) = -1`,
   `dtMatZetaReal * dtMatZetaRealInv = 1`, `(dtMatS1 * dtMatPhi2) * dtMatZetaReal * (dtMatS1 * dtMatPhi2) = dtMatZetaRealInv`,
   `(zetaRealMat4 : KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ).transpose * zetaRealMat4 = KitaevLocalGapOmegaSpectrumPoset.Mat4.I4`,
   `(zetaRealMat4 : KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ).transpose * KitaevLocalGapOmegaSpectrumPoset.Mat4.diracMass2 * zetaRealMat4 = KitaevLocalGapOmegaSpectrumPoset.Mat4.diracMass2`,
   `sp4J1J2 * sp4J1J2 = 1`, and `sp4Omega * sp4CrossBoost + sp4CrossBoost.transpose * sp4Omega = 0`.
3. **Two-Bit $8 \times 8$ Real Tetraktys $\mathbb{Z}_4$ Weyl Pair (`clock4`, `shift4`, `phase4`)**:
   `clock4 ^ 4 = 1`, `shift4 ^ 4 = 1`, `phase4 ^ 2 = -1`, and `clock4 * shift4 = phase4 * shift4 * clock4`.
4. **4-Majorana Open Kitaev Chain Square-First Bulk Healing & BDI Mod-8 Stack Index**:
   `SquareFirstBulkOp (KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2 : KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ) KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA 1 = 0` and
   `KitaevLocalGapOmegaSpectrumPoset.Mat4.bdiStackIndexMod8 (List.replicate 8 (KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA : KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ)) = 0`.
5. **$\mathcal{C}\ell(4,4) \cong \mathrm{Mat}_{16}(\mathbb{Z})$ Grading Anticommutation**:
   `(Mat32.parity16 : Matrix (Fin 16) (Fin 16) ℤ) * Mat32.flip01_16 + Mat32.flip01_16 * Mat32.parity16 = 0`. -/
theorem canonical_kitaev_dewitt_tetractys_finite_matrix_bridge :
    (dtMatS0 * dtMatPhi0 = dtMatJ0 ∧
     dtMatJ0 * dtMatJ0 = -1 ∧
     dtMatS0 * dtMatJ0 * dtMatS0 = -dtMatJ0 ∧
     (1 + tetraktysJ0) * (1 + tetraktysJ0) = (2 : ℤ) • tetraktysJ0) ∧
    (InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset.realEighthRootCarry
       dtMatP2 dtMatPhi2 dtMatJ1 = dtMatZetaReal ∧
     dtMatZetaReal * dtMatZetaReal = dtMatJ1 ∧
     (dtMatZetaReal * dtMatZetaReal) * (dtMatZetaReal * dtMatZetaReal) = -1 ∧
     dtMatZetaReal * dtMatZetaRealInv = 1 ∧
     (dtMatS1 * dtMatPhi2) * dtMatZetaReal * (dtMatS1 * dtMatPhi2) = dtMatZetaRealInv ∧
     (KitaevLocalGapOmegaSpectrumPoset.Mat4.zetaRealMat4 :
        KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ).transpose *
        KitaevLocalGapOmegaSpectrumPoset.Mat4.zetaRealMat4 =
        KitaevLocalGapOmegaSpectrumPoset.Mat4.I4 ∧
     (KitaevLocalGapOmegaSpectrumPoset.Mat4.zetaRealMat4 :
        KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ).transpose *
        KitaevLocalGapOmegaSpectrumPoset.Mat4.diracMass2 *
        KitaevLocalGapOmegaSpectrumPoset.Mat4.zetaRealMat4 =
        KitaevLocalGapOmegaSpectrumPoset.Mat4.diracMass2 ∧
     sp4J1J2 * sp4J1J2 = 1 ∧
     sp4Omega * sp4CrossBoost + sp4CrossBoost.transpose * sp4Omega = 0) ∧
    (clock4 ^ 4 = 1 ∧
     shift4 ^ 4 = 1 ∧
     phase4 ^ 2 = -1 ∧
     clock4 * shift4 = phase4 * shift4 * clock4) ∧
    (SquareFirstBulkOp
       (KitaevLocalGapOmegaSpectrumPoset.Mat4.projCut2 :
         KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ)
       KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA 1 = 0 ∧
     KitaevLocalGapOmegaSpectrumPoset.Mat4.bdiStackIndexMod8
       (List.replicate 8
         (KitaevLocalGapOmegaSpectrumPoset.Mat4.kitaevChainA :
           KitaevLocalGapOmegaSpectrumPoset.Mat4 ℤ)) = 0) ∧
    ((Mat32.parity16 : Matrix (Fin 16) (Fin 16) ℤ) * Mat32.flip01_16 +
       Mat32.flip01_16 * Mat32.parity16 = 0) := by
  have h1 := single_bit_dewitt_tetractys_int_matrix_realization
  have hTet := tetraktys_integer_complex_structure_laws
  have h2 := two_bit_real_eighth_root_carry_int_matrix_realization
  have hSpO :=
    KitaevLocalGapOmegaSpectrumPoset.Mat4.dewitt_tetractys_mat4_zeta8_and_sp4_invariance (K := ℤ)
  have hBoost := double_bivector_real_boost_int_matrix_realization
  have h3 := tetraktys_real_z4_weyl_pair
  have hMaj :=
    KitaevLocalGapOmegaSpectrumPoset.Mat4.open_kitaev_majorana_chain_square_first_healing (K := ℤ)
  have hBdi :=
    KitaevLocalGapOmegaSpectrumPoset.Mat4.bdi_chiral_zero_mode_index_and_mod8_fidkowski_kitaev_reduction
      (K := ℤ) [] [] [] [] 0
  have h16 := Mat32.parity16_anticomm_flip01_16 (K := ℤ)
  exact ⟨⟨h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, hTet.2.2.2.2.2⟩,
    ⟨h2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.2.1,
     hSpO.2.2.1, hSpO.2.2.2,
     hBoost.2.2.2.2.2.2.2.1, hBoost.2.2.2.2.2.2.2.2.1⟩,
    ⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.2.2⟩,
    ⟨hMaj.2.2.2.2.2.2, hBdi.2.2.1.2.2.2.1⟩,
    h16⟩

/-- **Theorem 2 (`canonical_kitaev_dewitt_tetractys_universal_ring_bridge`)**:
In any associative ring `[Ring B]` and any commutative ring `[CommRing K]`:
1. **Kitaev Square-First Local Gap Healing (`[Ring B]`)**:
   `SquareFirstBulkOp P A μ₀ - TruncateFirstBulkOp P A μ₀ = -(KitaevLocalGapOmegaSpectrumPoset.N_plus P A * KitaevLocalGapOmegaSpectrumPoset.N_minus P A)`.
2. **Single-Bit DeWitt Split Tetractys Unification (`[Ring B]`)**:
   When `P * P = P` and `genPhi P W W * genPhi P W W = 1`:
   `invS P * invS P = 1`, `invS P * genPhi P W W = genJ P W W`, `genJ P W W * genJ P W W = -1`,
   `invS P * genJ P W W * invS P = -genJ P W W`, `conePlus P W * conePlus P W = 0`, and
   `coneMinus P W * coneMinus P W = 0`.
3. **Two-Bit Real 8th Root of Unity $\zeta_{\text{real}}$ & Reflection Conjugation (`[Ring B]`)**:
   For `ζ = realEighthRootCarry P₂ Φ₂ J₁` and `ζ_inv = realEighthRootCarryInv P₂ Φ₂ J₁`:
   `ζ * ζ = J₁`, `(ζ * ζ) * (ζ * ζ) = -1`, `ζ * ζ_inv = 1`, `ζ_inv = -J₁ * ζ`, and
   `(S₁ * Φ₂) * ζ * (S₁ * Φ₂) = ζ_inv`.
4. **Real Brown–Gauss Sum & $\mathbb{Z}_4$ Parafermion Braid Unitarity in `[Ring B]`**:
   For `ζ⁴ = -1`, `X⁴ = 1`, and `ζ * X = X * ζ`:
   `1 + ζ + ζ⁴ + ζ⁸ * ζ = ζ + ζ`, `(1 - X * X) * (ζ * X * (1 + X * X)) = 0`, and
   `realBraidZ4Ring ζ X * realBraidZ4InvRing ζ X = 1 + 1 + 1 + 1`.
5. **$\mathbb{Z}_4$-Nilpotent Unipotent Super-Grassmannian Gate & $\mathcal{D}_{\mathrm{Klein}}^2$ Mass-Gap Shield (`[CommRing K]`)**:
   For `η⁴ = 0`, `(1 - η) * (cyclotomicPhi2 η * cyclotomicPhi4 η) = 1` and
   `unipotentExpGate4Pos η * unipotentExpGate4Neg η = 36`; and for any `D16, M16 : Mat16 K`,
   `Mat32.kleinDirac D16 M16 * Mat32.kleinDirac D16 M16 = ((Mat2.I2 : Mat2 K) ⊗ₖ (D16 * D16 - M16 * M16)) + ((Mat2.sigmaX : Mat2 K) ⊗ₖ (D16 * M16 - M16 * D16))`. -/
theorem canonical_kitaev_dewitt_tetractys_universal_ring_bridge
    {B : Type u} [Ring B] {K : Type u} [CommRing K]
    (P A W μ0 P2 Phi2 J1 S1 ζ X : B)
    (hP : P * P = P)
    (hPhi_sq : genPhi P W W * genPhi P W W = 1)
    (hP2 : P2 * P2 = P2)
    (hPhi2_sq : Phi2 * Phi2 = 1)
    (h_swap2 : Phi2 * P2 = (1 - P2) * Phi2)
    (hJ1_sq : J1 * J1 = -1)
    (h_comm_P : J1 * P2 = P2 * J1)
    (h_comm_Phi : J1 * Phi2 = Phi2 * J1)
    (hS1_sq : S1 * S1 = 1)
    (h_S1_P2 : S1 * P2 = P2 * S1)
    (h_S1_Phi2 : S1 * Phi2 = Phi2 * S1)
    (h_S1_J1 : S1 * J1 = -(J1 * S1))
    (hζ4 : ζ * (ζ * (ζ * ζ)) = -1)
    (hX4 : X * (X * (X * X)) = 1)
    (h_comm : ζ * X = X * ζ)
    (η : K) (hη4 : (η * η) * (η * η) = 0)
    (D16 M16 : Mat16 K) :
    (SquareFirstBulkOp P A μ0 - TruncateFirstBulkOp P A μ0 =
       -(KitaevLocalGapOmegaSpectrumPoset.N_plus P A *
         KitaevLocalGapOmegaSpectrumPoset.N_minus P A)) ∧
    (invS P * invS P = 1 ∧
     invS P * genPhi P W W = genJ P W W ∧
     genJ P W W * genJ P W W = -1 ∧
     invS P * genJ P W W * invS P = -genJ P W W ∧
     conePlus P W * conePlus P W = 0 ∧
     coneMinus P W * coneMinus P W = 0) ∧
    (let ζ_r :=
       InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset.realEighthRootCarry
         P2 Phi2 J1
     let ζ_inv :=
       InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset.realEighthRootCarryInv
         P2 Phi2 J1
     ζ_r * ζ_r = J1 ∧
     (ζ_r * ζ_r) * (ζ_r * ζ_r) = -1 ∧
     ζ_r * ζ_inv = 1 ∧
     ζ_inv = -J1 * ζ_r ∧
     (S1 * Phi2) * ζ_r * (S1 * Phi2) = ζ_inv) ∧
    (let ζ4 := ζ * (ζ * (ζ * ζ))
     let ζ8 := ζ4 * ζ4
     1 + ζ + ζ4 + ζ8 * ζ = ζ + ζ ∧
     (1 - X * X) * (ζ * X * (1 + X * X)) = 0 ∧
     realBraidZ4Ring ζ X * realBraidZ4InvRing ζ X = 1 + 1 + 1 + 1) ∧
    ((1 - η) * (cyclotomicPhi2 η * cyclotomicPhi4 η) = 1 ∧
     unipotentExpGate4Pos η * unipotentExpGate4Neg η = 36 ∧
     Mat32.kleinDirac D16 M16 * Mat32.kleinDirac D16 M16 =
       ((Mat2.I2 : Mat2 K) ⊗ₖ (D16 * D16 - M16 * M16)) +
       ((Mat2.sigmaX : Mat2 K) ⊗ₖ (D16 * M16 - M16 * D16))) := by
  have hGap := (square_first_local_bulk_gap_collar_healing P A μ0 hP).1
  have hTet := dewitt_tetractys_peirce_spine_unification P W hP hPhi_sq
  have hZeta :=
    real_binary_carry_eighth_root_of_unity_and_inverse
      P2 Phi2 J1 hP2 hPhi2_sq h_swap2 hJ1_sq h_comm_P h_comm_Phi
  have hConj :=
    InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset.real_eighth_root_carry_reflection_conjugation
      P2 Phi2 J1 S1 hPhi2_sq hS1_sq h_swap2 h_comm_Phi h_S1_P2 h_S1_Phi2 h_S1_J1
  have hBraid :=
    InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset.real_dewitt_brown_gauss_and_z4_braid_unitarity_ring
      ζ X hζ4 hX4 h_comm
  have hGate := (z4_unipotent_exponential_gate_and_cyclotomic_partition_quotient η).2.2.2 hη4
  have hKleinDirac := (Mat32.kl18_klein_dirac_mat32_square_and_gap_shield D16 M16 (0 : K)).2.1
  exact ⟨hGap,
    ⟨hTet.2.1, hTet.2.2.2.1, hTet.2.2.2.2.1, hTet.2.2.2.2.2.1, hTet.2.2.2.2.2.2.2.1, hTet.2.2.2.2.2.2.2.2⟩,
    ⟨hZeta.1, hZeta.2.1, hZeta.2.2.2.1, hZeta.2.2.2.2.2, hConj.2⟩,
    ⟨hBraid.2.1, hBraid.2.2.1, hBraid.2.2.2⟩,
    ⟨hGate.1, hGate.2, hKleinDirac⟩⟩

/-- **Theorem 3 (`canonical_tetractys_sp4_positive_grassmannian_amplituhedron_bridge`)**:
Unifies Row 3 & Row 4 of the DeWitt Split Tetractys ($\mathfrak{TP}_1 \prec \dots \prec \mathfrak{TP}_7$):
1. **Row 3 $\mathfrak{sl}_2(\mathbb{R})$ Lie Triad Closure & Quadratic Casimir $S_P^2 + \Phi^2 - J^2 = 3I$**:
   For $S_P^2 = 1$, $\Phi^2 = 1$, $\Phi S_P = -S_P \Phi$, and $J = S_P \Phi$:
   $[S_P, \Phi] = 2J$, $[S_P, J] = 2\Phi$, $[J, \Phi] = 2S_P$, and $S_P^2 + \Phi^2 - J^2 = 1 + 1 + 1$.
2. **Row 4 Nilpotent Chevalley–Peirce Ladder & Unipotent Shear Factorization**:
   For $P^2 = P$ and $\Phi^2 = 1$:
   $[S_P, N_+] = 2N_+$, $[S_P, N_-] = -2N_-$, $[N_+, N_-] = S_P$, and
   $(1 + N_+)(1 + N_-)(1 - N_-)(1 - N_+) = 1$.
3. **Two-Bit $16 = 10 \oplus 6$ Split, Double-Bivector Real Boost, & $\mathfrak{sp}(4, \mathbb{R})$ Closure**:
   `1 + 2 + 3 + 4 = 10`, `(3 * 3 + 1 * 1) + (3 * 1 + 1 * 3) = 16`, `(J1 * J2) * (J1 * J2) = 1`,
   `Omega * (Omega * S) + (-(S * Omega)) * Omega = 0`, and
   `[Omega * S1, Omega * S2] = Omega * (S1 * Omega * S2 - S2 * Omega * S1)`.
4. **Total Positivity ($\mathrm{TP}_2$) of $\mathcal{G}_+(t, s)$, Homogeneous Grassmannian Projector $\widetilde{P}_+(t, s)$, & $\mathrm{Gr}_+(2, 4)$ Plücker Positivity**:
   `shearPlus t * shearMinus s = gaussianTP2 t s`, `(gaussianTP2 t s).det = 1`,
   `posGrassProj t s * posGrassProj t s = (1 + t * s) • posGrassProj t s`, strict positivity
   of all minors for $0 < a, 0 < b$, and strict positivity of all 6 ordered Plücker minors
   $\Delta_{ij} > 0$ ($0 \le i < j \le 3$) on $\mathrm{Gr}_+(2, 4)$.
5. **6D Klein Quadric Plücker Relation & Ordered Moment-Curve Vandermonde Positivity**:
   `plucker2 Z W 0 1 * plucker2 Z W 2 3 - plucker2 Z W 0 2 * plucker2 Z W 1 3 + plucker2 Z W 0 3 * plucker2 Z W 1 2 = 0`,
   $\langle Z(t_0) Z(t_1) Z(t_2) Z(t_3) \rangle = \prod_{0 \le i < j \le 3}(t_j - t_i)$, and
   $0 < \langle Z(a_0) Z(a_1) Z(a_2) Z(a_3) \rangle$ for $a_0 < a_1 < a_2 < a_3$. -/
theorem canonical_tetractys_sp4_positive_grassmannian_amplituhedron_bridge
    {B : Type u} [Ring B] {K : Type u} [CommRing K]
    (P W S_P Phi J1 J2 Omega S S1 S2 : B)
    (hP : P * P = P)
    (hGenPhi : genPhi P W W * genPhi P W W = 1)
    (hS_sq : S_P * S_P = 1)
    (hPhi_sq : Phi * Phi = 1)
    (h_anti : Phi * S_P = -(S_P * Phi))
    (hJ1_sq : J1 * J1 = -1)
    (hJ2_sq : J2 * J2 = -1)
    (hJ_comm : J1 * J2 = J2 * J1)
    (hOmega_sq : Omega * Omega = -1)
    (t s t0 t1 t2 t3 : K) (Z W4 : Fin 4 → K)
    (a b a0 a1 a2 a3 : ℤ)
    (ha : 0 < a) (hb : 0 < b)
    (h01 : a0 < a1) (h12 : a1 < a2) (h23 : a2 < a3)
    (r1 r2 r3 r4 : ℝ)
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hr3 : 0 < r3) (hr4 : 0 < r4) :
    (let J := S_P * Phi
     S_P * Phi - Phi * S_P = 2 * J ∧
     S_P * J - J * S_P = 2 * Phi ∧
     J * Phi - Phi * J = 2 * S_P ∧
     S_P * S_P + Phi * Phi - J * J = 1 + 1 + 1) ∧
    (comm (invS P) (conePlus P W) = (2 : ℤ) • conePlus P W ∧
     comm (invS P) (coneMinus P W) = -((2 : ℤ) • coneMinus P W) ∧
     comm (conePlus P W) (coneMinus P W) = invS P ∧
     ((1 + conePlus P W) * (1 + coneMinus P W)) *
       ((1 - coneMinus P W) * (1 - conePlus P W)) = 1) ∧
    ((1 + 2 + 3 + 4 = 10 ∧ (3 * 3 + 1 * 1) + (3 * 1 + 1 * 3) = 16) ∧
     (J1 * J2) * (J1 * J2) = 1 ∧
     Omega * (Omega * S) + (-(S * Omega)) * Omega = 0 ∧
     (Omega * S1) * (Omega * S2) - (Omega * S2) * (Omega * S1) =
       Omega * (S1 * Omega * S2 - S2 * Omega * S1)) ∧
    (shearPlus t * shearMinus s = gaussianTP2 t s ∧
     (gaussianTP2 t s).det = 1 ∧
     posGrassProj t s * posGrassProj t s = (1 + t * s) • posGrassProj t s ∧
     0 < gaussianTP2 a b 0 0 ∧
     0 < (gaussianTP2 a b).det ∧
     (∀ i j : Fin 4, i < j →
       0 < gr24Minor (gr24PositiveChart r1 r2 r3 r4) i j)) ∧
    (plucker2 Z W4 0 1 * plucker2 Z W4 2 3 -
       plucker2 Z W4 0 2 * plucker2 Z W4 1 3 +
       plucker2 Z W4 0 3 * plucker2 Z W4 1 2 = 0 ∧
     InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.bracket4
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve t0)
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve t1)
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve t2)
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve t3) =
       (t1 - t0) * (t2 - t0) * (t3 - t0) * (t2 - t1) * (t3 - t1) * (t3 - t2) ∧
     0 < InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.bracket4
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve a0)
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve a1)
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve a2)
       (InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.momentCurve a3)) := by
  have hSl2 := dewitt_triad_sl2_commutator_closure S_P Phi hS_sq hPhi_sq h_anti
  have hCas : S_P * S_P + Phi * Phi - (S_P * Phi) * (S_P * Phi) = 1 + 1 + 1 := by
    rw [hS_sq, hPhi_sq, hSl2.1, sub_neg_eq_add]
  have hChev := dewitt_peirce_chevalley_brackets P W hP hGenPhi
  have hShear := peirce_gaussian_shear_factorization P W W hP
  have hSp4 :=
    InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.tetractys_two_bit_10_plus_6_and_symplectic_lie_closure
      J1 J2 Omega S S1 S2 hJ1_sq hJ2_sq hJ_comm hOmega_sq
  have hTp2 :=
    InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.positive_grassmannian_gaussian_tp2_and_homogeneous_projector
      t s a b ha hb 1 1 zero_lt_one zero_lt_one
  have hGr24 := gr24_positive_chart_plucker_coordinates r1 r2 r3 r4 hr1 hr2 hr3 hr4
  have hKlein := plucker2_satisfies_klein_quadric_relation Z W4
  have hVand :=
    InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.moment_curve_amplituhedron_vandermonde_positivity
      t0 t1 t2 t3 Z W4 Z W4 a0 a1 a2 a3 h01 h12 h23 0 1 2 3
      (by norm_num) (by norm_num) (by norm_num)
  exact ⟨⟨hSl2.2.1, hSl2.2.2.1, hSl2.2.2.2.2.1, hCas⟩,
    ⟨hChev.1, hChev.2.1, hChev.2.2.1, hShear.2.1⟩,
    ⟨⟨hSp4.1, hSp4.2.2.2.1⟩, hSp4.2.2.2.2.1, hSp4.2.2.2.2.2.1, hSp4.2.2.2.2.2.2.1⟩,
    ⟨hTp2.1, hTp2.2.1, hTp2.2.2.1, hTp2.2.2.2.1, hTp2.2.2.2.2.2.2.2.1, hGr24.2.2.2.2.2.2.2⟩,
    ⟨hKlein.1, hVand.1, hVand.2.2.1⟩⟩

/-- The existing Tetractys network chart is the same matrix as the canonical
finite `Gr(2,4)` chart, so its positive-weight points satisfy the canonical
strict maximal-minor predicate. This bridges the two matrix APIs; it does not
assert a map from the symplectic generators to the network weights. -/
theorem tetractysNetworkChart_mem_canonicalInterior
    (t1 t2 t3 t4 : ℝ) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (ht3 : 0 < t3) (ht4 : 0 < t4) :
    InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.gr24PositiveChart
        t1 t2 t3 t4 ∈
      InfoGeometry.Canonical.positiveGrassmannianInterior (k := 2) (n := 4) := by
  have hmatrix :
      InfoGeometry.Parafermion.TetractysSp4PositiveGrassmannianPoset.gr24PositiveChart
          t1 t2 t3 t4 =
        InfoGeometry.Canonical.positiveGr24NetworkMatrix t1 t2 t3 t4 := by
    rfl
  rw [hmatrix]
  exact InfoGeometry.Canonical.positiveGr24NetworkMatrix_mem_interior
    t1 t2 t3 t4 ht1 ht2 ht3 ht4

end InfoGeometry.Canonical.KitaevDeWittTetractysParafermionBridge

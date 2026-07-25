import Mathlib
import InfoGeometry.LogJordanKreinCore
import InfoGeometry.Canonical.SplitCARCurrentSourceAdapter
import InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
# InfoGeometry.Canonical.LogVirasoroExtension

Non-Semisimple Logarithmic Virasoro Representation Extension and Krein Intertwiner.

This module formalizes the non-semisimple extension $V_{\text{log}} = V \times V$ of a Virasoro
representation $V$, constructing the off-diagonal 1-cocycle block structure:

$$\rho_{\text{log}}(x) = \begin{pmatrix} \rho(x) & c(x) \\ 0 & \rho(x) \end{pmatrix}$$

It proves that the zero-mode $L_0^{\text{log}}$ on $V_{\text{log}}$ contains a genuine non-diagonalizable
Jordan cell $L(\Delta) = \begin{pmatrix} \Delta & 1 \\ 0 & \Delta \end{pmatrix}$, satisfying full
Virasoro relations, non-diagonalizability, and Krein pseudo-hermiticity.
-/

namespace InfoGeometry.Canonical.LogVirasoroExtension

open VirasoroProject
open InfoGeometry.LogJordanKreinCore
open InfoGeometry.Canonical.SplitCARCurrentSourceAdapter
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable {A : Type*} [Ring A]

/-- The logarithmic extension carrier space $V_{\text{log}} = V \times V$. -/
abbrev Vlog (V : Type*) := V × V

/-- Upper-triangular block operator on $V \times V$ defined by diagonal operator `T` and off-diagonal operator `C`. -/
def blockOp (T C : Module.End 𝕜 V) : Module.End 𝕜 (V × V) where
  toFun := fun p => ⟨T p.1 + C p.2, T p.2⟩
  map_add' := by
    intro p q
    ext <;> simp [map_add, add_assoc, add_left_comm]
  map_smul' := by
    intro r p
    ext <;> simp [map_smul, smul_add]

/--
**Upper-Triangular Block Commutator Theorem:**
The commutator of two block operators $[(T_1, C_1), (T_2, C_2)]$ equals the block operator with diagonal $[T_1, T_2]$
and off-diagonal $[T_1, C_2] + [C_1, T_2]$.
-/
theorem blockOp_commutator (T1 C1 T2 C2 : Module.End 𝕜 V) :
    (blockOp T1 C1).commutator (blockOp T2 C2) =
      blockOp (T1.commutator T2) (T1.commutator C2 + C1.commutator T2) := by
  ext ⟨u, v⟩
  · simp [blockOp, LinearMap.commutator, sub_eq_iff_eq_add]
    abel
  · simp [blockOp, LinearMap.commutator]

/--
**Virasoro 1-Cocycle Derivation Condition:**
The linear map $c : \mathfrak{vir} \to \operatorname{End}(V)$ is a Lie-algebra 1-cocycle for the representation $\rho$ if
$$c([x, y]) = [\rho(x), c(y)] + [c(x), \rho(y)]$$
-/
def IsVirasoroCocycle
    (ρ : VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 V)
    (c : VirasoroAlgebra 𝕜 →ₗ[𝕜] Module.End 𝕜 V) : Prop :=
  ∀ x y : VirasoroAlgebra 𝕜,
    c ⁅x, y⁆ = (ρ x).commutator (c y) + (c x).commutator (ρ y)

/--
**Logarithmic Extension Representation Constructor:**
Given a Virasoro representation $\rho$ and a 1-cocycle $c$, constructs the non-semisimple Lie-algebra representation
$\rho_{\text{log}} : \mathfrak{vir} \to \operatorname{End}(V \times V)$.
-/
def makeLogVirasoroRepresentation
    (ρ : VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 V)
    (c : VirasoroAlgebra 𝕜 →ₗ[𝕜] Module.End 𝕜 V)
    (hc : IsVirasoroCocycle ρ c) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 (V × V) where
  toFun := fun x => blockOp (ρ x) (c x)
  map_add' := by
    intro x y
    ext <;> simp [blockOp, map_add]
  map_smul' := by
    intro r x
    ext <;> simp [blockOp, map_smul]
  map_lie' := by
    intro x y
    simp only [LieHom.coe_toLinearMap, blockOp_commutator]
    have h1 : (ρ ⁅x, y⁆) = (ρ x).commutator (ρ y) := map_lie ρ x y
    have h2 : c ⁅x, y⁆ = (ρ x).commutator (c y) + (c x).commutator (ρ y) := hc x y
    rw [h1, h2]

/--
**Source-Derived Logarithmic Extension:**
Extends an `AdapterData 𝕜 A V` representation to the logarithmic extension space $V \times V$.
-/
noncomputable def AdapterData.toLogVirasoroExtension
    (D : AdapterData 𝕜 A V)
    (c : VirasoroAlgebra 𝕜 →ₗ[𝕜] Module.End 𝕜 V)
    (hc : IsVirasoroCocycle D.toSugawaraVirasoroRepresentation c) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 (V × V) :=
  makeLogVirasoroRepresentation D.toSugawaraVirasoroRepresentation c hc

/--
**Logarithmic Virasoro Intertwiner Construction:**
Given a primary state $v_0 \neq 0$ with $L_0 v_0 = \Delta v_0$, $c(L_0) v_0 = v_0$, and $[\rho(L_0), c(L_0)] = 0$,
embeds the 2D non-diagonalizable Jordan cell $L(\Delta)$ into $V \times V$.
-/
noncomputable def makeLogIntertwiner
    (ρ : VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 V)
    (c : VirasoroAlgebra 𝕜 →ₗ[𝕜] Module.End 𝕜 V)
    (hc : IsVirasoroCocycle ρ c)
    (Δ : 𝕜) (v0 : V) (hv0 : v0 ≠ 0)
    (hL0 : ρ (VirasoroAlgebra.lgen 𝕜 0) v0 = Δ • v0)
    (hc0 : c (VirasoroAlgebra.lgen 𝕜 0) v0 = v0)
    (hcomm0 : (ρ (VirasoroAlgebra.lgen 𝕜 0)).commutator (c (VirasoroAlgebra.lgen 𝕜 0)) = 0) :
    LogVirasoroIntertwiner (V × V) (makeLogVirasoroRepresentation ρ c hc (VirasoroAlgebra.lgen 𝕜 0)) Δ where
  ι := {
    toFun := fun v => (v 0 • v0 + v 1 • c (VirasoroAlgebra.lgen 𝕜 0) v0, v 1 • v0)
    map_add' := by
      intro x y
      ext <;> simp [add_smul, add_assoc, add_left_comm]
    map_smul' := by
      intro r x
      ext <;> simp [smul_add, mul_smul]
  }
  injective := by
    intro x y hxy
    have hsnd : x 1 • v0 = y 1 • v0 := congr_arg Prod.snd hxy
    have hy1 : x 1 = y 1 := by
      have hdiff : (x 1 - y 1) • v0 = 0 := by
        rw [sub_smul, hsnd, sub_self]
      cases smul_eq_zero.mp hdiff with
      | inl h => exact sub_eq_zero.mp h
      | inr h => contradiction
    have hfst : x 0 • v0 + x 1 • c (VirasoroAlgebra.lgen 𝕜 0) v0 = y 0 • v0 + y 1 • c (VirasoroAlgebra.lgen 𝕜 0) v0 := congr_arg Prod.fst hxy
    rw [hy1] at hfst
    have hy0 : x 0 = y 0 := by
      have hdiff : (x 0 - y 0) • v0 = 0 := by
        have hsub := congr_arg (fun z => z - y 1 • c (VirasoroAlgebra.lgen 𝕜 0) v0) hfst
        simp only [add_sub_cancel_right] at hsub
        rw [sub_smul, hsub, sub_self]
      cases smul_eq_zero.mp hdiff with
      | inl h => exact sub_eq_zero.mp h
      | inr h => contradiction
    ext i
    fin_cases i
    · exact hy0
    · exact hy1
  intertwines := by
    ext w
    have h_comm_apply : ρ (VirasoroAlgebra.lgen 𝕜 0) (c (VirasoroAlgebra.lgen 𝕜 0) v0) = Δ • c (VirasoroAlgebra.lgen 𝕜 0) v0 := by
      have h1 : (ρ (VirasoroAlgebra.lgen 𝕜 0)).commutator (c (VirasoroAlgebra.lgen 𝕜 0)) v0 = 0 := by rw [hcomm0, LinearMap.zero_apply]
      have h1' : ρ (VirasoroAlgebra.lgen 𝕜 0) (c (VirasoroAlgebra.lgen 𝕜 0) v0) - c (VirasoroAlgebra.lgen 𝕜 0) (ρ (VirasoroAlgebra.lgen 𝕜 0) v0) = 0 := by
        simpa [LinearMap.commutator] using h1
      rw [hL0] at h1'
      rw [map_smul] at h1'
      exact sub_eq_zero.mp h1'
    refine Prod.ext ?_ ?_
    · simp [makeLogVirasoroRepresentation, blockOp, jordanCell, Matrix.toLin', Matrix.mulVec, Fin.sum_univ_two, hL0, hc0, h_comm_apply, map_add, map_smul, smul_add, add_assoc, add_left_comm, mul_smul]
      abel
    · simp [makeLogVirasoroRepresentation, blockOp, jordanCell, Matrix.toLin', Matrix.mulVec, Fin.sum_univ_two, hL0, hc0, map_add, map_smul, smul_add, add_assoc, add_left_comm, mul_smul]

end InfoGeometry.Canonical.LogVirasoroExtension

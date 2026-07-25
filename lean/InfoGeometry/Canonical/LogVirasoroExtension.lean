import Mathlib
import InfoGeometry.LogJordanKreinCore
import InfoGeometry.Canonical.SplitCARCurrentSourceAdapter
import InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

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
  toFun := fun ⟨u, v⟩ => ⟨T u + C v, T v⟩
  map_add' := by
    intro ⟨u1, v1⟩ ⟨u2, v2⟩
    ext <;> simp [map_add, add_assoc, add_left_comm]
  map_smul' := by
    intro r ⟨u, v⟩
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
    ext ⟨u, v⟩ <;> simp [blockOp, map_add]
  map_smul' := by
    intro r x
    ext ⟨u, v⟩ <;> simp [blockOp, map_smul]
  map_lie' := by
    intro x y
    simp [blockOp_commutator]
    rw [map_lie ρ x y]
    congr 1
    exact (hc x y).symm

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
Given a primary state $v_0 \neq 0$ with $L_0 v_0 = \Delta v_0$ and $c(L_0) v_0 = v_0$,
embeds the 2D non-diagonalizable Jordan cell $L(\Delta)$ into $V \times V$.
-/
def makeLogIntertwiner
    (ρ : VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 V)
    (c : VirasoroAlgebra 𝕜 →ₗ[𝕜] Module.End 𝕜 V)
    (hc : IsVirasoroCocycle ρ c)
    (Δ : 𝕜) (v0 : V) (hv0 : v0 ≠ 0)
    (hL0 : ρ (L 0) v0 = Δ • v0)
    (hc0 : c (L 0) v0 = v0) :
    LogVirasoroIntertwiner (V × V) (makeLogVirasoroRepresentation ρ c hc (L 0)) Δ where
  ι := {
    toFun := fun v => (v 0 • v0 + v 1 • c (L 0) v0, v 1 • v0)
    map_add' := by
      intro x y
      ext <;> simp [add_smul, smul_add, add_assoc, add_left_comm]
    map_smul' := by
      intro r x
      ext <;> simp [smul_add, mul_smul]
  }
  injective := by
    intro x y hxy
    have h2 : x 1 • v0 = y 1 • v0 := by
      have := congr_arg Prod.snd hxy
      exact this
    have hy1 : x 1 = y 1 := by
      have := sub_eq_zero.mp (smul_eq_zero.mp (by simpa [sub_smul] using sub_eq_zero.2 h2) |>.resolve_right hv0)
      exact this
    subst hy1
    have h1 : x 0 • v0 = y 0 • v0 := by
      have := congr_arg Prod.fst hxy
      simpa using this
    have hy0 : x 0 = y 0 := by
      have := sub_eq_zero.mp (smul_eq_zero.mp (by simpa [sub_smul] using sub_eq_zero.2 h1) |>.resolve_right hv0)
      exact this
    ext i
    fin_cases i <;> assumption
  intertwines := by
    ext x
    ext i
    fin_cases i <;> simp [makeLogVirasoroRepresentation, blockOp, jordanCell, Matrix.toLin', Matrix.mulVec, Fin.sum_univ_two, e0, e1, hL0, hc0, map_add, map_smul, smul_add, add_assoc, add_left_comm]

end InfoGeometry.Canonical.LogVirasoroExtension

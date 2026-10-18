/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Zorn Split-Octonion Para-Kähler Phase Space, $\operatorname{Cl}(3,3)$ Null Cone, and Metriplectic Product

This module formalizes the 6-dimensional purely imaginary para-Kähler phase space
`ParaKahlerVec R` ($V = T^+ \oplus T^- \cong R^3 \oplus (R^3)^*$) inside the 8-dimensional
Zorn vector-matrix split-octonion algebra `ZornSplitOctonion R` imported from
`InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge`:

1. **Zorn Split-Octonion Algebra & 3D Cross-Product Identities**:
   - Reuses `ZornSplitOctonion R`, `canonicalZornSplitOctonion`, `vec3Dot`, `vec3Cross`,
     `zornMul`, and `zornNorm` ($N(x) = a b - \langle u, v \rangle$) from
     `ZornSplitOctonionFin8Bridge`, and defines `zornOne`, `zornParaGrading`, `zornAdd`,
     `zornSub`, `zornSmul`, and `zornCommutator`, together with `vec3Cross_self` and
     `vec3Cross_anticomm`.

2. **6D Para-Kähler Phase Space, Fock Spinor Bridge & $\operatorname{Cl}(3,3)$ Split Quadratic Form**:
   - Defines `ParaKahlerVec R`, `embedVec`, `primalSheet`, and `dualSheet`, and proves
     `fin8ToZorn_gPlus1_vac_eq_embedVec_primalSheet` and
     `fin8ToZorn_gPlus2Hodge_vac_eq_embedVec_dualSheet` identifying the vacuum Fock columns
     of `gPlus1 k` and `gPlus2Hodge k` under `fin8ToZorn` with the embedded primal and dual
     polarization sheets $T^+$ and $T^-$.
   - Split quadratic form $Q_{3,3}(u, v) = \langle u, v \rangle$ diagonalizing under
     the Majorana substitution $(u, v) = (p + q, p - q)$ to $\|p\|^2 - \|q\|^2$.
   - Para-complex involution $K(u, v) = (u, -v)$ with $K^2 = \operatorname{id}$ and
     eigenspaces $T^+ = \operatorname{primalSheet}$ ($+1$) and
     $T^- = \operatorname{dualSheet}$ ($-1$, certified on the embedded carrier by
     `embedVec_paraComplexK_dualSheet`).
   - Symmetric neutral metric $g(z_1, z_2) = \langle u_1, v_2 \rangle + \langle v_1, u_2 \rangle$
     and symplectic form $\omega(z_1, z_2) = \langle u_1, v_2 \rangle - \langle v_1, u_2 \rangle
     = g(K z_1, z_2)$.

3. **Clifford–Zorn Anticommutator, Isotropic Null Cone & Isotropic Sheets**:
   - Anticommutator identity $z_1 z_2 + z_2 z_1 = g(z_1, z_2) \cdot 1_{\text{Zorn}}$ and
     square identity $z^2 = -N(z) \cdot 1_{\text{Zorn}}$.
   - Equivalence of the $\operatorname{Cl}(3,3)$ null-cone condition $N(z) = 0$, nilpotency
     $z^2 = 0$, and orthogonality $\langle u, v \rangle = 0$.
   - Proof that both polarization sheets $T^+$ and $T^-$ lie in the null cone and the
     restrictions of $g$ and $\omega$ to each sheet vanish. Maximality is not asserted
     over the arbitrary commutative-ring carrier used here.

4. **Zorn Commutator Decomposition & Full Metriplectic Product over `ℝ`**:
   - Commutator identity $[z_1, z_2] = \omega(z_1, z_2) I_{\text{para}} + 2 (z_1 \times_H z_2)$
     separating the scalar symplectic pairing along $I_{\text{para}} = \operatorname{diag}(1, -1)$
     from the 3D Hodge cross-product terms $(-v_1 \times v_2, u_1 \times u_2)$.
   - Full metriplectic product decomposition over `ℝ`:
     $$z_1 z_2 = \tfrac{1}{2} g(z_1, z_2) 1_{\text{Zorn}}
       + \tfrac{1}{2} \omega(z_1, z_2) I_{\text{para}} + z_1 \times_H z_2.$$

5. **Para-Kähler Grading Action, Lagrange Identity & Chiral Volume Associator**:
   - Commutator action $[I_{\text{para}}, z] = 2 K(z)$ on embedded phase-space vectors
     (`zorn_paraGrading_commutator_embedVec`) and anticommutation $\{I_{\text{para}}, z\} = 0$
     (`zorn_paraGrading_anticommutator_embedVec`).
   - Lagrange–Binet–Cauchy coordinate identity
     $g(z_1, z_2)^2 - \omega(z_1, z_2)^2 + 4 \langle u_1 \times u_2, v_1 \times v_2 \rangle
     = g(z_1, z_1) g(z_2, z_2)$ (`paraKahler_lagrange_norm_composition`), together with the
     self-metric and Zorn-norm identities for `hodgeCrossVec z₁ z₂`
     (`paraKahlerMetric_hodgeCrossVec_self`, `zornNorm_embedVec_hodgeCrossVec`) and the direct
     synthesis with `ZornSplitOctonionFin8Bridge.zornNorm_mul`
     (`zornNorm_embedVec_mul_eq_metriplectic_lagrange`,
     `paraKahler_lagrange_eq_four_mul_zornNorm_mul`).
   - Left and right primal triple-product projections onto the Peirce idempotents $e_1, e_0$
     scaled by $\det(u_1, u_2, u_3)$ (`zorn_primal_triple_left_eq_volume_smul_e1`,
     `zorn_primal_triple_right_eq_volume_smul_e0`), the sum of these two bracketings as a
     scalar multiple of $1_{\text{Zorn}}$ (`zorn_primal_triple_bracketing_sum_eq_volume_smul_one`),
     and chiral volume associator
     identity $[u_1, u_2, u_3] = -\det(u_1, u_2, u_3) I_{\text{para}}$
     (`zorn_primal_triple_associator_eq_volume_paraGrading`).
   - Chiral lightcone null-ray scaling (`paraKahlerScale`, `paraKahlerMetric_scale`,
     `symplecticForm_scale`, `isOnNullCone_scale`, `hodgeCrossVec_scale_self`), unipotent
     shear transport along $T^+ / T^-$ (`paraNilpotentMinus`, `paraNilpotentMinus_sq_zero`,
     `paraUnipotentShear`, `paraUnipotentShear_zero`, `paraUnipotentShear_add`,
     `paraUnipotentShear_neg_cancel`, `paraKahlerMetric_paraUnipotentShear_self`,
     `isOnNullCone_paraUnipotentShear_dualSheet`, `symplecticForm_primal_paraUnipotentShear`),
     metric-skew nilpotent flow and its `Module` / `LinearMap` / `LinearEquiv` realization
     (`paraSkewNilpotent`, `paraSkewNilpotent_sq_zero`, `paraKahlerMetric_paraSkewNilpotent_skew`,
     `paraKahlerMetric_paraSkewNilpotent_self_right`,
     `paraKahlerMetric_paraSkewNilpotent_self_left`,
     `paraKahlerMetric_paraSkewNilpotent_quad_zero`,
     `paraSkewNilpotentLinear`, `paraSkewNilpotentLinear_comp_self`,
     `paraSkewUnipotentFlow`, `paraSkewUnipotentFlow_zero`, `paraSkewUnipotentFlow_add`,
     `paraSkewUnipotentFlow_neg_cancel`, `paraSkewUnipotentFlow_cancel_neg`,
     `paraSkewUnipotentFlowEquiv`, `paraSkewUnipotentFlowLinearMap`,
     `paraSkewUnipotentFlowLinearEquiv`, `paraKahlerMetric_paraSkewUnipotentFlow_expand`,
     `paraKahlerMetric_paraSkewUnipotentFlow_invariant`,
     `paraKahlerMetric_paraSkewUnipotentFlowLinearEquiv_invariant`,
     `isOnNullCone_paraSkewUnipotentFlow_iff`), and the null-cone metriplectic reduction
     (`nullCone_metriplectic_eq_two_mul_hodgeCrossVec_self`,
     `nullCone_paraSkewUnipotentFlow_metriplectic_hodge_balance`).

6. **Pointwise Clifford Relations & Peirce Coordinate Sectors on $\mathbb{O}_s$**:
   Moved to the dedicated owner `InfoGeometry.Canonical.SplitOctonionClifford33Soldering`.
   The Cl(3,3) anticommutator laws `zorn_left_clifford33_soldering` and
   `zorn_right_clifford33_soldering`, the four Peirce coordinate evaluations
   `peirceKetBra00_eq` / `peirceKetBra01_eq` / `peirceKetBra10_eq` / `peirceKetBra11_eq`, and
   `peirce_ketbra_completeness` are proved there, together with the bilinearity and unit
   lemmas they rest on, the `Fin 8 → ℝ` `LinearMap` and `Matrix (Fin 8) (Fin 8) ℝ`
   realisation of the left- and right-multiplication operators, and the corresponding
   operator- and matrix-level Cl(3,3) laws. They are not duplicated here, so that there is a
   single owner for the soldering law and no short-name ambiguity between two namespaces.

## Scope Note

The Cl(3,3) anticommutator laws of `SplitOctonionClifford33Soldering` are not a proof of an
algebra isomorphism from a Clifford algebra to `Matrix (Fin 8) (Fin 8) ℝ`; `fin8ZornEquiv`
is only a type equivalence, and that module explicitly disclaims any Cl(3,3) isomorphism
and any identification with Jordan–Wigner Majorana Kronecker strings.

The non-Fock algebraic identities in Sections 1–5 and 7 are proved over an arbitrary
commutative ring `CommRing R`. The finite Fock spinor bridge theorems
`fin8ToZorn_gPlus1_vac_eq_embedVec_primalSheet` and
`fin8ToZorn_gPlus2Hodge_vac_eq_embedVec_dualSheet` are certified over `ℤ`. The explicit
nonzero-associator witness and the resulting obstruction to injective multiplicative maps
into associative semigroups are stated over `ℝ`. The half-integer metriplectic synthesis
`zornMul_embedVec_metriplectic_decomp` in Section 6 is also stated over `ℝ`, where `1 / 2`
is available.
-/

namespace InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone

open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge

/-!
## Section 1: Zorn Split-Octonion Linear Operations & 3D Cross-Product Identities
-/

section RingOperations

variable {R : Type*} [CommRing R]

/-- Multiplicative identity $\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ of the Zorn algebra. -/
def zornOne : ZornSplitOctonion R :=
  ⟨1, fun _ => 0, fun _ => 0, 1⟩

/-- Diagonal para-complex grading element $I_{\text{para}} = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def zornParaGrading : ZornSplitOctonion R :=
  ⟨1, fun _ => 0, fun _ => 0, -1⟩

/-- Componentwise addition on `ZornSplitOctonion R`. -/
def zornAdd (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨x.a + y.a, fun k => x.u k + y.u k, fun k => x.v k + y.v k, x.b + y.b⟩

/-- Componentwise subtraction on `ZornSplitOctonion R`. -/
def zornSub (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨x.a - y.a, fun k => x.u k - y.u k, fun k => x.v k - y.v k, x.b - y.b⟩

/-- Scalar multiplication on `ZornSplitOctonion R`. -/
def zornSmul (c : R) (x : ZornSplitOctonion R) : ZornSplitOctonion R :=
  ⟨c * x.a, fun k => c * x.u k, fun k => c * x.v k, c * x.b⟩

/-- Algebra commutator $[x, y] = x y - y x$ on `ZornSplitOctonion R`. -/
def zornCommutator (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  zornSub (zornMul x y) (zornMul y x)

/-- The 3D cross product of any vector with itself vanishes. -/
theorem vec3Cross_self (u : Fin 3 → R) : vec3Cross u u = fun _ => 0 := by
  funext k
  fin_cases k <;> {
    dsimp [vec3Cross]
    ring
  }

/-- The 3D cross product is skew-symmetric: $(u \times v)_k + (v \times u)_k = 0$. -/
theorem vec3Cross_anticomm (u v : Fin 3 → R) (k : Fin 3) :
    vec3Cross u v k + vec3Cross v u k = 0 := by
  fin_cases k <;> {
    dsimp [vec3Cross]
    ring
  }

/-!
## Section 2: The 6D Para-Kähler Phase Space $V = T^+ \oplus T^-$ Inside `ZornSplitOctonion R`
-/

/-- A vector $(u, v) \in T^+ \oplus T^-$ in the 6-dimensional para-Kähler phase space. -/
@[ext]
structure ParaKahlerVec (R : Type*) where
  u : Fin 3 → R
  v : Fin 3 → R

/-- Closed integer witness for `ParaKahlerVec`. -/
def canonicalParaKahlerVec : ParaKahlerVec ℤ :=
  ⟨![1, 0, 0], ![0, 1, 0]⟩

instance {S : Type*} [Zero S] : Inhabited (ParaKahlerVec S) :=
  ⟨⟨fun _ => 0, fun _ => 0⟩⟩

/-- Embedding of the 6D phase space into the off-diagonal subspace of `ZornSplitOctonion R`. -/
def embedVec (z : ParaKahlerVec R) : ZornSplitOctonion R :=
  ⟨0, z.u, z.v, 0⟩

/-- Primal polarization sheet inclusion $T^+ \hookrightarrow V$, $u \mapsto (u, 0)$. -/
def primalSheet (u : Fin 3 → R) : ParaKahlerVec R :=
  ⟨u, fun _ => 0⟩

/-- Dual polarization sheet inclusion $T^- \hookrightarrow V$, $v \mapsto (0, v)$. -/
def dualSheet (v : Fin 3 → R) : ParaKahlerVec R :=
  ⟨fun _ => 0, v⟩

/-- **Fock Spinor Bridge for the Primal Sheet $T^+$**:
Mapping the vacuum column of the grade-$+1$ Fock creation matrix `gPlus1 k` into
`ZornSplitOctonion ℤ` via `fin8ToZorn` yields the embedded primal sheet basis vector. -/
theorem fin8ToZorn_gPlus1_vac_eq_embedVec_primalSheet (k : Fin 3) :
    fin8ToZorn (fun r => gPlus1 k r 0) =
      embedVec (primalSheet (fun j => if j = k then (1 : ℤ) else 0)) := by
  ext j
  · revert k
    decide
  · revert k j
    decide
  · revert k j
    decide
  · revert k
    decide

/-- **Fock Spinor Bridge for the Dual Sheet $T^-$**:
Mapping the vacuum column of the cyclic Hodge grade-$+2$ bivector creation matrix
`gPlus2Hodge k` into `ZornSplitOctonion ℤ` via `fin8ToZorn` yields the embedded dual
sheet basis vector. -/
theorem fin8ToZorn_gPlus2Hodge_vac_eq_embedVec_dualSheet (k : Fin 3) :
    fin8ToZorn (fun r => gPlus2Hodge k r 0) =
      embedVec (dualSheet (fun j => if j = k then (1 : ℤ) else 0)) := by
  ext j
  · revert k
    decide
  · revert k j
    decide
  · revert k j
    decide
  · revert k
    decide

/-- The split-signature $\operatorname{Cl}(3,3)$ quadratic form $Q_{3,3}(u, v) = \langle u, v \rangle$. -/
def cl33QuadraticForm (z : ParaKahlerVec R) : R :=
  vec3Dot z.u z.v

/-- The neutral-signature $(3,3)$ para-Kähler metric $g(z_1, z_2) = \langle u_1, v_2 \rangle + \langle v_1, u_2 \rangle$. -/
def paraKahlerMetric (z₁ z₂ : ParaKahlerVec R) : R :=
  vec3Dot z₁.u z₂.v + vec3Dot z₁.v z₂.u

/-- The canonical symplectic 2-form $\omega(z_1, z_2) = \langle u_1, v_2 \rangle - \langle v_1, u_2 \rangle$. -/
def symplecticForm (z₁ z₂ : ParaKahlerVec R) : R :=
  vec3Dot z₁.u z₂.v - vec3Dot z₁.v z₂.u

/-- The para-complex structure $K(u, v) = (u, -v)$ with eigenvalues $\pm 1$ on $T^\pm$. -/
def paraComplexK (z : ParaKahlerVec R) : ParaKahlerVec R :=
  ⟨z.u, fun k => -z.v k⟩

/-- A phase-space vector $z = (u, v)$ lies on the $\operatorname{Cl}(3,3)$ isotropic null cone when
its embedded Zorn norm vanishes. -/
def IsOnNullCone (z : ParaKahlerVec R) : Prop :=
  zornNorm (embedVec z) = 0

/-- The off-diagonal Hodge cross-product pairing $z_1 \times_H z_2 = (-v_1 \times v_2, u_1 \times u_2)$. -/
def hodgeCrossVec (z₁ z₂ : ParaKahlerVec R) : ParaKahlerVec R :=
  ⟨fun k => -vec3Cross z₁.v z₂.v k, vec3Cross z₁.u z₂.u⟩

/-!
## Section 3: Core Para-Kähler & $\operatorname{Cl}(3,3)$ Clifford–Zorn Theorems
-/

/-- Under the Majorana change of basis $(u, v) = (p + q, p - q)$, the $\operatorname{Cl}(3,3)$
quadratic form diagonalizes into the $(3,3)$ signature difference $\|p\|^2 - \|q\|^2$. -/
theorem cl33QuadraticForm_majorana_split (p q : Fin 3 → R) :
    cl33QuadraticForm ⟨fun k => p k + q k, fun k => p k - q k⟩ =
      vec3Dot p p - vec3Dot q q := by
  dsimp [cl33QuadraticForm, vec3Dot]
  ring

/-- The para-complex operator $K$ is an involution: $K(K(z)) = z$. -/
theorem paraComplexK_sq_id (z : ParaKahlerVec R) :
    paraComplexK (paraComplexK z) = z := by
  ext k
  · rfl
  · dsimp [paraComplexK]
    ring

/-- Primal sheet vectors are $+1$ eigenvectors of $K$. -/
theorem paraComplexK_primalSheet (u : Fin 3 → R) :
    paraComplexK (primalSheet u) = primalSheet u := by
  ext k
  · rfl
  · dsimp [paraComplexK, primalSheet]
    ring

/-- Dual sheet vectors are $-1$ eigenvectors of $K$. -/
theorem paraComplexK_dualSheet (v : Fin 3 → R) :
    paraComplexK (dualSheet v) = ⟨fun _ => 0, fun k => -v k⟩ := by
  ext k <;> rfl

/-- On the embedded Zorn carrier, `paraComplexK` acts on the dual sheet $T^-$ as scalar
multiplication by $-1$. -/
theorem embedVec_paraComplexK_dualSheet (v : Fin 3 → R) :
    embedVec (paraComplexK (dualSheet v)) = zornSmul (-1 : R) (embedVec (dualSheet v)) := by
  ext k
  · dsimp [embedVec, paraComplexK, dualSheet, zornSmul]
    ring
  · fin_cases k <;> {
      dsimp [embedVec, paraComplexK, dualSheet, zornSmul]
      ring
    }
  · fin_cases k <;> {
      dsimp [embedVec, paraComplexK, dualSheet, zornSmul]
      ring
    }
  · dsimp [embedVec, paraComplexK, dualSheet, zornSmul]
    ring

/-- The para-Kähler metric $g$ is symmetric. -/
theorem paraKahlerMetric_symm (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric z₁ z₂ = paraKahlerMetric z₂ z₁ := by
  dsimp [paraKahlerMetric, vec3Dot]
  ring

/-- The canonical symplectic form $\omega$ is skew-symmetric. -/
theorem symplecticForm_skew (z₁ z₂ : ParaKahlerVec R) :
    symplecticForm z₁ z₂ = -symplecticForm z₂ z₁ := by
  dsimp [symplecticForm, vec3Dot]
  ring

/-- The para-Kähler metric is anti-invariant under $K$: $g(K z_1, K z_2) = -g(z_1, z_2)$. -/
theorem paraKahlerMetric_K_antiInvariant (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraComplexK z₁) (paraComplexK z₂) = -paraKahlerMetric z₁ z₂ := by
  dsimp [paraKahlerMetric, paraComplexK, vec3Dot]
  ring

/-- Compatibility of $(g, K, \omega)$: $\omega(z_1, z_2) = g(K z_1, z_2)$. -/
theorem symplecticForm_eq_metric_K (z₁ z₂ : ParaKahlerVec R) :
    symplecticForm z₁ z₂ = paraKahlerMetric (paraComplexK z₁) z₂ := by
  dsimp [symplecticForm, paraKahlerMetric, paraComplexK, vec3Dot]
  ring

/-- **Clifford–Zorn Anticommutator Identity**:
In `ZornSplitOctonion R`, the anticommutator of two embedded phase-space vectors $z_1, z_2$
is scalar multiplication of `zornOne` by the para-Kähler metric $g(z_1, z_2)$, while the
3D cross-product terms cancel by skew-symmetry. -/
theorem zorn_anticommutator_eq_paraKahlerMetric_smul_one (z₁ z₂ : ParaKahlerVec R) :
    zornAdd (zornMul (embedVec z₁) (embedVec z₂)) (zornMul (embedVec z₂) (embedVec z₁)) =
      zornSmul (paraKahlerMetric z₁ z₂) zornOne := by
  ext k
  · dsimp [zornAdd, zornMul, embedVec, zornSmul, zornOne, paraKahlerMetric, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornAdd, zornMul, embedVec, zornSmul, zornOne, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornAdd, zornMul, embedVec, zornSmul, zornOne, vec3Cross]
      ring
    }
  · dsimp [zornAdd, zornMul, embedVec, zornSmul, zornOne, paraKahlerMetric, vec3Dot]
    ring

/-- The Zorn square of an embedded phase-space vector $z$ equals $-N(z) \cdot 1_{\text{Zorn}}$. -/
theorem zorn_vec_sq_eq_neg_norm_smul_one (z : ParaKahlerVec R) :
    zornMul (embedVec z) (embedVec z) = zornSmul (-zornNorm (embedVec z)) zornOne := by
  ext k
  · dsimp [zornMul, embedVec, zornSmul, zornOne, zornNorm, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, zornSmul, zornOne, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, zornSmul, zornOne, vec3Cross]
      ring
    }
  · dsimp [zornMul, embedVec, zornSmul, zornOne, zornNorm, vec3Dot]
    ring

/-!
## Section 4: The $\operatorname{Cl}(3,3)$ Isotropic Null Cone & Isotropic Sheets $T^+, T^-$
-/

/-- The Zorn norm of an embedded vector $z = (u, v)$ is $-\langle u, v \rangle$. -/
theorem zornNorm_embedVec (z : ParaKahlerVec R) :
    zornNorm (embedVec z) = -vec3Dot z.u z.v := by
  dsimp [zornNorm, embedVec]
  ring

/-- Scalar multiplication of `zornOne` by `0` yields the zero split-octonion. -/
theorem zornSmul_zero_zornOne :
    zornSmul (0 : R) (zornOne : ZornSplitOctonion R) = ⟨0, fun _ => 0, fun _ => 0, 0⟩ := by
  ext k <;> {
    dsimp [zornSmul, zornOne]
    ring
  }

/-- A phase-space vector $z$ lies on the null cone if and only if $\langle u, v \rangle = 0$. -/
theorem isOnNullCone_iff_vec3Dot_zero (z : ParaKahlerVec R) :
    IsOnNullCone z ↔ vec3Dot z.u z.v = 0 := by
  dsimp [IsOnNullCone]
  rw [zornNorm_embedVec, neg_eq_zero]

/-- A phase-space vector $z$ lies on the null cone if and only if its Zorn square vanishes. -/
theorem isOnNullCone_iff_zorn_sq_zero (z : ParaKahlerVec R) :
    IsOnNullCone z ↔
      zornMul (embedVec z) (embedVec z) = ⟨0, fun _ => 0, fun _ => 0, 0⟩ := by
  rw [isOnNullCone_iff_vec3Dot_zero, zorn_vec_sq_eq_neg_norm_smul_one,
    zornNorm_embedVec, neg_neg]
  constructor
  · intro h
    rw [h]
    exact zornSmul_zero_zornOne
  · intro h
    have ha := congrArg ZornSplitOctonion.a h
    dsimp [zornSmul, zornOne] at ha
    rw [mul_one] at ha
    exact ha

/-- Every primal sheet vector $(u, 0) \in T^+$ lies on the $\operatorname{Cl}(3,3)$ null cone. -/
theorem primalSheet_isOnNullCone (u : Fin 3 → R) :
    IsOnNullCone (primalSheet u) := by
  rw [isOnNullCone_iff_vec3Dot_zero]
  dsimp [primalSheet, vec3Dot]
  ring

/-- The primal sheet $T^+$ is $g$-isotropic: $g((u_1, 0), (u_2, 0)) = 0$. -/
theorem primalSheet_paraKahlerMetric_zero (u₁ u₂ : Fin 3 → R) :
    paraKahlerMetric (primalSheet u₁) (primalSheet u₂) = 0 := by
  dsimp [paraKahlerMetric, primalSheet, vec3Dot]
  ring

/-- The restriction of $\omega$ to the primal sheet vanishes:
$\omega((u_1, 0), (u_2, 0)) = 0$. Maximality is not claimed here. -/
theorem primalSheet_symplecticForm_zero (u₁ u₂ : Fin 3 → R) :
    symplecticForm (primalSheet u₁) (primalSheet u₂) = 0 := by
  dsimp [symplecticForm, primalSheet, vec3Dot]
  ring

/-- Every dual sheet vector $(0, v) \in T^-$ lies on the $\operatorname{Cl}(3,3)$ null cone. -/
theorem dualSheet_isOnNullCone (v : Fin 3 → R) :
    IsOnNullCone (dualSheet v) := by
  rw [isOnNullCone_iff_vec3Dot_zero]
  dsimp [dualSheet, vec3Dot]
  ring

/-- The dual sheet $T^-$ is $g$-isotropic: $g((0, v_1), (0, v_2)) = 0$. -/
theorem dualSheet_paraKahlerMetric_zero (v₁ v₂ : Fin 3 → R) :
    paraKahlerMetric (dualSheet v₁) (dualSheet v₂) = 0 := by
  dsimp [paraKahlerMetric, dualSheet, vec3Dot]
  ring

/-- The restriction of $\omega$ to the dual sheet vanishes:
$\omega((0, v_1), (0, v_2)) = 0$. Maximality is not claimed here. -/
theorem dualSheet_symplecticForm_zero (v₁ v₂ : Fin 3 → R) :
    symplecticForm (dualSheet v₁) (dualSheet v₂) = 0 := by
  dsimp [symplecticForm, dualSheet, vec3Dot]
  ring

/-!
## Section 5: Zorn Commutator Decomposition: Symplectic $\omega$ + Twice Hodge Cross Products
-/

/-- **Zorn Commutator Decomposition**:
The Zorn commutator $[z_1, z_2]$ decomposes into the symplectic pairing $\omega(z_1, z_2)$
along the para-grading diagonal $I_{\text{para}}$ plus twice the off-diagonal Hodge
cross-product vector $z_1 \times_H z_2$. -/
theorem zorn_commutator_eq_symplectic_add_two_hodgeCross (z₁ z₂ : ParaKahlerVec R) :
    zornCommutator (embedVec z₁) (embedVec z₂) =
      zornAdd (zornSmul (symplecticForm z₁ z₂) zornParaGrading)
        (zornSmul (2 : R) (embedVec (hodgeCrossVec z₁ z₂))) := by
  ext k
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, zornAdd, zornSmul,
      zornParaGrading, symplecticForm, hodgeCrossVec, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, zornAdd, zornSmul,
        zornParaGrading, hodgeCrossVec, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, zornAdd, zornSmul,
        zornParaGrading, hodgeCrossVec, vec3Cross]
      ring
    }
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, zornAdd, zornSmul,
      zornParaGrading, symplecticForm, hodgeCrossVec, vec3Dot]
    ring

/-- The commutator of a primal vector $(u, 0) \in T^+$ and a dual vector $(0, v) \in T^-$ is
purely diagonal and proportional to their canonical pairing $\langle u, v \rangle$:
$[(u, 0), (0, v)] = \langle u, v \rangle I_{\text{para}}$. -/
theorem zorn_commutator_primal_dual_pure_symplectic (u v : Fin 3 → R) :
    zornCommutator (embedVec (primalSheet u)) (embedVec (dualSheet v)) =
      zornSmul (vec3Dot u v) zornParaGrading := by
  ext k
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
      zornSmul, zornParaGrading, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
        zornSmul, zornParaGrading, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
        zornSmul, zornParaGrading, vec3Cross]
      ring
    }
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
      zornSmul, zornParaGrading, vec3Dot]
    ring

/-- The commutator of two primal vectors $(u_1, 0), (u_2, 0) \in T^+$ lands purely in the
dual sheet $T^-$ via the 3D Hodge cross product:
$[(u_1, 0), (u_2, 0)] = 2 (0, u_1 \times u_2)$. -/
theorem zorn_commutator_primal_primal_pure_hodgeCross (u₁ u₂ : Fin 3 → R) :
    zornCommutator (embedVec (primalSheet u₁)) (embedVec (primalSheet u₂)) =
      zornSmul (2 : R) (embedVec (dualSheet (vec3Cross u₁ u₂))) := by
  ext k
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
      zornSmul, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
        zornSmul, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
        zornSmul, vec3Cross]
      ring
    }
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
      zornSmul, vec3Dot]
    ring

/-- The commutator of two dual vectors $(0, v_1), (0, v_2) \in T^-$ lands purely in the
primal sheet $T^+$ via the negative 3D Hodge cross product:
$[(0, v_1), (0, v_2)] = 2 (-v_1 \times v_2, 0)$. -/
theorem zorn_commutator_dual_dual_pure_hodgeCross (v₁ v₂ : Fin 3 → R) :
    zornCommutator (embedVec (dualSheet v₁)) (embedVec (dualSheet v₂)) =
      zornSmul (2 : R) (embedVec (primalSheet (fun k => -vec3Cross v₁ v₂ k))) := by
  ext k
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
      zornSmul, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
        zornSmul, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
        zornSmul, vec3Cross]
      ring
    }
  · dsimp [zornCommutator, zornSub, zornMul, embedVec, primalSheet, dualSheet,
      zornSmul, vec3Dot]
    ring

end RingOperations

/-!
## Section 6: Full Metriplectic Product Synthesis over `ℝ` ($g + \omega + \text{Hodge Cross Product}$)
-/

/-- **Metriplectic Zorn Product Decomposition over `ℝ`**:
For any two phase-space vectors $z_1, z_2 \in \operatorname{ParaKahlerVec} \mathbb{R}$, their full
Zorn split-octonion product unifies the symmetric para-Kähler metric $g$, the skew-symmetric
symplectic form $\omega$, and the off-diagonal Hodge cross-product pairing $z_1 \times_H z_2$:
$$z_1 z_2 = \tfrac{1}{2} g(z_1, z_2) 1_{\text{Zorn}}
  + \tfrac{1}{2} \omega(z_1, z_2) I_{\text{para}} + z_1 \times_H z_2.$$ -/
theorem zornMul_embedVec_metriplectic_decomp (z₁ z₂ : ParaKahlerVec ℝ) :
    zornMul (embedVec z₁) (embedVec z₂) =
      zornAdd
        (zornAdd
          (zornSmul ((1 / 2 : ℝ) * paraKahlerMetric z₁ z₂) zornOne)
          (zornSmul ((1 / 2 : ℝ) * symplecticForm z₁ z₂) zornParaGrading))
        (embedVec (hodgeCrossVec z₁ z₂)) := by
  ext k
  · dsimp [zornMul, embedVec, zornAdd, zornSmul, zornOne, zornParaGrading,
      paraKahlerMetric, symplecticForm, hodgeCrossVec, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, zornAdd, zornSmul, zornOne, zornParaGrading,
        hodgeCrossVec, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, zornAdd, zornSmul, zornOne, zornParaGrading,
        hodgeCrossVec, vec3Cross]
      ring
    }
  · dsimp [zornMul, embedVec, zornAdd, zornSmul, zornOne, zornParaGrading,
      paraKahlerMetric, symplecticForm, hodgeCrossVec, vec3Dot]
    ring

/-!
## Section 7: Para-Kähler Grading Action, Lagrange Coordinate Identity & Chiral Volume Associator
-/

section GradingAndAssociator

variable {R : Type*} [CommRing R]

/-- Alias for the para-complex operator $K(u, v) = (u, -v)$. -/
abbrev paraComplexOp (z : ParaKahlerVec R) : ParaKahlerVec R :=
  paraComplexK z

/-- Zero element of `ZornSplitOctonion R`. -/
def zornZero : ZornSplitOctonion R :=
  ⟨0, fun _ => 0, fun _ => 0, 0⟩

/-- Upper-left Peirce idempotent $e_0 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ in `ZornSplitOctonion R`. -/
def zornE0 : ZornSplitOctonion R :=
  ⟨1, fun _ => 0, fun _ => 0, 0⟩

/-- Lower-right Peirce idempotent $e_1 = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$ in `ZornSplitOctonion R`. -/
def zornE1 : ZornSplitOctonion R :=
  ⟨0, fun _ => 0, fun _ => 0, 1⟩

/-- Algebra anticommutator $\{x, y\} = x y + y x$ on `ZornSplitOctonion R`. -/
def zornAnticommutator (x y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  zornAdd (zornMul x y) (zornMul y x)

/-- Algebra associator $[x, y, z] = (x y) z - x (y z)$ on `ZornSplitOctonion R`. -/
def zornAssociator (x y z : ZornSplitOctonion R) : ZornSplitOctonion R :=
  zornSub (zornMul (zornMul x y) z) (zornMul x (zornMul y z))

/-- Scalar 3D triple product $\det(u_1, u_2, u_3) = \langle u_1 \times u_2, u_3 \rangle$. -/
def vec3TripleProduct (u₁ u₂ u₃ : Fin 3 → R) : R :=
  vec3Dot (vec3Cross u₁ u₂) u₃

/-- **Commutator Action of the Para-Complex Operator $K$**:
The commutator with the diagonal para-grading element $I_{\text{para}} = \operatorname{diag}(1, -1)$
acts on embedded phase-space vectors as $2 K$; no derivation law on the full Zorn algebra is
asserted:
$[I_{\text{para}}, z] = 2 K(z)$. -/
theorem zorn_paraGrading_commutator_embedVec (z : ParaKahlerVec R) :
    zornCommutator zornParaGrading (embedVec z) =
      zornSmul (2 : R) (embedVec (paraComplexK z)) := by
  ext k
  · dsimp [zornCommutator, zornSub, zornMul, zornParaGrading, embedVec,
      zornSmul, paraComplexK, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, zornParaGrading, embedVec,
        zornSmul, paraComplexK, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornCommutator, zornSub, zornMul, zornParaGrading, embedVec,
        zornSmul, paraComplexK, vec3Cross]
      ring
    }
  · dsimp [zornCommutator, zornSub, zornMul, zornParaGrading, embedVec,
      zornSmul, paraComplexK, vec3Dot]
    ring

/-- The diagonal para-grading element $I_{\text{para}}$ anticommutes with every embedded
phase-space vector $z \in V$: $\{I_{\text{para}}, z\} = 0$. -/
theorem zorn_paraGrading_anticommutator_embedVec (z : ParaKahlerVec R) :
    zornAnticommutator zornParaGrading (embedVec z) = zornZero := by
  ext k
  · dsimp [zornAnticommutator, zornAdd, zornMul, zornParaGrading, embedVec, zornZero, vec3Dot]
    ring
  · fin_cases k <;> {
      dsimp [zornAnticommutator, zornAdd, zornMul, zornParaGrading, embedVec, zornZero, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornAnticommutator, zornAdd, zornMul, zornParaGrading, embedVec, zornZero, vec3Cross]
      ring
    }
  · dsimp [zornAnticommutator, zornAdd, zornMul, zornParaGrading, embedVec, zornZero, vec3Dot]
    ring

/-- **Lagrange–Binet–Cauchy Metriplectic Norm Composition Law**:
The para-Kähler metric/symplectic difference of squares `g(z₁, z₂)² - ω(z₁, z₂)²`
plus `4 ⟨u₁ × u₂, v₁ × v₂⟩` equals the product of the individual para-Kähler norms
`g(z₁, z₁) * g(z₂, z₂)`. The Zorn norm composition law itself is `ZornSplitOctonionFin8Bridge.zornNorm_mul`; its coordinate form on embedded para-Kähler vectors is `zornNorm_embedVec_mul_eq_metriplectic_lagrange`. -/
theorem paraKahler_lagrange_norm_composition (z₁ z₂ : ParaKahlerVec R) :
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂ := by
  unfold paraKahlerMetric symplecticForm vec3Dot vec3Cross
  dsimp
  ring

/-- **Lagrange's decomposition identity** for the three-dimensional cross product:
$\langle \mathbf{a}\times\mathbf{b},\; \mathbf{c}\times\mathbf{d}\rangle
 = \langle \mathbf{a}, \mathbf{c}\rangle\langle \mathbf{b}, \mathbf{d}\rangle
 - \langle \mathbf{a}, \mathbf{d}\rangle\langle \mathbf{b}, \mathbf{c}\rangle$.

This is the general four-vector statement underlying
`paraKahler_lagrange_norm_composition` and `hodgeCrossPairing_eq_norm_gap`: the Hodge cross
product is nothing but the Lagrange correction term of the $\mathbb{R}^3$ wedge product. -/
theorem vec3_lagrange (a b c d : Fin 3 → R) :
    vec3Dot (vec3Cross a b) (vec3Cross c d)
      = vec3Dot a c * vec3Dot b d - vec3Dot a d * vec3Dot b c := by
  simp [vec3Dot, vec3Cross]
  ring

/-- **The Hodge cross pairing is exactly the norm gap.** The off-diagonal Hodge pairing
carried by `hodgeCrossVec z₁ z₂` repairs the discrepancy between the $(1,1)$ para-Kähler
inner-product determinant and the multiplicative self-norm product:
$$4\,\langle \mathbf{u}_1 \times \mathbf{u}_2,\ \mathbf{v}_1 \times \mathbf{v}_2\rangle
 = g(z_1,z_1)\,g(z_2,z_2) - \bigl(g(z_1,z_2)^2 - \omega(z_1,z_2)^2\bigr).$$
Equivalently the metriplectic determinant $g^2-\omega^2$ alone under-counts the norm by
exactly one Hodge term. This is the "why" behind `paraKahler_lagrange_norm_composition`,
stated as a standalone discrepancy law. -/
theorem hodgeCrossPairing_eq_norm_gap (z₁ z₂ : ParaKahlerVec R) :
    4 * vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v)
      = paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂
        - (paraKahlerMetric z₁ z₂ ^ 2 - symplecticForm z₁ z₂ ^ 2) := by
  have h := paraKahler_lagrange_norm_composition z₁ z₂
  linear_combination h

/-- **Self-Metric of the Hodge Cross-Product Vector**:
The para-Kähler self-metric of `hodgeCrossVec z₁ z₂` equals
$-2 \langle \mathbf{u}_1 \times \mathbf{u}_2, \mathbf{v}_1 \times \mathbf{v}_2 \rangle$. -/
theorem paraKahlerMetric_hodgeCrossVec_self (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (hodgeCrossVec z₁ z₂) (hodgeCrossVec z₁ z₂) =
      -2 * vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v) := by
  dsimp [paraKahlerMetric, hodgeCrossVec, vec3Dot, vec3Cross]
  ring

/-- **Zorn Norm of the Embedded Hodge Cross-Product Vector**:
The embedded Zorn norm of `hodgeCrossVec z₁ z₂` equals the cross-product pairing
$\langle \mathbf{u}_1 \times \mathbf{u}_2, \mathbf{v}_1 \times \mathbf{v}_2 \rangle$. -/
theorem zornNorm_embedVec_hodgeCrossVec (z₁ z₂ : ParaKahlerVec R) :
    zornNorm (embedVec (hodgeCrossVec z₁ z₂)) =
      vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v) := by
  dsimp [zornNorm, embedVec, hodgeCrossVec, vec3Dot, vec3Cross]
  ring

/-- **Intrinsic Form of the Lagrange Norm Law via `hodgeCrossVec`**:
Since `g(hodgeCrossVec z₁ z₂, hodgeCrossVec z₁ z₂) = -2 ⟨u₁ × u₂, v₁ × v₂⟩`,
the multiplicative norm identity is expressed purely in terms of `g`, `ω`, and `hodgeCrossVec`:
$$g(z_1, z_2)^2 - \omega(z_1, z_2)^2 - 2 g(z_1 \times_H z_2, z_1 \times_H z_2)
  = g(z_1, z_1) g(z_2, z_2).$$ -/
theorem paraKahler_lagrange_norm_via_hodgeCrossVec (z₁ z₂ : ParaKahlerVec R) :
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 -
      2 * paraKahlerMetric (hodgeCrossVec z₁ z₂) (hodgeCrossVec z₁ z₂) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂ := by
  unfold paraKahlerMetric symplecticForm hodgeCrossVec vec3Dot vec3Cross
  dsimp
  ring

/-- **Metriplectic Lagrange Identity in Terms of Embedded Zorn Norms**:
The para-Kähler Lagrange expression equals the product $(2 N(z_1)) (2 N(z_2))$ of the doubled
embedded Zorn norms of $z_1$ and $z_2$. -/
theorem zornNorm_embedVec_mul_eq_metriplectic_lagrange (z₁ z₂ : ParaKahlerVec R) :
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v) =
      (2 * zornNorm (embedVec z₁)) * (2 * zornNorm (embedVec z₂)) := by
  dsimp [paraKahlerMetric, symplecticForm, zornNorm, embedVec, vec3Dot, vec3Cross]
  ring

/-- **Direct Synthesis of Para-Kähler Lagrange Identity with Zorn Norm Multiplicativity**:
The para-Kähler Lagrange expression $g(z_1, z_2)^2 - \omega(z_1, z_2)^2
+ 4 \langle \mathbf{u}_1 \times \mathbf{u}_2, \mathbf{v}_1 \times \mathbf{v}_2 \rangle$ equals
four times the Zorn norm of the split-octonion product `zornMul (embedVec z₁) (embedVec z₂)`. -/
theorem paraKahler_lagrange_eq_four_mul_zornNorm_mul (z₁ z₂ : ParaKahlerVec R) :
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v) =
      4 * zornNorm (zornMul (embedVec z₁) (embedVec z₂)) := by
  dsimp [paraKahlerMetric, symplecticForm, zornNorm, zornMul, embedVec, vec3Dot, vec3Cross]
  ring

/-- Left-associated triple product of three primal sheet vectors lands on the lower-right
Peirce idempotent $e_1$ scaled by the 3D volume $\det(u_1, u_2, u_3)$. -/
theorem zorn_primal_triple_left_eq_volume_smul_e1 (u₁ u₂ u₃ : Fin 3 → R) :
    zornMul (zornMul (embedVec (primalSheet u₁)) (embedVec (primalSheet u₂)))
      (embedVec (primalSheet u₃)) =
      zornSmul (vec3TripleProduct u₁ u₂ u₃) zornE1 := by
  ext k
  · dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE1, vec3TripleProduct, vec3Dot, vec3Cross]
    ring
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE1, vec3Dot, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE1, vec3Dot, vec3Cross]
      ring
    }
  · dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE1, vec3TripleProduct, vec3Dot, vec3Cross]
    ring

/-- Right-associated triple product of three primal sheet vectors lands on the upper-left
Peirce idempotent $e_0$ scaled by the 3D volume $\det(u_1, u_2, u_3)$. -/
theorem zorn_primal_triple_right_eq_volume_smul_e0 (u₁ u₂ u₃ : Fin 3 → R) :
    zornMul (embedVec (primalSheet u₁))
      (zornMul (embedVec (primalSheet u₂)) (embedVec (primalSheet u₃))) =
      zornSmul (vec3TripleProduct u₁ u₂ u₃) zornE0 := by
  ext k
  · dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE0, vec3TripleProduct, vec3Dot, vec3Cross]
    ring
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE0, vec3Dot, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE0, vec3Dot, vec3Cross]
      ring
    }
  · dsimp [zornMul, embedVec, primalSheet, zornSmul, zornE0, vec3TripleProduct, vec3Dot, vec3Cross]
    ring

/-- **Primal Triple Bracketing-Sum Identity**:
The sum of the left- and right-associated triple products $(u_1 u_2) u_3 + u_1 (u_2 u_3)$
of three primal vectors is proportional to the identity element $1_{\text{Zorn}} = e_0 + e_1$
with coefficient equal to the oriented 3D volume $\det(u_1, u_2, u_3)$. This is a sum over
the two bracketings; no permutation symmetry of the inputs is asserted. -/
theorem zorn_primal_triple_bracketing_sum_eq_volume_smul_one (u₁ u₂ u₃ : Fin 3 → R) :
    zornAdd
      (zornMul (zornMul (embedVec (primalSheet u₁)) (embedVec (primalSheet u₂)))
        (embedVec (primalSheet u₃)))
      (zornMul (embedVec (primalSheet u₁))
        (zornMul (embedVec (primalSheet u₂)) (embedVec (primalSheet u₃)))) =
      zornSmul (vec3TripleProduct u₁ u₂ u₃) zornOne := by
  ext k
  · dsimp [zornAdd, zornMul, embedVec, primalSheet, zornSmul, zornOne,
      vec3TripleProduct, vec3Dot, vec3Cross]
    ring
  · fin_cases k <;> {
      dsimp [zornAdd, zornMul, embedVec, primalSheet, zornSmul, zornOne, vec3Dot, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornAdd, zornMul, embedVec, primalSheet, zornSmul, zornOne, vec3Dot, vec3Cross]
      ring
    }
  · dsimp [zornAdd, zornMul, embedVec, primalSheet, zornSmul, zornOne,
      vec3TripleProduct, vec3Dot, vec3Cross]
    ring

/-- **Chiral Volume Associator Identity**:
The Zorn associator $[u_1, u_2, u_3] = (u_1 u_2) u_3 - u_1 (u_2 u_3)$ of three primal sheet
vectors is proportional to the para-grading element $I_{\text{para}} = e_0 - e_1$ with
coefficient $-\det(u_1, u_2, u_3)$. -/
theorem zorn_primal_triple_associator_eq_volume_paraGrading (u₁ u₂ u₃ : Fin 3 → R) :
    zornAssociator
      (embedVec (primalSheet u₁))
      (embedVec (primalSheet u₂))
      (embedVec (primalSheet u₃)) =
      zornSmul (-vec3TripleProduct u₁ u₂ u₃) zornParaGrading := by
  ext k
  · dsimp [zornAssociator, zornSub, zornMul, embedVec, primalSheet, zornSmul,
      zornParaGrading, vec3TripleProduct, vec3Dot, vec3Cross]
    ring
  · fin_cases k <;> {
      dsimp [zornAssociator, zornSub, zornMul, embedVec, primalSheet, zornSmul,
        zornParaGrading, vec3Dot, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [zornAssociator, zornSub, zornMul, embedVec, primalSheet, zornSmul,
        zornParaGrading, vec3Dot, vec3Cross]
      ring
    }
  · dsimp [zornAssociator, zornSub, zornMul, embedVec, primalSheet, zornSmul,
      zornParaGrading, vec3TripleProduct, vec3Dot, vec3Cross]
    ring

/-- The standard primal basis triple has a nonzero associator in the Zorn product.
This witness makes explicit that the `Fin 8` Fock-state carrier equivalence is not
a multiplicative identification with ordinary associative matrix multiplication. -/
theorem zorn_primal_basis_associator_ne_zero :
    zornAssociator
      (embedVec (primalSheet (![1, 0, 0] : Fin 3 → ℝ)))
      (embedVec (primalSheet (![0, 1, 0] : Fin 3 → ℝ)))
      (embedVec (primalSheet (![0, 0, 1] : Fin 3 → ℝ))) ≠ zornZero := by
  rw [zorn_primal_triple_associator_eq_volume_paraGrading]
  norm_num [vec3TripleProduct, vec3Dot, vec3Cross, zornSmul,
    zornParaGrading, zornZero]

/-- No injective multiplicative representation of this Zorn product can land in
an associative semigroup. In particular, the `Fin 8` carrier equivalence cannot
be upgraded to an injective homomorphism into the Fock matrix algebra with its
ordinary associative product. -/
theorem no_injective_zornMul_map_to_associative_semigroup
    {A : Type*} [Semigroup A] :
    ¬ ∃ φ : ZornSplitOctonion ℝ → A,
        Function.Injective φ ∧
          (∀ x y : ZornSplitOctonion ℝ, φ (zornMul x y) = φ x * φ y) := by
  rintro ⟨φ, hinj, hmul⟩
  let x : ZornSplitOctonion ℝ :=
    embedVec (primalSheet (![1, 0, 0] : Fin 3 → ℝ))
  let y : ZornSplitOctonion ℝ :=
    embedVec (primalSheet (![0, 1, 0] : Fin 3 → ℝ))
  let z : ZornSplitOctonion ℝ :=
    embedVec (primalSheet (![0, 0, 1] : Fin 3 → ℝ))
  have hdefect : zornMul (zornMul x y) z ≠ zornMul x (zornMul y z) := by
    intro h
    have hassocZero := congrArg
      (fun q : ZornSplitOctonion ℝ => zornSub q (zornMul x (zornMul y z))) h
    have hassoc : zornAssociator x y z = zornZero := by
      simpa [zornAssociator, zornSub, zornZero] using hassocZero
    exact zorn_primal_basis_associator_ne_zero (by simpa [x, y, z] using hassoc)
  apply hdefect
  apply hinj
  calc
    φ (zornMul (zornMul x y) z) = φ (zornMul x y) * φ z := hmul _ _
    _ = (φ x * φ y) * φ z := by rw [hmul]
    _ = φ x * (φ y * φ z) := mul_assoc _ _ _
    _ = φ x * φ (zornMul y z) := by rw [hmul]
    _ = φ (zornMul x (zornMul y z)) := (hmul _ _).symm

/-!
### Chiral Lightcone Null-Ray Scaling & Unipotent Shear Transport along $T^+ / T^-$
-/

/-- Lower-case spelling of the canonical Zorn-norm null-cone predicate.

This deliberately reuses `IsOnNullCone`: over an arbitrary `CommRing`, the condition
`paraKahlerMetric z z = 0` is only `2 * vec3Dot z.u z.v = 0` and need not be equivalent
to Zorn-norm nullity in characteristic two. -/
def isOnNullCone (z : ParaKahlerVec R) : Prop :=
  IsOnNullCone z

/-- Scalar dilation $\lambda_t(u, v) = (t u, t v)$ along rays in the 6D para-Kähler phase space. -/
def paraKahlerScale (t : R) (z : ParaKahlerVec R) : ParaKahlerVec R :=
  ⟨fun k => t * z.u k, fun k => t * z.v k⟩

/-- Bilinear scaling of the para-Kähler metric $g(\lambda_t z_1, \lambda_s z_2) = (t s) g(z_1, z_2)$. -/
theorem paraKahlerMetric_scale (t s : R) (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraKahlerScale t z₁) (paraKahlerScale s z₂) =
      (t * s) * paraKahlerMetric z₁ z₂ := by
  dsimp [paraKahlerMetric, paraKahlerScale, vec3Dot]
  ring

/-- Bilinear scaling of the canonical symplectic form
$\omega(\lambda_t z_1, \lambda_s z_2) = (t s) \omega(z_1, z_2)$. -/
theorem symplecticForm_scale (t s : R) (z₁ z₂ : ParaKahlerVec R) :
    symplecticForm (paraKahlerScale t z₁) (paraKahlerScale s z₂) =
      (t * s) * symplecticForm z₁ z₂ := by
  dsimp [symplecticForm, paraKahlerScale, vec3Dot]
  ring

/-- Projective ray invariance of the chiral lightcone: if $z$ lies on the null cone
(`isOnNullCone z`), then every scaled point $\lambda_t z$ along the ray also lies on the null cone. -/
theorem isOnNullCone_scale (t : R) {z : ParaKahlerVec R} (hz : isOnNullCone z) :
    isOnNullCone (paraKahlerScale t z) := by
  change IsOnNullCone z at hz
  change IsOnNullCone (paraKahlerScale t z)
  rw [isOnNullCone_iff_vec3Dot_zero] at hz ⊢
  calc
    vec3Dot (paraKahlerScale t z).u (paraKahlerScale t z).v =
        t ^ 2 * vec3Dot z.u z.v := by
          dsimp [paraKahlerScale, vec3Dot]
          ring
    _ = 0 := by rw [hz]; ring

/-- Collinear vectors along the same phase-space ray have a vanishing 5-graded Hodge
cross-product vector: $(\lambda_t z) \times_H z = 0$. -/
theorem hodgeCrossVec_scale_self (t : R) (z : ParaKahlerVec R) :
    hodgeCrossVec (paraKahlerScale t z) z = ⟨fun _ => 0, fun _ => 0⟩ := by
  ext k
  · fin_cases k <;> {
      dsimp [hodgeCrossVec, paraKahlerScale, vec3Cross]
      ring
    }
  · fin_cases k <;> {
      dsimp [hodgeCrossVec, paraKahlerScale, vec3Cross]
      ring
    }

/-- Square-zero sheet-lowering operator $N_-(u, v) = (0, u)$ mapping the primal sheet
$T^+$ into the dual sheet $T^-$ and annihilating $T^-$. -/
def paraNilpotentMinus (z : ParaKahlerVec R) : ParaKahlerVec R :=
  ⟨fun _ => 0, z.u⟩

/-- The sheet-lowering operator $N_-$ is square-zero: $N_-^2 = 0$. -/
theorem paraNilpotentMinus_sq_zero (z : ParaKahlerVec R) :
    paraNilpotentMinus (paraNilpotentMinus z) = ⟨fun _ => 0, fun _ => 0⟩ := by
  ext k <;> rfl

/-- Unipotent shear transport $\mathcal{U}_p = I + p N_-$ along $T^+ \to T^-$:
$\mathcal{U}_p(u, v) = (u, v + p u)$. -/
def paraUnipotentShear (p : R) (z : ParaKahlerVec R) : ParaKahlerVec R :=
  ⟨z.u, fun k => z.v k + p * z.u k⟩

/-- At zero shear parameter $p = 0$, $\mathcal{U}_0$ is the identity on `ParaKahlerVec R`. -/
theorem paraUnipotentShear_zero (z : ParaKahlerVec R) :
    paraUnipotentShear 0 z = z := by
  ext k
  · rfl
  · dsimp [paraUnipotentShear]
    ring

/-- Additive 1-parameter group law for unipotent shear transport:
$\mathcal{U}_{p_1} \circ \mathcal{U}_{p_2} = \mathcal{U}_{p_1 + p_2}$. -/
theorem paraUnipotentShear_add (p₁ p₂ : R) (z : ParaKahlerVec R) :
    paraUnipotentShear p₁ (paraUnipotentShear p₂ z) = paraUnipotentShear (p₁ + p₂) z := by
  ext k
  · rfl
  · dsimp [paraUnipotentShear]
    ring

/-- Invertibility of unipotent shear transport via opposite parameter $-p$:
$\mathcal{U}_{-p}(\mathcal{U}_p(z)) = z$. -/
theorem paraUnipotentShear_neg_cancel (p : R) (z : ParaKahlerVec R) :
    paraUnipotentShear (-p) (paraUnipotentShear p z) = z := by
  rw [paraUnipotentShear_add, neg_add_cancel, paraUnipotentShear_zero]

/-- Evolution of the para-Kähler self-metric under unipotent shear transport:
$g(\mathcal{U}_p z, \mathcal{U}_p z) = g(z, z) + 2 p \langle u, u \rangle$. -/
theorem paraKahlerMetric_paraUnipotentShear_self (p : R) (z : ParaKahlerVec R) :
    paraKahlerMetric (paraUnipotentShear p z) (paraUnipotentShear p z) =
      paraKahlerMetric z z + 2 * p * vec3Dot z.u z.u := by
  dsimp [paraKahlerMetric, paraUnipotentShear, vec3Dot]
  ring

/-- Along the dual null sheet $T^-$, unipotent shear transport $\mathcal{U}_p$ preserves
the chiral lightcone identically for all $p$. -/
theorem isOnNullCone_paraUnipotentShear_dualSheet (p : R) (v : Fin 3 → R) :
    isOnNullCone (paraUnipotentShear p (dualSheet v)) := by
  change IsOnNullCone (paraUnipotentShear p (dualSheet v))
  rw [isOnNullCone_iff_vec3Dot_zero]
  dsimp [paraUnipotentShear, dualSheet, vec3Dot]
  ring

/-- The symplectic pairing between a primal sheet vector $(u, 0) \in T^+$ and its $p$-sheared
image $\mathcal{U}_p(u, 0)$ reads out the additive shear parameter $p \cdot \langle u, u \rangle$. -/
theorem symplecticForm_primal_paraUnipotentShear (p : R) (u : Fin 3 → R) :
    symplecticForm (primalSheet u) (paraUnipotentShear p (primalSheet u)) =
      p * vec3Dot u u := by
  dsimp [symplecticForm, primalSheet, paraUnipotentShear, vec3Dot]
  ring

/-- The para-Kähler-metric-skew nilpotent operator $N_a(u, v) = (0, a \times u)$
associated with a 3D generator vector $a \in R^3$. -/
def paraSkewNilpotent (a : Fin 3 → R) (z : ParaKahlerVec R) : ParaKahlerVec R :=
  ⟨fun _ => 0, vec3Cross a z.u⟩

/-- The operator $N_a$ is square-zero: $N_a^2 = 0$. -/
theorem paraSkewNilpotent_sq_zero (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewNilpotent a (paraSkewNilpotent a z) = ⟨fun _ => 0, fun _ => 0⟩ := by
  ext k
  · rfl
  · fin_cases k <;> {
      dsimp [paraSkewNilpotent, vec3Cross]
      ring
    }

/-- The nilpotent `Nₐ` anticommutes with the para-complex involution `K`:
`K ∘ Nₐ = - Nₐ ∘ K`. In particular, this flow generator exchanges the two
`K`-eigenspaces instead of preserving them as a connection coefficient would. -/
theorem paraSkewNilpotent_anticommutes_paraComplexK
    (a : Fin 3 → R) (z : ParaKahlerVec R) :
    ∀ k, (paraComplexK (paraSkewNilpotent a z)).u k = 0 ∧
      (paraComplexK (paraSkewNilpotent a z)).v k +
        (paraSkewNilpotent a (paraComplexK z)).v k = 0 := by
  intro k
  constructor
  · rfl
  · dsimp [paraComplexK, paraSkewNilpotent]
    ring

/-- If `z` lies in the primal `+1` eigenspace of `K`, then `Nₐ z` lies in
the dual `-1` eigenspace. This makes the sheet exchange explicit. -/
theorem paraSkewNilpotent_maps_primal_eigen_to_dual
    (a : Fin 3 → R) (z : ParaKahlerVec R)
    (hz : paraComplexK z = z) :
    ∀ k, (paraComplexK (paraSkewNilpotent a z)).v k +
      (paraSkewNilpotent a z).v k = 0 := by
  intro k
  rw [← hz]
  exact (paraSkewNilpotent_anticommutes_paraComplexK a z k).2

/-- Infinitesimal metric-skew-symmetry of $N_a$ with respect to the para-Kähler
metric $g$: $g(N_a z_1, z_2) + g(z_1, N_a z_2) = 0$. -/
theorem paraKahlerMetric_paraSkewNilpotent_skew (a : Fin 3 → R) (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraSkewNilpotent a z₁) z₂ +
      paraKahlerMetric z₁ (paraSkewNilpotent a z₂) = 0 := by
  dsimp [paraKahlerMetric, paraSkewNilpotent, vec3Dot, vec3Cross]
  ring

/-- **Step 1a of the Unipotent Invariance Decomposition**:
On the diagonal $z_1 = z_2 = z$, the right infinitesimal generator pairing
$g(z, N_a z) = \langle u, a \times u \rangle$ vanishes identically over any commutative ring. -/
theorem paraKahlerMetric_paraSkewNilpotent_self_right (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraKahlerMetric z (paraSkewNilpotent a z) = 0 := by
  dsimp [paraKahlerMetric, paraSkewNilpotent, vec3Dot, vec3Cross]
  ring

/-- **Step 1b of the Unipotent Invariance Decomposition**:
On the diagonal $z_1 = z_2 = z$, the left infinitesimal generator pairing
$g(N_a z, z) = \langle a \times u, u \rangle$ vanishes identically over any commutative ring. -/
theorem paraKahlerMetric_paraSkewNilpotent_self_left (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraKahlerMetric (paraSkewNilpotent a z) z = 0 := by
  dsimp [paraKahlerMetric, paraSkewNilpotent, vec3Dot, vec3Cross]
  ring

/-- **Step 2 of the Unipotent Invariance Decomposition**:
Because $N_a$ maps every phase-space vector into the $g$-isotropic dual sheet $T^-$
(and is square-zero, $N_a^2 = 0$), the quadratic $p^2$-term $g(N_a z_1, N_a z_2)$ vanishes
identically for all $z_1, z_2$. -/
theorem paraKahlerMetric_paraSkewNilpotent_quad_zero (a : Fin 3 → R)
    (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraSkewNilpotent a z₁) (paraSkewNilpotent a z₂) = 0 := by
  dsimp [paraKahlerMetric, paraSkewNilpotent, vec3Dot, vec3Cross]
  ring

/-- Unipotent flow generated by the para-Kähler-skew nilpotent $N_a$:
$\mathcal{U}_{p, a}(u, v) = (u, v + p (a \times u))$. -/
def paraSkewUnipotentFlow (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) : ParaKahlerVec R :=
  ⟨z.u, fun k => z.v k + p * vec3Cross a z.u k⟩

/-- At flow parameter $p = 0$, the unipotent flow $\mathcal{U}_{0, a}$ is the identity. -/
@[simp]
theorem paraSkewUnipotentFlow_zero (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewUnipotentFlow 0 a z = z := by
  ext k
  · rfl
  · dsimp [paraSkewUnipotentFlow]
    ring

/-- Additive 1-parameter group law for the para-Kähler-skew unipotent flow:
$\mathcal{U}_{p_1, a} \circ \mathcal{U}_{p_2, a} = \mathcal{U}_{p_1 + p_2, a}$. -/
theorem paraSkewUnipotentFlow_add (p₁ p₂ : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewUnipotentFlow p₁ a (paraSkewUnipotentFlow p₂ a z) =
      paraSkewUnipotentFlow (p₁ + p₂) a z := by
  ext k
  · rfl
  · dsimp [paraSkewUnipotentFlow]
    ring

/-- Left-inverse law for the 1-parameter unipotent flow $\mathcal{U}_{p, a}$:
$\mathcal{U}_{-p, a}(\mathcal{U}_{p, a}(z)) = z$. -/
@[simp]
theorem paraSkewUnipotentFlow_neg_cancel (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewUnipotentFlow (-p) a (paraSkewUnipotentFlow p a z) = z := by
  rw [paraSkewUnipotentFlow_add (-p) p a z, neg_add_cancel, paraSkewUnipotentFlow_zero a z]

/-- Right-inverse law for the 1-parameter unipotent flow $\mathcal{U}_{p, a}$:
$\mathcal{U}_{p, a}(\mathcal{U}_{-p, a}(z)) = z$. -/
@[simp]
theorem paraSkewUnipotentFlow_cancel_neg (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewUnipotentFlow p a (paraSkewUnipotentFlow (-p) a z) = z := by
  rw [paraSkewUnipotentFlow_add p (-p) a z, add_neg_cancel, paraSkewUnipotentFlow_zero a z]

/-- The 1-parameter unipotent flow $\mathcal{U}_{p, a}$ packaged as a bijective equivalence
on the 6D para-Kähler phase space `ParaKahlerVec R`, with inverse $\mathcal{U}_{-p, a}$. -/
def paraSkewUnipotentFlowEquiv (p : R) (a : Fin 3 → R) :
    ParaKahlerVec R ≃ ParaKahlerVec R where
  toFun := paraSkewUnipotentFlow p a
  invFun := paraSkewUnipotentFlow (-p) a
  left_inv z := paraSkewUnipotentFlow_neg_cancel p a z
  right_inv z := paraSkewUnipotentFlow_cancel_neg p a z

@[simp]
theorem paraSkewUnipotentFlowEquiv_apply (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewUnipotentFlowEquiv p a z = paraSkewUnipotentFlow p a z :=
  rfl

@[simp]
theorem paraSkewUnipotentFlowEquiv_symm_apply (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    (paraSkewUnipotentFlowEquiv p a).symm z = paraSkewUnipotentFlow (-p) a z :=
  rfl

/-!
### `AddCommGroup`, `Module`, `LinearMap`, and `LinearEquiv` Realization on `ParaKahlerVec R`
-/

instance instAddParaKahlerVec : Add (ParaKahlerVec R) :=
  ⟨fun z₁ z₂ => ⟨z₁.u + z₂.u, z₁.v + z₂.v⟩⟩

instance instZeroParaKahlerVec : Zero (ParaKahlerVec R) :=
  ⟨⟨0, 0⟩⟩

instance instNegParaKahlerVec : Neg (ParaKahlerVec R) :=
  ⟨fun z => ⟨-z.u, -z.v⟩⟩

instance instSubParaKahlerVec : Sub (ParaKahlerVec R) :=
  ⟨fun z₁ z₂ => ⟨z₁.u - z₂.u, z₁.v - z₂.v⟩⟩

instance instSMulParaKahlerVec {S : Type*} [SMul S R] : SMul S (ParaKahlerVec R) :=
  ⟨fun r z => ⟨r • z.u, r • z.v⟩⟩

@[simp]
theorem ParaKahlerVec.add_u (z₁ z₂ : ParaKahlerVec R) : (z₁ + z₂).u = z₁.u + z₂.u :=
  rfl

@[simp]
theorem ParaKahlerVec.add_v (z₁ z₂ : ParaKahlerVec R) : (z₁ + z₂).v = z₁.v + z₂.v :=
  rfl

@[simp]
theorem ParaKahlerVec.zero_u : (0 : ParaKahlerVec R).u = 0 :=
  rfl

@[simp]
theorem ParaKahlerVec.zero_v : (0 : ParaKahlerVec R).v = 0 :=
  rfl

@[simp]
theorem ParaKahlerVec.neg_u (z : ParaKahlerVec R) : (-z).u = -z.u :=
  rfl

@[simp]
theorem ParaKahlerVec.neg_v (z : ParaKahlerVec R) : (-z).v = -z.v :=
  rfl

@[simp]
theorem ParaKahlerVec.sub_u (z₁ z₂ : ParaKahlerVec R) : (z₁ - z₂).u = z₁.u - z₂.u :=
  rfl

@[simp]
theorem ParaKahlerVec.sub_v (z₁ z₂ : ParaKahlerVec R) : (z₁ - z₂).v = z₁.v - z₂.v :=
  rfl

omit [CommRing R] in
@[simp]
theorem ParaKahlerVec.smul_u {S : Type*} [SMul S R] (r : S) (z : ParaKahlerVec R) :
    (r • z).u = r • z.u :=
  rfl

omit [CommRing R] in
@[simp]
theorem ParaKahlerVec.smul_v {S : Type*} [SMul S R] (r : S) (z : ParaKahlerVec R) :
    (r • z).v = r • z.v :=
  rfl

instance instAddCommGroupParaKahlerVec : AddCommGroup (ParaKahlerVec R) where
  add := (· + ·)
  add_assoc a b c := by ext k <;> exact add_assoc _ _ _
  zero := 0
  zero_add a := by ext k <;> exact zero_add _
  add_zero a := by ext k <;> exact add_zero _
  nsmul n z := n • z
  nsmul_zero z := by ext k <;> exact zero_smul ℕ _
  nsmul_succ n z := by ext k <;> exact succ_nsmul _ n
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg a b := by ext k <;> exact sub_eq_add_neg _ _
  zsmul n z := n • z
  zsmul_zero' z := by ext k <;> exact zero_smul ℤ _
  zsmul_succ' n z := by ext k <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n z := by ext k <;> exact SubNegMonoid.zsmul_neg' n _
  neg_add_cancel a := by ext k <;> exact neg_add_cancel _
  add_comm a b := by ext k <;> exact add_comm _ _

instance instModuleParaKahlerVec : Module R (ParaKahlerVec R) where
  smul := (· • ·)
  one_smul z := by ext k <;> exact one_smul R _
  mul_smul r s z := by ext k <;> exact mul_smul r s _
  smul_zero r := by ext k <;> exact smul_zero r
  smul_add r z₁ z₂ := by ext k <;> exact smul_add r _ _
  add_smul r s z := by ext k <;> exact add_smul r s _
  zero_smul z := by ext k <;> exact zero_smul R _

/-- Additivity of the metric-skew square-zero generator $N_a$. -/
theorem paraSkewNilpotent_add (a : Fin 3 → R) (z₁ z₂ : ParaKahlerVec R) :
    paraSkewNilpotent a (z₁ + z₂) = paraSkewNilpotent a z₁ + paraSkewNilpotent a z₂ := by
  ext k
  · simp [paraSkewNilpotent]
  · fin_cases k
    · dsimp [ParaKahlerVec.add_v, paraSkewNilpotent, vec3Cross, ParaKahlerVec.add_u]; ring
    · dsimp [ParaKahlerVec.add_v, paraSkewNilpotent, vec3Cross, ParaKahlerVec.add_u]; ring
    · dsimp [ParaKahlerVec.add_v, paraSkewNilpotent, vec3Cross, ParaKahlerVec.add_u]; ring

/-- Scalar-multiplication compatibility of the metric-skew square-zero generator $N_a$. -/
theorem paraSkewNilpotent_smul (a : Fin 3 → R) (r : R) (z : ParaKahlerVec R) :
    paraSkewNilpotent a (r • z) = r • paraSkewNilpotent a z := by
  ext k
  · simp [paraSkewNilpotent]
  · fin_cases k
    · dsimp [ParaKahlerVec.smul_v, paraSkewNilpotent, vec3Cross, ParaKahlerVec.smul_u,
        smul_eq_mul]; ring
    · dsimp [ParaKahlerVec.smul_v, paraSkewNilpotent, vec3Cross, ParaKahlerVec.smul_u,
        smul_eq_mul]; ring
    · dsimp [ParaKahlerVec.smul_v, paraSkewNilpotent, vec3Cross, ParaKahlerVec.smul_u,
        smul_eq_mul]; ring

/-- The metric-skew square-zero operator $N_a(u, v) = (0, a \times u)$ packaged as an
$R$-linear endomorphism of `ParaKahlerVec R`. -/
def paraSkewNilpotentLinear (a : Fin 3 → R) : ParaKahlerVec R →ₗ[R] ParaKahlerVec R where
  toFun := paraSkewNilpotent a
  map_add' := paraSkewNilpotent_add a
  map_smul' := paraSkewNilpotent_smul a

@[simp]
theorem paraSkewNilpotentLinear_apply (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewNilpotentLinear a z = paraSkewNilpotent a z :=
  rfl

/-- The linear operator `paraSkewNilpotentLinear a` is square-zero:
$N_a \circ N_a = 0$ in `ParaKahlerVec R →ₗ[R] ParaKahlerVec R`. -/
theorem paraSkewNilpotentLinear_comp_self (a : Fin 3 → R) :
    (paraSkewNilpotentLinear a).comp (paraSkewNilpotentLinear a) = 0 :=
  LinearMap.ext fun z => paraSkewNilpotent_sq_zero a z

/-- Infinitesimal metric skew-symmetry of `paraSkewNilpotentLinear a` with respect to the
para-Kähler metric $g$. -/
theorem paraKahlerMetric_paraSkewNilpotentLinear_skew (a : Fin 3 → R)
    (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraSkewNilpotentLinear a z₁) z₂ +
      paraKahlerMetric z₁ (paraSkewNilpotentLinear a z₂) = 0 :=
  paraKahlerMetric_paraSkewNilpotent_skew a z₁ z₂

/-- The unipotent flow $\mathcal{U}_{p, a} = I + p N_a$ as a linear map on `ParaKahlerVec R`. -/
def paraSkewUnipotentFlowLinearMap (p : R) (a : Fin 3 → R) :
    ParaKahlerVec R →ₗ[R] ParaKahlerVec R :=
  LinearMap.id + p • paraSkewNilpotentLinear a

@[simp]
theorem paraSkewUnipotentFlowLinearMap_apply (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewUnipotentFlowLinearMap p a z = paraSkewUnipotentFlow p a z := by
  ext k
  · change z.u k + p * 0 = z.u k
    rw [mul_zero, add_zero]
  · rfl

/-- The 1-parameter unipotent flow $\mathcal{U}_{p, a} = I + p N_a$ packaged as an
$R$-linear automorphism (`LinearEquiv`) of `ParaKahlerVec R`, with inverse
$\mathcal{U}_{-p, a} = I - p N_a$. -/
def paraSkewUnipotentFlowLinearEquiv (p : R) (a : Fin 3 → R) :
    ParaKahlerVec R ≃ₗ[R] ParaKahlerVec R where
  toLinearMap := paraSkewUnipotentFlowLinearMap p a
  invFun := paraSkewUnipotentFlowLinearMap (-p) a
  left_inv z := by
    change paraSkewUnipotentFlowLinearMap (-p) a (paraSkewUnipotentFlowLinearMap p a z) = z
    rw [paraSkewUnipotentFlowLinearMap_apply, paraSkewUnipotentFlowLinearMap_apply,
      paraSkewUnipotentFlow_neg_cancel p a z]
  right_inv z := by
    change paraSkewUnipotentFlowLinearMap p a (paraSkewUnipotentFlowLinearMap (-p) a z) = z
    rw [paraSkewUnipotentFlowLinearMap_apply, paraSkewUnipotentFlowLinearMap_apply,
      paraSkewUnipotentFlow_cancel_neg p a z]

@[simp]
theorem paraSkewUnipotentFlowLinearEquiv_apply (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    paraSkewUnipotentFlowLinearEquiv p a z = paraSkewUnipotentFlow p a z :=
  paraSkewUnipotentFlowLinearMap_apply p a z

@[simp]
theorem paraSkewUnipotentFlowLinearEquiv_symm_apply (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    (paraSkewUnipotentFlowLinearEquiv p a).symm z = paraSkewUnipotentFlow (-p) a z :=
  paraSkewUnipotentFlowLinearMap_apply (-p) a z

/-- **Step 3 of the Unipotent Invariance Decomposition (Quadratic Taylor Expansion in $p$)**:
For $\mathcal{U}_{p, a} = I + p N_a$, the evolved para-Kähler metric expands into its
zeroth-order base metric $g(z_1, z_2)$, its linear $p$-coefficient
$g(N_a z_1, z_2) + g(z_1, N_a z_2)$ (which vanishes by metric skew-symmetry),
and its quadratic $p^2$-coefficient $g(N_a z_1, N_a z_2)$ (which vanishes by $T^-$ isotropy). -/
theorem paraKahlerMetric_paraSkewUnipotentFlow_expand (p : R) (a : Fin 3 → R)
    (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraSkewUnipotentFlow p a z₁) (paraSkewUnipotentFlow p a z₂) =
      paraKahlerMetric z₁ z₂ +
        p * (paraKahlerMetric (paraSkewNilpotent a z₁) z₂ +
          paraKahlerMetric z₁ (paraSkewNilpotent a z₂)) +
        p ^ 2 * paraKahlerMetric (paraSkewNilpotent a z₁) (paraSkewNilpotent a z₂) := by
  dsimp [paraKahlerMetric, paraSkewUnipotentFlow, paraSkewNilpotent, vec3Dot, vec3Cross]
  ring

/-- Exact metric invariance of the para-Kähler-skew unipotent flow:
$g(\mathcal{U}_{p, a} z_1, \mathcal{U}_{p, a} z_2) = g(z_1, z_2)$. -/
theorem paraKahlerMetric_paraSkewUnipotentFlow_invariant (p : R) (a : Fin 3 → R)
    (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraSkewUnipotentFlow p a z₁) (paraSkewUnipotentFlow p a z₂) =
      paraKahlerMetric z₁ z₂ := by
  dsimp [paraKahlerMetric, paraSkewUnipotentFlow, vec3Dot, vec3Cross]
  ring

/-- Exact metric invariance of the linear automorphism `paraSkewUnipotentFlowLinearEquiv p a`. -/
theorem paraKahlerMetric_paraSkewUnipotentFlowLinearEquiv_invariant (p : R) (a : Fin 3 → R)
    (z₁ z₂ : ParaKahlerVec R) :
    paraKahlerMetric (paraSkewUnipotentFlowLinearEquiv p a z₁)
      (paraSkewUnipotentFlowLinearEquiv p a z₂) =
      paraKahlerMetric z₁ z₂ := by
  rw [paraSkewUnipotentFlowLinearEquiv_apply, paraSkewUnipotentFlowLinearEquiv_apply,
    paraKahlerMetric_paraSkewUnipotentFlow_invariant p a z₁ z₂]

/-- The para-Kähler-skew unipotent flow preserves the full 6D Zorn-norm null cone
identically for all $p$ and $a$: $\mathcal{U}_{p, a} z$ is null if and only if $z$ is null. -/
theorem isOnNullCone_paraSkewUnipotentFlow_iff (p : R) (a : Fin 3 → R) (z : ParaKahlerVec R) :
    isOnNullCone (paraSkewUnipotentFlow p a z) ↔ isOnNullCone z := by
  change IsOnNullCone (paraSkewUnipotentFlow p a z) ↔ IsOnNullCone z
  rw [isOnNullCone_iff_vec3Dot_zero, isOnNullCone_iff_vec3Dot_zero]
  have hpair :
      vec3Dot (paraSkewUnipotentFlow p a z).u (paraSkewUnipotentFlow p a z).v =
        vec3Dot z.u z.v := by
    dsimp [paraSkewUnipotentFlow, vec3Dot, vec3Cross]
    ring
  rw [hpair]

/-- **Null-Cone Metriplectic Reduction to Hodge Cross Self-Metric**:
Whenever $z_1$ lies on the Zorn-norm null cone (`isOnNullCone z₁`),
the metriplectic difference of squares $g(z_1, z_2)^2 - \omega(z_1, z_2)^2$ equals twice the
para-Kähler self-metric of the Hodge cross-product vector $z_1 \times_H z_2$. -/
theorem nullCone_metriplectic_eq_two_mul_hodgeCrossVec_self
    {z₁ z₂ : ParaKahlerVec R} (hz₁ : isOnNullCone z₁) :
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 =
      2 * paraKahlerMetric (hodgeCrossVec z₁ z₂) (hodgeCrossVec z₁ z₂) := by
  change IsOnNullCone z₁ at hz₁
  have hdot : vec3Dot z₁.u z₁.v = 0 :=
    (isOnNullCone_iff_vec3Dot_zero z₁).mp hz₁
  have hself : paraKahlerMetric z₁ z₁ = 0 := by
    unfold paraKahlerMetric vec3Dot
    dsimp [vec3Dot] at hdot
    linear_combination 2 * hdot
  have hlag := paraKahler_lagrange_norm_via_hodgeCrossVec z₁ z₂
  rw [hself, zero_mul] at hlag
  linear_combination hlag

/-- **Dynamic Chiral Lightcone Metriplectic–Hodge Lock for All Flow Times $p$**:
Because the metric-skew unipotent flow $\mathcal{U}_{p, a}$ preserves the Zorn-norm null cone
identically (`isOnNullCone_paraSkewUnipotentFlow_iff`), any null-cone state $z_1$ paired with an
arbitrary state $z_2$ obeys the exact metriplectic–Hodge balance along the entire unipotent
trajectory $p \mapsto \mathcal{U}_{p, a} z_i$:
$$g(\mathcal{U}_{p, a} z_1, \mathcal{U}_{p, a} z_2)^2
  - \omega(\mathcal{U}_{p, a} z_1, \mathcal{U}_{p, a} z_2)^2
  = 2\, g(\mathcal{U}_{p, a} z_1 \times_H \mathcal{U}_{p, a} z_2,\;
          \mathcal{U}_{p, a} z_1 \times_H \mathcal{U}_{p, a} z_2).$$ -/
theorem nullCone_paraSkewUnipotentFlow_metriplectic_hodge_balance
    (p : R) (a : Fin 3 → R) {z₁ z₂ : ParaKahlerVec R} (hz₁ : isOnNullCone z₁) :
    (paraKahlerMetric (paraSkewUnipotentFlow p a z₁) (paraSkewUnipotentFlow p a z₂)) ^ 2 -
      (symplecticForm (paraSkewUnipotentFlow p a z₁) (paraSkewUnipotentFlow p a z₂)) ^ 2 =
      2 * paraKahlerMetric
        (hodgeCrossVec (paraSkewUnipotentFlow p a z₁) (paraSkewUnipotentFlow p a z₂))
        (hodgeCrossVec (paraSkewUnipotentFlow p a z₁) (paraSkewUnipotentFlow p a z₂)) :=
  nullCone_metriplectic_eq_two_mul_hodgeCrossVec_self
    ((isOnNullCone_paraSkewUnipotentFlow_iff p a z₁).mpr hz₁)

end GradingAndAssociator

end InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone

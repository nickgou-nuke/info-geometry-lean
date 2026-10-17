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
     = g(z_1, z_1) g(z_2, z_2)$ (`paraKahler_lagrange_coordinate_identity`), compatible with the
     separate Zorn norm composition theorem `ZornSplitOctonionFin8Bridge.zornNorm_mul`.
   - Left and right primal triple-product projections onto the Peirce idempotents $e_1, e_0$
     scaled by $\det(u_1, u_2, u_3)$ (`zorn_primal_triple_left_eq_volume_smul_e1`,
     `zorn_primal_triple_right_eq_volume_smul_e0`), the sum of these two bracketings as a
     scalar multiple of $1_{\text{Zorn}}$ (`zorn_primal_triple_bracketing_sum_eq_volume_smul_one`),
     and chiral volume associator
     identity $[u_1, u_2, u_3] = -\det(u_1, u_2, u_3) I_{\text{para}}$
     (`zorn_primal_triple_associator_eq_volume_paraGrading`).

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

/-- **Para-Kähler Lagrange–Binet–Cauchy Coordinate Identity**:
The difference of squares of the para-Kähler metric $g(z_1, z_2)$ and symplectic form
$\omega(z_1, z_2)$ combines with the cross-product pairing $4 \langle u_1 \times u_2, v_1 \times v_2 \rangle$
to yield the product of self-metrics $g(z_1, z_1) g(z_2, z_2)$. The Zorn norm composition law
itself is stated separately as `ZornSplitOctonionFin8Bridge.zornNorm_mul`; this lemma records its
coordinate Lagrange identity on embedded para-Kähler vectors. -/
theorem paraKahler_lagrange_coordinate_identity (z₁ z₂ : ParaKahlerVec R) :
    (paraKahlerMetric z₁ z₂) ^ 2 - (symplecticForm z₁ z₂) ^ 2 +
      4 * vec3Dot (vec3Cross z₁.u z₂.u) (vec3Cross z₁.v z₂.v) =
      paraKahlerMetric z₁ z₁ * paraKahlerMetric z₂ z₂ := by
  dsimp [paraKahlerMetric, symplecticForm, vec3Dot, vec3Cross]
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

end GradingAndAssociator

end InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge

/-!
# Split-Quaternion Subalgebra Embedding, Generalized Socle Leibniz Characterization, and Joint 17-Parameter Separation

This module establishes four structural results connecting the 4D $(2,1)$ coordinate algebra
of `InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly` with the Zorn split-octonion carrier
`ZornSplitOctonion R` and the 14-parameter diagonally lifted $G_2$ derivation family
`sedenionG2Derivation` from `InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge`:

1. **Section 1 — Exact `IsSo21Adjoint` Characterization of `socleDerivation` & Associative Split-Quaternion Subalgebra Embedding $\mathbb{H}_s \hookrightarrow \mathbb{O}_s$**:
   - Defines `IsSo21Adjoint X` packaging the $(2,1)$ cross-product derivation law and
     `so21BilinearForm` skew-adjointness for $X \in \operatorname{Mat}_{3 \times 3}(R)$.
   - Proves that `socleDerivation X` satisfies the Leibniz rule on `socleDoublingMul` **if and
     only if** `IsSo21Adjoint X` holds (`socleDerivation_leibniz_iff_isSo21Adjoint`).
   - Defines the associative split-quaternion multiplication `splitQuatSocleMul` on
     `R × (Fin 3 → R)` (with $+ \operatorname{so21BilinearForm}$), proves its associativity
     (`splitQuatSocleMul_assoc`) and its Leibniz compatibility under `IsSo21Adjoint`
     (`socleDerivation_leibniz_splitQuatSocleMul_of_isSo21Adjoint`), and constructs the
     explicit unital algebra homomorphism `embedSplitQuatToZorn : R × (Fin 3 → R) → ZornSplitOctonion R`
     (`embedSplitQuatToZorn_one`, `embedSplitQuatToZorn_mul`).

2. **Section 2 — Parameter Additivity of `sedenionG2Derivation` and Pointwise Sums of Derivations**:
   - Proves that `parameterAction`, `zornG2Derivation`, and `sedenionG2Derivation` are additive
     in the 14-parameter vector `p : Params` (`sedenionG2Derivation_add_left`), and that the
     pointwise sum of any two split-sedenion derivations is again a derivation of `sedenionMul`
     (`sedenion_derivations_add`).

3. **Section 3 — Lifting `socleDerivation` to `SplitSedenion ℝ` and the Explicit Leibniz Counterexample**:
   - Defines `socleDerivationLift X : SplitSedenion R → SplitSedenion R` acting on the
     $\Lambda^2$ (`v`) slot of the second Zorn factor, and proves the explicit negative result
     `socleDerivationLift_not_leibniz`: `socleDerivationLift (sl2GenK13 (R := ℝ))` does **not**
     satisfy the Leibniz rule for `sedenionMul` on the $\Lambda^1$ probe pair
     `((lambda1Probe 0, zornZero), (zornZero, lambda1Probe 1))`.

4. **Section 4 — Joint Separation `sedenionSocleDirectSum_injective` via Three Basis Probes vs. Two-Probe Failure on $M_3(\mathbb{R})$**:
   - Defines the pointwise sum `sedenionSocleDirectSum p M` of `sedenionG2Derivation p` and
     `socleDerivationLift M`, proves that `readSedenionG2Params` annihilates the socle lift and
     recovers `p` (`readSedenionG2Params_sedenionSocleDirectSum`), and proves full kernel
     separation `sedenionSocleDirectSum_injective` using the three $\Lambda^2$ basis probes
     `V 0, V 1, V 2`.
   - Proves `two_probes_do_not_separate`: on the unrestricted 9-dimensional matrix space
     `Matrix (Fin 3) (Fin 3) ℝ`, the non-zero matrix `nonSeparatingMatrix` annihilates both
     `(0, 1, 1)` and `(1, 1, 0)` and is detected only by the third probe `(1, 0, 1)`.
-/

noncomputable section

namespace InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix (E11 E22 U V)
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.SplitSedenionDerivationAnomaly

/-!
## Section 1: Exact `IsSo21Adjoint` Characterization & Associative Split-Quaternion Subalgebra Embedding
-/

/-- Real $3 \times 3$ specialization of $J_{12}$ for carrier-matched non-commutativity certification. -/
abbrev sl2GenJ12Real : Matrix (Fin 3) (Fin 3) ℝ :=
  sl2GenJ12 (R := ℝ)

/-- Real $3 \times 3$ specialization of $K_{13}$ for carrier-matched non-commutativity certification. -/
abbrev sl2GenK13Real : Matrix (Fin 3) (Fin 3) ℝ :=
  sl2GenK13 (R := ℝ)

/-- Explicit non-commutativity witness on `Matrix (Fin 3) (Fin 3) ℝ`:
$J_{12} K_{13} \neq K_{13} J_{12}$. -/
theorem sl2Gen_real_noncommute :
    sl2GenJ12Real * sl2GenK13Real ≠ sl2GenK13Real * sl2GenJ12Real :=
  sl2_generator_products_noncommute

/-- `socleDerivation` annihilates the scalar coordinate and applies `X.mulVec` to the vector slot. -/
theorem socleDerivation_scalar {R : Type*} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (c : R) (w : Fin 3 → R) :
    socleDerivation X (c, w) = (0, X.mulVec w) :=
  rfl

/-- Predicate stating that $X \in \operatorname{Mat}_{3 \times 3}(R)$ acts as a derivation of
`so21CrossProduct` and is skew-adjoint with respect to `so21BilinearForm`. -/
def IsSo21Adjoint {R : Type*} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) : Prop :=
  (∀ u v : Fin 3 → R, X.mulVec (so21CrossProduct u v) =
      so21CrossProduct (X.mulVec u) v + so21CrossProduct u (X.mulVec v)) ∧
    (∀ u v : Fin 3 → R,
      so21BilinearForm (X.mulVec u) v + so21BilinearForm u (X.mulVec v) = 0)

/-- The compact rotation generator `sl2GenJ12` satisfies `IsSo21Adjoint`. -/
theorem sl2GenJ12_isSo21Adjoint {R : Type*} [CommRing R] :
    IsSo21Adjoint (sl2GenJ12 (R := R)) :=
  ⟨fun u v => (so21_generators_leibniz_crossProduct (R := R) u v).1,
   fun u v => (sl2_so21_generators_metric_invariance (R := R) u v).1⟩

/-- The first hyperbolic boost generator `sl2GenK13` satisfies `IsSo21Adjoint`. -/
theorem sl2GenK13_isSo21Adjoint {R : Type*} [CommRing R] :
    IsSo21Adjoint (sl2GenK13 (R := R)) :=
  ⟨fun u v => (so21_generators_leibniz_crossProduct (R := R) u v).2.1,
   fun u v => (sl2_so21_generators_metric_invariance (R := R) u v).2.1⟩

/-- The second hyperbolic boost generator `sl2GenK23` satisfies `IsSo21Adjoint`. -/
theorem sl2GenK23_isSo21Adjoint {R : Type*} [CommRing R] :
    IsSo21Adjoint (sl2GenK23 (R := R)) :=
  ⟨fun u v => (so21_generators_leibniz_crossProduct (R := R) u v).2.2,
   fun u v => (sl2_so21_generators_metric_invariance (R := R) u v).2.2⟩

/-- Combined packet certifying that all three $(2,1)$ generators satisfy `IsSo21Adjoint`. -/
theorem sl2Gen_isSo21Adjoint {R : Type*} [CommRing R] :
    IsSo21Adjoint (sl2GenJ12 (R := R)) ∧
      IsSo21Adjoint (sl2GenK13 (R := R)) ∧
      IsSo21Adjoint (sl2GenK23 (R := R)) :=
  ⟨sl2GenJ12_isSo21Adjoint, sl2GenK13_isSo21Adjoint, sl2GenK23_isSo21Adjoint⟩

/-- Any matrix $X$ satisfying `IsSo21Adjoint X` differentiates `socleDoublingMul` via `socleDerivation X`. -/
theorem socleDerivation_leibniz_of_isSo21Adjoint {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R)
    (hX : IsSo21Adjoint X) (x y : R × (Fin 3 → R)) :
    socleDerivation X (socleDoublingMul x y) =
      socleDoublingMul (socleDerivation X x) y + socleDoublingMul x (socleDerivation X y) := by
  obtain ⟨c₁, u⟩ := x
  obtain ⟨c₂, v⟩ := y
  have key : (fun j => c₁ * v j + c₂ * u j + so21CrossProduct u v j) =
      c₁ • v + c₂ • u + so21CrossProduct u v := by
    funext j
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hvec : X.mulVec (fun j => c₁ * v j + c₂ * u j + so21CrossProduct u v j) =
      c₁ • X.mulVec v + c₂ • X.mulVec u +
        so21CrossProduct (X.mulVec u) v + so21CrossProduct u (X.mulVec v) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hX.1 u v]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine Prod.ext ?_ ?_
  · show 0 = (0 * c₂ - so21BilinearForm (X.mulVec u) v) +
        (c₁ * 0 - so21BilinearForm u (X.mulVec v))
    linear_combination hX.2 u v
  · simp only [socleDerivation, socleDoublingMul]
    rw [hvec]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> (simp [so21CrossProduct]; ring)

/-- Converse characterization: if `socleDerivation X` satisfies the Leibniz rule for
`socleDoublingMul`, then `X` satisfies `IsSo21Adjoint X`. -/
theorem isSo21Adjoint_of_socleDerivation_leibniz {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R)
    (hL : ∀ x y : R × (Fin 3 → R),
      socleDerivation X (socleDoublingMul x y) =
        socleDoublingMul (socleDerivation X x) y + socleDoublingMul x (socleDerivation X y)) :
    IsSo21Adjoint X := by
  refine ⟨?_, ?_⟩
  · intro u v
    have h2 := congrArg Prod.snd (hL (0, u) (0, v))
    have hzero : (fun i : Fin 3 => (0 : R) * v i + (0 : R) * u i + so21CrossProduct u v i) =
        so21CrossProduct u v := by
      funext i
      ring
    dsimp [socleDerivation, socleDoublingMul] at h2
    rw [hzero] at h2
    funext i
    have hi := congrFun h2 i
    change X.mulVec (so21CrossProduct u v) i =
      (0 * v i + 0 * X.mulVec u i + so21CrossProduct (X.mulVec u) v i) +
      (0 * X.mulVec v i + 0 * u i + so21CrossProduct u (X.mulVec v) i) at hi
    change X.mulVec (so21CrossProduct u v) i =
      so21CrossProduct (X.mulVec u) v i + so21CrossProduct u (X.mulVec v) i
    linear_combination hi
  · intro u v
    have h1 := congrArg Prod.fst (hL (0, u) (0, v))
    dsimp [socleDerivation, socleDoublingMul] at h1
    linear_combination h1

/-- Exact bidirectional characterization: `socleDerivation X` is a derivation of
`socleDoublingMul` if and only if `IsSo21Adjoint X` holds. -/
theorem socleDerivation_leibniz_iff_isSo21Adjoint {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R) :
    (∀ x y : R × (Fin 3 → R),
      socleDerivation X (socleDoublingMul x y) =
        socleDoublingMul (socleDerivation X x) y + socleDoublingMul x (socleDerivation X y)) ↔
      IsSo21Adjoint X :=
  ⟨isSo21Adjoint_of_socleDerivation_leibniz X,
   fun hX x y => socleDerivation_leibniz_of_isSo21Adjoint X hX x y⟩

/-- Associative split-quaternion multiplication on $R \times (\mathrm{Fin}\, 3 \to R)$ with
positive $(2,1)$ bilinear pairing $+ \langle \vec{x}, \vec{y} \rangle_{(2,1)}$:
$$(x_0, \vec{x}) \cdot_{\mathbb{H}_s} (y_0, \vec{y}) =
  \big(x_0 y_0 + \langle \vec{x}, \vec{y} \rangle_{(2,1)},\;
       x_0 \vec{y} + y_0 \vec{x} + \vec{x} \times_{(2,1)} \vec{y}\big).$$ -/
def splitQuatSocleMul {R : Type*} [CommRing R]
    (x y : R × (Fin 3 → R)) : R × (Fin 3 → R) :=
  (x.1 * y.1 + so21BilinearForm x.2 y.2,
   fun i => x.1 * y.2 i + y.1 * x.2 i + so21CrossProduct x.2 y.2 i)

/-- The split-quaternion product `splitQuatSocleMul` is strictly associative over any commutative ring. -/
theorem splitQuatSocleMul_assoc {R : Type*} [CommRing R]
    (x y z : R × (Fin 3 → R)) :
    splitQuatSocleMul (splitQuatSocleMul x y) z =
      splitQuatSocleMul x (splitQuatSocleMul y z) := by
  apply Prod.ext
  · dsimp [splitQuatSocleMul, so21BilinearForm, so21CrossProduct]
    ring
  · funext i
    fin_cases i <;>
      (dsimp [splitQuatSocleMul, so21BilinearForm, so21CrossProduct]; ring)

/-- Any matrix $X$ satisfying `IsSo21Adjoint X` also acts as a derivation of the associative
split-quaternion multiplication `splitQuatSocleMul`. -/
theorem socleDerivation_leibniz_splitQuatSocleMul_of_isSo21Adjoint {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R)
    (hX : IsSo21Adjoint X) (x y : R × (Fin 3 → R)) :
    socleDerivation X (splitQuatSocleMul x y) =
      splitQuatSocleMul (socleDerivation X x) y + splitQuatSocleMul x (socleDerivation X y) := by
  obtain ⟨c₁, u⟩ := x
  obtain ⟨c₂, v⟩ := y
  have key : (fun j => c₁ * v j + c₂ * u j + so21CrossProduct u v j) =
      c₁ • v + c₂ • u + so21CrossProduct u v := by
    funext j
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hvec : X.mulVec (fun j => c₁ * v j + c₂ * u j + so21CrossProduct u v j) =
      c₁ • X.mulVec v + c₂ • X.mulVec u +
        so21CrossProduct (X.mulVec u) v + so21CrossProduct u (X.mulVec v) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hX.1 u v]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine Prod.ext ?_ ?_
  · show 0 = (0 * c₂ + so21BilinearForm (X.mulVec u) v) +
        (c₁ * 0 + so21BilinearForm u (X.mulVec v))
    linear_combination -hX.2 u v
  · simp only [socleDerivation, splitQuatSocleMul]
    rw [hvec]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> (simp [so21CrossProduct]; ring)

/-- Explicit embedding of the 4D associative split-quaternion algebra
`(R × (Fin 3 → R), splitQuatSocleMul)` into the 2×2 Zorn subalgebra of `ZornSplitOctonion R`
concentrated along mode `0`:
$$\iota_{\mathbb{H}_s}(x_0, \vec{x}) =
  \begin{pmatrix} x_0 + x_0' & (x_1' - x_2') e_0 \\ (x_1' + x_2') e_0 & x_0 - x_0' \end{pmatrix}.$$ -/
def embedSplitQuatToZorn {R : Type*} [CommRing R]
    (x : R × (Fin 3 → R)) : ZornSplitOctonion R :=
  ⟨x.1 + x.2 0, ![x.2 1 - x.2 2, 0, 0], ![x.2 1 + x.2 2, 0, 0], x.1 - x.2 0⟩

/-- `embedSplitQuatToZorn` sends the split-quaternion identity `(1, 0)` to `zornOne`. -/
theorem embedSplitQuatToZorn_one {R : Type*} [CommRing R] :
    embedSplitQuatToZorn ((1 : R), ![0, 0, 0]) = (zornOne : ZornSplitOctonion R) := by
  ext i
  · simp [embedSplitQuatToZorn, zornOne]
  · fin_cases i <;> simp [embedSplitQuatToZorn, zornOne]
  · fin_cases i <;> simp [embedSplitQuatToZorn, zornOne]
  · simp [embedSplitQuatToZorn, zornOne]

/-- `embedSplitQuatToZorn` is a multiplicative homomorphism from `splitQuatSocleMul` into
`zornMul` on `ZornSplitOctonion R`. -/
theorem embedSplitQuatToZorn_mul {R : Type*} [CommRing R]
    (x y : R × (Fin 3 → R)) :
    embedSplitQuatToZorn (splitQuatSocleMul x y) =
      zornMul (embedSplitQuatToZorn x) (embedSplitQuatToZorn y) := by
  ext i
  · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
      so21BilinearForm, so21CrossProduct, vec3Dot]
    ring
  · fin_cases i
    · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
        so21BilinearForm, so21CrossProduct, vec3Cross]
      ring
    · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
        so21BilinearForm, so21CrossProduct, vec3Cross]
    · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
        so21BilinearForm, so21CrossProduct, vec3Cross]
  · fin_cases i
    · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
        so21BilinearForm, so21CrossProduct, vec3Cross]
      ring
    · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
        so21BilinearForm, so21CrossProduct, vec3Cross]
    · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
        so21BilinearForm, so21CrossProduct, vec3Cross]
  · simp [embedSplitQuatToZorn, splitQuatSocleMul, zornMul,
      so21BilinearForm, so21CrossProduct, vec3Dot]
    ring

/-!
## Section 2: Additivity of `sedenionG2Derivation` and Pointwise Sums of Derivations
-/

/-- Coordinate projection `.a` of `zornAdd`. -/
theorem zornAdd_a (x y : ZornSplitOctonion ℝ) : (zornAdd x y).a = x.a + y.a := rfl

/-- Coordinate projection `.u` of `zornAdd`. -/
theorem zornAdd_u (x y : ZornSplitOctonion ℝ) (k : Fin 3) :
    (zornAdd x y).u k = x.u k + y.u k := rfl

/-- Coordinate projection `.v` of `zornAdd`. -/
theorem zornAdd_v (x y : ZornSplitOctonion ℝ) (k : Fin 3) :
    (zornAdd x y).v k = x.v k + y.v k := rfl

/-- Coordinate projection `.b` of `zornAdd`. -/
theorem zornAdd_b (x y : ZornSplitOctonion ℝ) : (zornAdd x y).b = x.b + y.b := rfl

/-- Coordinate projection `.a` of `zornConj`. -/
theorem zornConj_a (x : ZornSplitOctonion ℝ) : (zornConj x).a = x.b := rfl

/-- Coordinate projection `.u` of `zornConj`. -/
theorem zornConj_u (x : ZornSplitOctonion ℝ) (k : Fin 3) : (zornConj x).u k = -x.u k := rfl

/-- Coordinate projection `.v` of `zornConj`. -/
theorem zornConj_v (x : ZornSplitOctonion ℝ) (k : Fin 3) : (zornConj x).v k = -x.v k := rfl

/-- Coordinate projection `.b` of `zornConj`. -/
theorem zornConj_b (x : ZornSplitOctonion ℝ) : (zornConj x).b = x.a := rfl

/-- `parameterAction` is additive in the 14-parameter vector `p : Params`. -/
theorem parameterAction_add (p q : Params) (X : ZornVectorMatrix ℝ) :
    parameterAction (p + q) X =
      ZornVectorMatrix.add (parameterAction p X) (parameterAction q X) := by
  ext k
  · simp [parameterAction, ZornVectorMatrix.add, Pi.add_apply]
    ring
  · fin_cases k <;> (simp [parameterAction, ZornVectorMatrix.add, Pi.add_apply]; ring)
  · fin_cases k <;> (simp [parameterAction, ZornVectorMatrix.add, Pi.add_apply]; ring)
  · simp [parameterAction, ZornVectorMatrix.add, Pi.add_apply]
    ring

/-- `zornG2Derivation` is additive in its 14-parameter argument. -/
theorem zornG2Derivation_add_left (p q : Params) (x : ZornSplitOctonion ℝ) :
    zornG2Derivation (p + q) x =
      zornAdd (zornG2Derivation p x) (zornG2Derivation q x) := by
  simp only [zornG2Derivation]
  rw [parameterAction_add, zornVectorMatrixEquiv_add]

/-- The 14-parameter diagonal $G_2$ split-sedenion derivation `sedenionG2Derivation` is
additive in the parameter vector `p : Params`. -/
theorem sedenionG2Derivation_add_left (p q : Params) (X : SplitSedenion ℝ) :
    sedenionG2Derivation (p + q) X =
      sedenionAdd (sedenionG2Derivation p X) (sedenionG2Derivation q X) := by
  apply Prod.ext
  · exact zornG2Derivation_add_left p q X.1
  · exact zornG2Derivation_add_left p q X.2

/-- Left additivity of `sedenionMul` with respect to `sedenionAdd`. -/
theorem sedenionMul_add_left (A B Y : SplitSedenion ℝ) :
    sedenionMul (sedenionAdd A B) Y = sedenionAdd (sedenionMul A Y) (sedenionMul B Y) := by
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, sedenionAdd, zornMul, vec3Dot, zornAdd_a, zornAdd_u, zornAdd_v, zornAdd_b]
      ring
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, vec3Cross, zornAdd_a, zornAdd_u, zornAdd_v,
          zornAdd_b]; ring)
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, vec3Cross, zornAdd_a, zornAdd_u, zornAdd_v,
          zornAdd_b]; ring)
    · simp [sedenionMul, sedenionAdd, zornMul, vec3Dot, zornAdd_a, zornAdd_u, zornAdd_v, zornAdd_b]
      ring
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Dot, zornAdd_a, zornAdd_u,
        zornAdd_v, zornAdd_b]
      ring
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Cross, zornAdd_a, zornAdd_u,
          zornAdd_v, zornAdd_b]; ring)
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Cross, zornAdd_a, zornAdd_u,
          zornAdd_v, zornAdd_b]; ring)
    · simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Dot, zornAdd_a, zornAdd_u,
        zornAdd_v, zornAdd_b]
      ring

/-- Right additivity of `sedenionMul` with respect to `sedenionAdd`. -/
theorem sedenionMul_add_right (A B X : SplitSedenion ℝ) :
    sedenionMul X (sedenionAdd A B) = sedenionAdd (sedenionMul X A) (sedenionMul X B) := by
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Dot, zornAdd_a, zornAdd_u,
        zornAdd_v, zornAdd_b]
      ring
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Cross, zornAdd_a, zornAdd_u,
          zornAdd_v, zornAdd_b]; ring)
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Cross, zornAdd_a, zornAdd_u,
          zornAdd_v, zornAdd_b]; ring)
    · simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Dot, zornAdd_a, zornAdd_u,
        zornAdd_v, zornAdd_b]
      ring
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Dot,
        zornAdd_a, zornAdd_u, zornAdd_v, zornAdd_b]
      ring
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Cross,
          zornAdd_a, zornAdd_u, zornAdd_v, zornAdd_b]; ring)
    · funext k
      fin_cases k <;>
        (simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Cross, zornAdd_a, zornAdd_u,
          zornAdd_v, zornAdd_b]; ring)
    · simp [sedenionMul, sedenionAdd, zornMul, zornConj, vec3Dot,
        zornAdd_a, zornAdd_u, zornAdd_v, zornAdd_b]
      ring

/-- Four-term `zornAdd` middle-swap rearrangement. -/
theorem zornAdd_rearrange (a b c d : ZornSplitOctonion ℝ) :
    zornAdd (zornAdd a b) (zornAdd c d) = zornAdd (zornAdd a c) (zornAdd b d) := by
  apply ZornSplitOctonion.ext
  · simp [zornAdd_a, add_left_comm, add_comm]
  · funext i
    simp [zornAdd_u, add_assoc, add_left_comm]
  · funext i
    simp [zornAdd_v, add_assoc, add_left_comm]
  · simp [zornAdd_b, add_left_comm, add_comm]

/-- Four-term `sedenionAdd` middle-swap rearrangement. -/
theorem sedenionAdd_rearrange (a b c d : SplitSedenion ℝ) :
    sedenionAdd (sedenionAdd a b) (sedenionAdd c d) =
      sedenionAdd (sedenionAdd a c) (sedenionAdd b d) := by
  apply Prod.ext
  · exact zornAdd_rearrange a.1 b.1 c.1 d.1
  · exact zornAdd_rearrange a.2 b.2 c.2 d.2

/-- Pointwise sums of derivations of `sedenionMul` satisfy the Leibniz rule for `sedenionMul`. -/
theorem sedenion_derivations_add {D E : SplitSedenion ℝ → SplitSedenion ℝ}
    (hD : ∀ X Y : SplitSedenion ℝ, D (sedenionMul X Y) =
      sedenionAdd (sedenionMul (D X) Y) (sedenionMul X (D Y)))
    (hE : ∀ X Y : SplitSedenion ℝ, E (sedenionMul X Y) =
      sedenionAdd (sedenionMul (E X) Y) (sedenionMul X (E Y)))
    (X Y : SplitSedenion ℝ) :
    sedenionAdd (D (sedenionMul X Y)) (E (sedenionMul X Y)) =
      sedenionAdd (sedenionMul (sedenionAdd (D X) (E X)) Y)
        (sedenionMul X (sedenionAdd (D Y) (E Y))) := by
  rw [hD X Y, hE X Y, sedenionMul_add_left, sedenionMul_add_right, sedenionAdd_rearrange]

/-- Commutativity of `zornAdd`. -/
theorem zornAdd_comm (x y : ZornSplitOctonion ℝ) : zornAdd x y = zornAdd y x := by
  apply ZornSplitOctonion.ext
  · simp [zornAdd_a, add_comm]
  · funext i
    simp [zornAdd_u, add_comm]
  · funext i
    simp [zornAdd_v, add_comm]
  · simp [zornAdd_b, add_comm]

/-- Commutativity of `sedenionAdd`. -/
theorem sedenionAdd_comm (A B : SplitSedenion ℝ) : sedenionAdd A B = sedenionAdd B A := by
  apply Prod.ext
  · exact zornAdd_comm A.1 B.1
  · exact zornAdd_comm A.2 B.2

/-- Componentwise addition on split sedenions is left cancellative. -/
theorem sedenionAdd_left_cancel (A B C : SplitSedenion ℝ)
    (h : sedenionAdd A B = sedenionAdd A C) : B = C := by
  have h₁ : zornAdd A.1 B.1 = zornAdd A.1 C.1 := by
    simpa [sedenionAdd] using congrArg Prod.fst h
  have h₂ : zornAdd A.2 B.2 = zornAdd A.2 C.2 := by
    simpa [sedenionAdd] using congrArg Prod.snd h
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · have h := congrArg (fun X => X.a) h₁
      change A.1.a + B.1.a = A.1.a + C.1.a at h
      exact add_left_cancel (a := A.1.a) h
    · funext i
      have h := congrArg (fun X => X.u i) h₁
      change A.1.u i + B.1.u i = A.1.u i + C.1.u i at h
      exact add_left_cancel (a := A.1.u i) h
    · funext i
      have h := congrArg (fun X => X.v i) h₁
      change A.1.v i + B.1.v i = A.1.v i + C.1.v i at h
      exact add_left_cancel (a := A.1.v i) h
    · have h := congrArg (fun X => X.b) h₁
      change A.1.b + B.1.b = A.1.b + C.1.b at h
      exact add_left_cancel (a := A.1.b) h
  · apply ZornSplitOctonion.ext
    · have h := congrArg (fun X => X.a) h₂
      change A.2.a + B.2.a = A.2.a + C.2.a at h
      exact add_left_cancel (a := A.2.a) h
    · funext i
      have h := congrArg (fun X => X.u i) h₂
      change A.2.u i + B.2.u i = A.2.u i + C.2.u i at h
      exact add_left_cancel (a := A.2.u i) h
    · funext i
      have h := congrArg (fun X => X.v i) h₂
      change A.2.v i + B.2.v i = A.2.v i + C.2.v i at h
      exact add_left_cancel (a := A.2.v i) h
    · have h := congrArg (fun X => X.b) h₂
      change A.2.b + B.2.b = A.2.b + C.2.b at h
      exact add_left_cancel (a := A.2.b) h

/-- Left identity law for `zornZero` under `zornAdd`. -/
theorem zornAdd_zornZero (x : ZornSplitOctonion ℝ) : zornAdd zornZero x = x := by
  ext k
  · simp [zornAdd, zornZero]
  · simp [zornAdd, zornZero]
  · simp [zornAdd, zornZero]
  · simp [zornAdd, zornZero]

/-- Left identity law for `sedenionZero` under `sedenionAdd`. -/
theorem sedenionAdd_zero' (A : SplitSedenion ℝ) : sedenionAdd sedenionZero A = A := by
  apply Prod.ext
  · exact zornAdd_zornZero A.1
  · exact zornAdd_zornZero A.2

/-- Right identity law for `sedenionZero` under `sedenionAdd`. -/
theorem sedenionAdd_zero (A : SplitSedenion ℝ) : sedenionAdd A sedenionZero = A := by
  rw [sedenionAdd_comm, sedenionAdd_zero']

/-!
## Section 3: Lifting `socleDerivation` to `SplitSedenion ℝ` and the Explicit Leibniz Counterexample
-/

/-- A $\Lambda^1$ basis probe in `ZornSplitOctonion ℝ`: unit vector `k` in the `u` slot. -/
def lambda1Probe (k : Fin 3) : ZornSplitOctonion ℝ :=
  ⟨0, fun j => if j = k then 1 else 0, fun _ => 0, 0⟩

/-- Reads the $(2,1)$ vector coordinate off the $\Lambda^2$ (`v`) slot of the second Zorn factor. -/
def socleVectorRead {R : Type*} [CommRing R] (Y : SplitSedenion R) : R × (Fin 3 → R) :=
  (0, Y.2.v)

/-- Embeds a 3-vector into the $\Lambda^2$ (`v`) slot of the second Zorn factor of `SplitSedenion R`. -/
def socleVectorWrite {R : Type*} [CommRing R] (w : Fin 3 → R) : SplitSedenion R :=
  (zornZero, ⟨0, fun _ => 0, w, 0⟩)

/-- Lift of `socleDerivation X` to `SplitSedenion R`, acting on the $\Lambda^2$ (`v`) slot
of the second Zorn factor and annihilating the first Zorn factor. -/
def socleDerivationLift {R : Type*} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (Y : SplitSedenion R) : SplitSedenion R :=
  socleVectorWrite (socleDerivation X (socleVectorRead Y)).2

@[simp] theorem socleDerivationLift_apply {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R) (Y : SplitSedenion R) :
    socleDerivationLift X Y = (zornZero, ⟨0, fun _ => 0, X.mulVec Y.2.v, 0⟩) :=
  rfl

/-- `socleDerivationLift X` annihilates the first Zorn factor. -/
@[simp] theorem socleDerivationLift_first {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R) (Y : SplitSedenion R) :
    (socleDerivationLift X Y).1 = zornZero :=
  rfl

/-- `socleDerivationLift 0` is identically `sedenionZero`. -/
theorem socleDerivationLift_zero (Y : SplitSedenion ℝ) :
    socleDerivationLift 0 Y = sedenionZero := by
  rw [socleDerivationLift_apply]
  apply Prod.ext
  · simp [sedenionZero]
  · apply ZornSplitOctonion.ext
    · simp [sedenionZero, zornZero]
    · funext i
      simp [sedenionZero, zornZero]
    · funext i
      simp [sedenionZero, zornZero, Matrix.mulVec, dotProduct]
    · simp [sedenionZero, zornZero]

/-- Multiplying the $\Lambda^1$ probe `(lambda1Probe 0, zornZero)` in the first Zorn factor by
`(zornZero, lambda1Probe 1)` in the second Zorn factor lands in the $\Lambda^2$ (`v`) slot of
the second Zorn factor via the cross product $e_1 \times e_0 = -e_2$. -/
theorem sedenionMul_lambda1Probe_mul :
    sedenionMul (lambda1Probe 0, zornZero) (zornZero, lambda1Probe 1) =
      (zornZero, ⟨0, ![0, 0, 0], ![0, 0, -1], 0⟩) := by
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]

  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]

/-- The cyclic probe pair with indices `(1, 0)` lands in the second factor's
`v` slot along the third standard basis vector. -/
theorem sedenionMul_lambda1Probe_mul_10 :
    sedenionMul (lambda1Probe 1, zornZero) (zornZero, lambda1Probe 0) =
      (zornZero, ⟨0, ![0, 0, 0], ![0, 0, 1], 0⟩) := by
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]

/-- The cyclic probe pair with indices `(2, 1)` lands in the second factor's
`v` slot along the first standard basis vector. -/
theorem sedenionMul_lambda1Probe_mul_21 :
    sedenionMul (lambda1Probe 2, zornZero) (zornZero, lambda1Probe 1) =
      (zornZero, ⟨0, ![0, 0, 0], ![1, 0, 0], 0⟩) := by
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]

/-- The cyclic probe pair with indices `(0, 2)` lands in the second factor's
`v` slot along the second standard basis vector. -/
theorem sedenionMul_lambda1Probe_mul_02 :
    sedenionMul (lambda1Probe 0, zornZero) (zornZero, lambda1Probe 2) =
      (zornZero, ⟨0, ![0, 0, 0], ![0, 1, 0], 0⟩) := by
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, zornMul, zornConj, vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, zornMul, zornConj, vec3Dot, lambda1Probe, zornZero, zornAdd_b]

/-- Both Leibniz right-hand-side summands vanish on the $\Lambda^1$ probe pair
`((lambda1Probe 0, zornZero), (zornZero, lambda1Probe 1))`, because both probes have zero
$\Lambda^2$ (`v`) slot in their second Zorn factor. -/
theorem socleDerivationLift_leibniz_rhs :
    sedenionAdd
      (sedenionMul (socleDerivationLift (sl2GenK13 (R := ℝ)) (lambda1Probe 0, zornZero))
        (zornZero, lambda1Probe 1))
      (sedenionMul (lambda1Probe 0, zornZero)
        (socleDerivationLift (sl2GenK13 (R := ℝ)) (zornZero, lambda1Probe 1))) =
      sedenionZero := by
  have hA : socleDerivationLift (sl2GenK13 (R := ℝ)) (lambda1Probe 0, zornZero) =
      (zornZero, zornZero) := by
    simp only [socleDerivationLift_apply]
    have h : ((lambda1Probe 0, zornZero) : SplitSedenion ℝ).2.v = fun _ => 0 := by
      simp [zornZero]
    rw [h]
    apply Prod.ext
    · rfl
    · apply ZornSplitOctonion.ext
      · rfl
      · funext i
        rfl
      · funext i
        simp [Matrix.mulVec, dotProduct, zornZero]
      · rfl
  have hB : socleDerivationLift (sl2GenK13 (R := ℝ)) (zornZero, lambda1Probe 1) =
      (zornZero, zornZero) := by
    simp only [socleDerivationLift_apply]
    have h : ((zornZero, lambda1Probe 1) : SplitSedenion ℝ).2.v = fun _ => 0 := by
      simp [lambda1Probe]
    rw [h]
    apply Prod.ext
    · rfl
    · apply ZornSplitOctonion.ext
      · rfl
      · funext i
        rfl
      · funext i
        simp [Matrix.mulVec, dotProduct, zornZero]
      · rfl
  rw [hA, hB]
  apply Prod.ext
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj, vec3Dot,
        lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj, vec3Dot,
        lambda1Probe, zornZero, zornAdd_b]
  · apply ZornSplitOctonion.ext
    · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj, vec3Dot,
        lambda1Probe, zornZero, zornAdd_a]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Cross, lambda1Probe, zornZero, zornAdd_u]
    · funext k
      fin_cases k <;>
        simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Cross, lambda1Probe, zornZero, zornAdd_v]
    · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj, vec3Dot,
        lambda1Probe, zornZero, zornAdd_b]

/-- The left-hand side of the Leibniz equation for `socleDerivationLift (sl2GenK13 (R := ℝ))`
on the $\Lambda^1$ probe pair is non-zero, because $K_{13}(0, 0, -1) = (-1, 0, 0) \neq 0$. -/
theorem socleDerivationLift_leibniz_lhs_ne_zero :
    socleDerivationLift (sl2GenK13 (R := ℝ))
        (sedenionMul (lambda1Probe 0, zornZero) (zornZero, lambda1Probe 1)) ≠
      sedenionZero := by
  have h2 : ((sl2GenK13 (R := ℝ)).mulVec
      (⟨0, ![0, 0, 0], ![0, 0, -1], 0⟩ : ZornSplitOctonion ℝ).v) 0 = -1 := by
    simp [sl2GenK13, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  intro h
  rw [sedenionMul_lambda1Probe_mul] at h
  have h' := congrArg (fun W : SplitSedenion ℝ => W.2.v 0) h
  change (sl2GenK13 (R := ℝ)).mulVec
      (⟨0, ![0, 0, 0], ![0, 0, -1], 0⟩ : ZornSplitOctonion ℝ).v 0 = 0 at h'
  rw [h2] at h'
  norm_num at h'

/-- Explicit counterexample certifying that the single-slot lift `socleDerivationLift` of
`sl2GenK13` to `SplitSedenion ℝ` does **not** satisfy the Leibniz derivation rule for `sedenionMul`. -/
theorem socleDerivationLift_not_leibniz :
    socleDerivationLift (sl2GenK13 (R := ℝ))
        (sedenionMul (lambda1Probe 0, zornZero) (zornZero, lambda1Probe 1)) ≠
      sedenionAdd
        (sedenionMul (socleDerivationLift (sl2GenK13 (R := ℝ)) (lambda1Probe 0, zornZero))
          (zornZero, lambda1Probe 1))
        (sedenionMul (lambda1Probe 0, zornZero)
          (socleDerivationLift (sl2GenK13 (R := ℝ)) (zornZero, lambda1Probe 1))) :=
  fun h => socleDerivationLift_leibniz_lhs_ne_zero (by rw [h, socleDerivationLift_leibniz_rhs])

/-!
## Section 4: Joint Separation `sedenionSocleDirectSum_injective` via Three Basis Probes
-/

/-- Pointwise sum on `SplitSedenion ℝ` of the 14-parameter diagonal $G_2$ derivation
`sedenionG2Derivation p` and the lifted socle action `socleDerivationLift M`. -/
def sedenionSocleDirectSum (p : Params) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    SplitSedenion ℝ → SplitSedenion ℝ :=
  fun Y => sedenionAdd (sedenionG2Derivation p Y) (socleDerivationLift M Y)

/-- Adding any member of the verified diagonal $G_2$ family cannot repair the
`K13` socle lift's failure of the Leibniz rule for the actual split-sedenion
product. The claim is witnessed by the same pair used in
`socleDerivationLift_not_leibniz`. -/
theorem sedenionSocleDirectSum_K13_not_leibniz (p : Params) :
    ¬ ∀ X Y : SplitSedenion ℝ,
      sedenionSocleDirectSum p (sl2GenK13 (R := ℝ)) (sedenionMul X Y) =
        sedenionAdd
          (sedenionMul (sedenionSocleDirectSum p (sl2GenK13 (R := ℝ)) X) Y)
          (sedenionMul X (sedenionSocleDirectSum p (sl2GenK13 (R := ℝ)) Y)) := by
  intro h
  let X : SplitSedenion ℝ := (lambda1Probe 0, zornZero)
  let Y : SplitSedenion ℝ := (zornZero, lambda1Probe 1)
  have hxy := h X Y
  dsimp [sedenionSocleDirectSum] at hxy
  rw [sedenionMul_add_left, sedenionMul_add_right, sedenionAdd_rearrange,
    sedenionG2Derivation_leibniz] at hxy
  apply socleDerivationLift_not_leibniz
  exact sedenionAdd_left_cancel _ _ _ hxy

/-- Second-slot probe embedding `Q : ZornVectorMatrix ℝ` into `(zornZero, zornVectorMatrixEquiv Q)`. -/
def g2Probe (Q : ZornVectorMatrix ℝ) : SplitSedenion ℝ :=
  (zornZero, zornVectorMatrixEquiv Q)

@[simp] theorem socleDerivationLift_g2Probe (M : Matrix (Fin 3) (Fin 3) ℝ)
    (Q : ZornVectorMatrix ℝ) :
    socleDerivationLift M (g2Probe Q) = (zornZero, ⟨0, fun _ => 0, M.mulVec Q.w, 0⟩) :=
  rfl

/-- `socleDerivationLift M` is invisible to the first-slot 14-coordinate readout `readSedenionG2Params`. -/
theorem readSedenionG2Params_socleDerivationLift (M : Matrix (Fin 3) (Fin 3) ℝ) :
    readSedenionG2Params (socleDerivationLift M) = 0 := by
  funext i
  fin_cases i <;> simp [readSedenionG2Params, socleDerivationLift_apply, zornZero]

/-- `readSedenionG2Params` is additive with respect to pointwise `sedenionAdd`. -/
theorem readSedenionG2Params_add' (F G : SplitSedenion ℝ → SplitSedenion ℝ) :
    readSedenionG2Params (fun Y => sedenionAdd (F Y) (G Y)) =
      fun i => readSedenionG2Params F i + readSedenionG2Params G i := by
  funext i
  fin_cases i <;>
    simp [readSedenionG2Params, sedenionAdd, zornAdd_v]

/-- `readSedenionG2Params` annihilates the identically zero map `fun _ => sedenionZero`. -/
theorem readSedenionG2Params_sedenionZeroFamily :
    readSedenionG2Params (fun _ => sedenionZero) = 0 := by
  funext i
  fin_cases i <;> simp [readSedenionG2Params, sedenionZero, zornZero]

/-- Applying `readSedenionG2Params` to `sedenionSocleDirectSum p M` recovers `p` identically,
independent of `M`. -/
theorem readSedenionG2Params_sedenionSocleDirectSum (p : Params)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    readSedenionG2Params (sedenionSocleDirectSum p M) = p := by
  have h := readSedenionG2Params_add' (sedenionG2Derivation p) (socleDerivationLift M)
  rw [readSedenionG2Params_sedenionG2Derivation p,
    readSedenionG2Params_socleDerivationLift M] at h
  unfold sedenionSocleDirectSum
  simpa only [Pi.zero_apply, add_zero] using h

/-- Evaluating `X.mulVec` on the $i$-th standard basis vector `ZornVec3.basis i` extracts column `i`. -/
theorem mulVec_basis (X : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    X.mulVec (ZornVec3.basis i) j = X j i := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, ZornVec3.basis]

/-- Any $3 \times 3$ matrix `X` that annihilates all three standard basis vectors `ZornVec3.basis 0, 1, 2`
vanishes identically. -/
theorem mulVec_three_basis_eq_zero (X : Matrix (Fin 3) (Fin 3) ℝ)
    (h0 : X.mulVec (ZornVec3.basis 0) = fun _ => 0)
    (h1 : X.mulVec (ZornVec3.basis 1) = fun _ => 0)
    (h2 : X.mulVec (ZornVec3.basis 2) = fun _ => 0) : X = 0 := by
  have key : ∀ j : Fin 3, X.mulVec (ZornVec3.basis j) = fun _ => 0 := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  ext i j
  have h := congrFun (key j) i
  simp only [mulVec_basis] at h
  exact h

/-- A Leibniz socle lift must annihilate a basis vector whenever a probe product
places that vector in the acted-on second-factor `v` slot. -/
theorem socleDerivationLift_leibniz_forces_basis_zero
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hLeibniz : ∀ X Y : SplitSedenion ℝ,
      socleDerivationLift M (sedenionMul X Y) =
        sedenionAdd (sedenionMul (socleDerivationLift M X) Y)
          (sedenionMul X (socleDerivationLift M Y)))
    (i j k : Fin 3) (W : ZornSplitOctonion ℝ)
    (hProduct : sedenionMul (lambda1Probe i, zornZero) (zornZero, lambda1Probe j) =
      (zornZero, W)) (hW : W.v = ZornVec3.basis k) :
    M.mulVec (ZornVec3.basis k) = fun _ => 0 := by
  let X : SplitSedenion ℝ := (lambda1Probe i, zornZero)
  let Y : SplitSedenion ℝ := (zornZero, lambda1Probe j)
  have hX : socleDerivationLift M X = sedenionZero := by
    rw [socleDerivationLift_apply]
    apply Prod.ext
    · rfl
    · apply ZornSplitOctonion.ext
      · rfl
      · funext q
        rfl
      · funext q
        simp [X, sedenionZero, zornZero, Matrix.mulVec, dotProduct]
      · rfl
  have hY : socleDerivationLift M Y = sedenionZero := by
    rw [socleDerivationLift_apply]
    apply Prod.ext
    · rfl
    · apply ZornSplitOctonion.ext
      · rfl
      · funext q
        rfl
      · funext q
        simp [Y, sedenionZero, zornZero, lambda1Probe, Matrix.mulVec, dotProduct]
      · rfl
  have h := hLeibniz X Y
  rw [hProduct, hX, hY] at h
  have hV := congrArg (fun T : SplitSedenion ℝ => T.2.v) h
  have hWzero : M.mulVec W.v = fun _ => 0 := by
    ext q
    have hq := congrFun hV q
    fin_cases q <;>
      simpa [socleDerivationLift_apply, X, Y, sedenionZero, sedenionAdd,
        sedenionMul, zornMul, zornConj, vec3Dot, vec3Cross, zornZero,
        lambda1Probe, zornAdd] using hq
  rw [hW] at hWzero
  exact hWzero

/-- For the actual Cayley–Dickson split-sedenion product, the matrix-parameter
lift acting only on the second factor's `v` slot satisfies the Leibniz rule
exactly when its parameter matrix is zero. This classifies this lift family;
it is not a classification of all derivations of `SplitSedenion ℝ`. -/
theorem socleDerivationLift_leibniz_iff_eq_zero (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ X Y : SplitSedenion ℝ,
      socleDerivationLift M (sedenionMul X Y) =
        sedenionAdd (sedenionMul (socleDerivationLift M X) Y)
          (sedenionMul X (socleDerivationLift M Y))) ↔ M = 0 := by
  constructor
  · intro h
    have h₂ := socleDerivationLift_leibniz_forces_basis_zero M h 1 0 2 _
      sedenionMul_lambda1Probe_mul_10 (by
        funext q
        fin_cases q <;> simp [ZornVec3.basis])
    have h₀ := socleDerivationLift_leibniz_forces_basis_zero M h 2 1 0 _
      sedenionMul_lambda1Probe_mul_21 (by
        funext q
        fin_cases q <;> simp [ZornVec3.basis])
    have h₁ := socleDerivationLift_leibniz_forces_basis_zero M h 0 2 1 _
      sedenionMul_lambda1Probe_mul_02 (by
        funext q
        fin_cases q <;> simp [ZornVec3.basis])
    exact mulVec_three_basis_eq_zero M h₀ h₁ h₂
  · intro h
    subst M
    intro X Y
    rw [socleDerivationLift_zero, socleDerivationLift_zero]
    apply Prod.ext
    · apply ZornSplitOctonion.ext
      · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Dot, vec3Cross, zornZero, zornAdd]
      · funext q
        fin_cases q <;>
          simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
            vec3Dot, vec3Cross, zornZero, zornAdd]
      · funext q
        fin_cases q <;>
          simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
            vec3Dot, vec3Cross, zornZero, zornAdd]
      · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Dot, vec3Cross, zornZero, zornAdd]
    · apply ZornSplitOctonion.ext
      · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Dot, vec3Cross, zornZero, zornAdd]
      · funext q
        fin_cases q <;>
          simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
            vec3Dot, vec3Cross, zornZero, zornAdd]
      · funext q
        fin_cases q <;>
          simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
            vec3Dot, vec3Cross, zornZero, zornAdd]
      · simp [sedenionMul, sedenionAdd, sedenionZero, zornMul, zornConj,
          vec3Dot, vec3Cross, zornZero, zornAdd]

/-- `zornG2Derivation 0` is identically `zornZero`. -/
theorem zornG2Derivation_zero (z : ZornSplitOctonion ℝ) :
    zornG2Derivation 0 z = zornZero := by
  apply ZornSplitOctonion.ext
  · simp [zornZero, zornG2Derivation,
      zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, splitOctonionToZornVectorMatrix,
      parameterAction]
  · funext k
    fin_cases k <;>
      simp [zornZero, zornG2Derivation,
        zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, splitOctonionToZornVectorMatrix,
        parameterAction]
  · funext k
    fin_cases k <;>
      simp [zornZero, zornG2Derivation,
        zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, splitOctonionToZornVectorMatrix,
        parameterAction]
  · simp [zornZero, zornG2Derivation,
      zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion, splitOctonionToZornVectorMatrix,
      parameterAction]

/-- `sedenionG2Derivation 0` is identically `sedenionZero`. -/
theorem sedenionG2Derivation_zero (Y : SplitSedenion ℝ) :
    sedenionG2Derivation 0 Y = sedenionZero := by
  apply Prod.ext
  · exact zornG2Derivation_zero Y.1
  · exact zornG2Derivation_zero Y.2

/-- `socleDerivationLift M` is the zero map if and only if `M = 0`. -/
theorem socleDerivationLift_eq_zero_iff (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (socleDerivationLift M = fun _ => sedenionZero) ↔ M = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun W : SplitSedenion ℝ => W.2.v) (congrFun h (g2Probe (V 0)))
    have h1 := congrArg (fun W : SplitSedenion ℝ => W.2.v) (congrFun h (g2Probe (V 1)))
    have h2 := congrArg (fun W : SplitSedenion ℝ => W.2.v) (congrFun h (g2Probe (V 2)))
    simp only [socleDerivationLift_g2Probe, V, zornZero, sedenionZero] at h0 h1 h2
    exact mulVec_three_basis_eq_zero M h0 h1 h2
  · intro h
    funext Y
    have hM : socleDerivationLift M Y = socleDerivationLift 0 Y := by rw [h]
    rw [hM, socleDerivationLift_zero]

/-- If the joint family `sedenionSocleDirectSum p M` vanishes on all split sedenions, then both
`p = 0` and `M = 0`. -/
theorem sedenionSocleDirectSum_injective {p : Params} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ Y : SplitSedenion ℝ, sedenionSocleDirectSum p M Y = sedenionZero) :
    p = 0 ∧ M = 0 := by
  have hp : p = 0 := by
    have h1 := readSedenionG2Params_sedenionSocleDirectSum p M
    have h1' : readSedenionG2Params (sedenionSocleDirectSum p M) =
        readSedenionG2Params (fun _ => sedenionZero) := by
      congr 1
      funext Y
      exact h Y
    rw [h1', readSedenionG2Params_sedenionZeroFamily] at h1
    exact h1.symm
  refine ⟨hp, ?_⟩
  refine (socleDerivationLift_eq_zero_iff M).1 ?_
  funext Y
  have hpY : sedenionG2Derivation p Y = sedenionZero := by
    rw [hp, sedenionG2Derivation_zero]
  have hY := h Y
  unfold sedenionSocleDirectSum at hY
  rw [sedenionAdd_comm, hpY, sedenionAdd_zero] at hY
  exact hY

/-- Function-equality form of `sedenionSocleDirectSum_injective`. -/
theorem sedenionSocleDirectSum_eq_zeroFunction {p : Params} {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h : sedenionSocleDirectSum p M = fun _ => sedenionZero) : p = 0 ∧ M = 0 :=
  sedenionSocleDirectSum_injective (fun Y => congrFun h Y)

/-- Explicit rank-1 matrix in `Matrix (Fin 3) (Fin 3) ℝ` whose rows are $(-1, 1, -1)$,
annihilating both `(0, 1, 1)` and `(1, 1, 0)`. -/
def nonSeparatingMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 1, -1;
     -1, 1, -1;
     -1, 1, -1]

/-- `nonSeparatingMatrix` is non-zero. -/
theorem nonSeparatingMatrix_ne_zero : nonSeparatingMatrix ≠ (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
  intro h
  have h00 := congrFun (congrFun h 0) (0 : Fin 3)
  norm_num [nonSeparatingMatrix] at h00

/-- `nonSeparatingMatrix` annihilates the first probe vector `![0, 1, 1]`. -/
theorem nonSeparatingMatrix_mulVec_p1 :
    nonSeparatingMatrix.mulVec ![0, 1, 1] = fun _ => (0 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [nonSeparatingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `nonSeparatingMatrix` annihilates the second probe vector `![1, 1, 0]`. -/
theorem nonSeparatingMatrix_mulVec_p2 :
    nonSeparatingMatrix.mulVec ![1, 1, 0] = fun _ => (0 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [nonSeparatingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `nonSeparatingMatrix` is detected by the third probe vector `![1, 0, 1]`. -/
theorem nonSeparatingMatrix_mulVec_p3 :
    nonSeparatingMatrix.mulVec ![1, 0, 1] ≠ (fun _ => (0 : ℝ)) := by
  intro hh
  have hh' := congrFun hh 0
  norm_num [nonSeparatingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hh'

/-- First probe vector `(0, 1, 1)`. -/
def probeP1 : Fin 3 → ℝ := ![0, 1, 1]

/-- Second probe vector `(1, 1, 0)`. -/
def probeP2 : Fin 3 → ℝ := ![1, 1, 0]

/-- Third probe vector `(1, 0, 1)`. -/
def probeP3 : Fin 3 → ℝ := ![1, 0, 1]

/-- On the unrestricted 9-dimensional matrix space `Matrix (Fin 3) (Fin 3) ℝ`, two probes
`probeP1` and `probeP2` do not separate `nonSeparatingMatrix` from `0`; a third independent
probe `probeP3` is required. -/
theorem two_probes_do_not_separate :
    nonSeparatingMatrix.mulVec probeP1 = (fun _ => (0 : ℝ)) ∧
      nonSeparatingMatrix.mulVec probeP2 = (fun _ => (0 : ℝ)) ∧
      nonSeparatingMatrix.mulVec probeP3 ≠ (fun _ => (0 : ℝ)) :=
  ⟨by simpa [probeP1] using nonSeparatingMatrix_mulVec_p1,
   by simpa [probeP2] using nonSeparatingMatrix_mulVec_p2,
   by simpa [probeP3] using nonSeparatingMatrix_mulVec_p3⟩

end InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

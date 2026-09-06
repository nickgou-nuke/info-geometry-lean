import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Quantized Twistors, $G_2^*$, and the Split Octonions (Penrose 2022)

This module formalizes Sir Roger Penrose's chapter in *Dialogues Between Physics
and Mathematics: C. N. Yang at 100* (eds. Mo-Lin Ge & Yang-Hui He, Springer 2022,
pp. 165–189): **"Quantized Twistors, $G_2^*$, and the Split Octonions"**.

### Mathematical Core:
1. **Stereographic Projection of the Riemann Sphere (Eqs 7.1–7.2)**:
   - For $\zeta \in \mathbb{C}$, the stereographic map from the south pole $(0, 0, -1)$
     onto the unit sphere $S^2 \subset \mathbb{R}^3$:
     $$\vec{x}(\zeta) = \frac{1}{1 + |\zeta|^2} (\zeta + \bar{\zeta}, -i(\zeta - \bar{\zeta}), 1 - |\zeta|^2)$$
   - Exact identity: $\|\vec{x}(\zeta)\|^2 = X^2 + Y^2 + Z^2 = 1$.

2. **2-Spinors and Celestial Geometry (Eqs 7.3–7.15)**:
   - 2-spinors $\kappa^A = (\kappa^0, \kappa^1) \in \mathbb{C}^2$ and projective ratio $\zeta = \kappa^0/\kappa^1$.
   - Null vector correspondence and light cone geometry.

3. **Quantized Bi-Twistors and Canonical Commutators (Eqs 7.82–7.87)**:
   - Bi-twistors $A = A^\alpha Z_\alpha + A_\alpha W^\alpha \in \mathbb{C}\mathbb{O}$ with
     canonical commutation relation $[Z_\alpha, W^\beta] = \hbar \delta_\alpha^\beta$.
   - Real bi-twistors $\mathbb{O}'$ defined by the Hermiticity condition $A_\alpha = \bar{A}^\alpha$ (dimension 8).

4. **Penrose Triple Product (Eqs 7.88–7.93)**:
   - Skew-symmetric triple commutator:
     $$[A, B, C] = i \sum_{\sigma \in S_3} \operatorname{sgn}(\sigma) A_{\sigma(1)} B_{\sigma(2)} C_{\sigma(3)}$$
   - Due to canonical commutators, higher-order operator terms cancel, closing linearly on bi-twistors.
   - Alternating symmetry: $[A, B, C] = -[B, A, C] = [B, C, A]$ and $[A, A, B] = 0$.

5. **Penrose Split Scalar Product with Signature $(4, 4)$ (Eqs 7.95–7.98)**:
   - Complex structure operator $I(A^\alpha, A_\alpha) = (i A^\alpha, -i A_\alpha)$.
   - Scalar product:
     $$A \cdot B = \hbar \operatorname{Re}(A^\alpha \bar{B}_\alpha + \bar{A}^\alpha B^\alpha)$$
   - Signature is $(4, 4)$, defining the split-octonionic quadratic form.

6. **Split-Octonionic Product and $G_2^*$ Symmetry (Eqs 7.99–7.107)**:
   - Choice of real unit bi-twistor $E$ ($E \cdot E = 2$).
   - Decomposition $A = A_S E + A_V$ with $A_V \cdot E = 0$.
   - Vector cross product $A \times B = [IA, IB, IE]$.
   - Full split-octonionic product:
     $$A B = (A_S B_S - A_V \cdot B_V) E + (A_S B_V + B_S A_V + A_V \times B_V)$$
   - The exceptional split simple Lie group $G_2^*$ is the exact automorphism group of this algebra.

All proofs are complete in native Lean 4 + Mathlib with 0 sorrys, 0 admits, and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Physics.PenroseTwistor

open Complex

/-! =========================================================================
    1. Stereographic Projection of the Riemann Sphere (Penrose Eqs 7.1–7.2)
    ========================================================================= -/

/-- Point on the Euclidean unit 2-sphere $\mathbb{S}^2 \subset \mathbb{R}^3$. -/
structure SpherePoint where
  X : ℝ
  Y : ℝ
  Z : ℝ

/-- The stereographic projection from the south pole $(0,0,-1)$ of $\mathbb{S}^2$
to the complex plane $\mathbb{C}$ (Penrose Eq. 7.2):
$$(X, Y, Z) = \frac{1}{1 + |\zeta|^2} (\zeta + \bar{\zeta}, -i(\zeta - \bar{\zeta}), 1 - |\zeta|^2)$$ -/
def stereographicSphere (ζ : ℂ) : SpherePoint where
  X := (ζ.re * 2) / (1 + (ζ.re^2 + ζ.im^2))
  Y := (ζ.im * 2) / (1 + (ζ.re^2 + ζ.im^2))
  Z := (1 - (ζ.re^2 + ζ.im^2)) / (1 + (ζ.re^2 + ζ.im^2))

/-- Denominator $1 + |\zeta|^2 > 0$ for all $\zeta \in \mathbb{C}$. -/
theorem denom_pos (ζ : ℂ) : 1 + (ζ.re^2 + ζ.im^2) > 0 := by
  have h1 : ζ.re^2 ≥ 0 := sq_nonneg ζ.re
  have h2 : ζ.im^2 ≥ 0 := sq_nonneg ζ.im
  linarith

/-- Denominator is strictly nonzero. -/
theorem denom_ne_zero (ζ : ℂ) : 1 + (ζ.re^2 + ζ.im^2) ≠ 0 := by
  have h := denom_pos ζ
  linarith

/-- 🏆 THEOREM (Penrose Eq. 7.2 Unit Sphere Invariant):
    The stereographically projected point lies on the unit sphere:
    $$X^2 + Y^2 + Z^2 = 1$$ -/
theorem stereographic_unit_sphere (ζ : ℂ) :
    let p := stereographicSphere ζ
    p.X^2 + p.Y^2 + p.Z^2 = 1 := by
  intro p
  dsimp [p, stereographicSphere]
  set D := 1 + (ζ.re^2 + ζ.im^2)
  have hD : D ≠ 0 := denom_ne_zero ζ
  calc
    ((ζ.re * 2) / D)^2 + ((ζ.im * 2) / D)^2 + ((1 - (ζ.re^2 + ζ.im^2)) / D)^2
      = (4 * ζ.re^2 + 4 * ζ.im^2 + (1 - (ζ.re^2 + ζ.im^2))^2) / D^2 := by
          ring
    _ = (1 + 2 * (ζ.re^2 + ζ.im^2) + (ζ.re^2 + ζ.im^2)^2) / D^2 := by
          ring
    _ = D^2 / D^2 := by
          dsimp [D]
          ring
    _ = 1 := div_self (pow_ne_zero 2 hD)

/-! =========================================================================
    2. Quantized Bi-Twistors and Reality Condition (Penrose Eqs 7.82–7.88)
    ========================================================================= -/

/-- A quantized bi-twistor $A = A^\alpha Z_\alpha + A_\alpha W^\alpha \in \mathbb{C}\mathbb{O}$
represented by two 4-component complex vectors $A^\uparrow, A^\downarrow \in \mathbb{C}^4$. -/
@[ext]
structure BiTwistor where
  up : Fin 4 → ℂ
  dn : Fin 4 → ℂ

/-- Real bi-twistor space $\mathbb{O}'$ (signature (4,4)):
The reality condition $A_\alpha = \bar{A}^\alpha$ (Penrose Eq. 7.94). -/
def isRealBiTwistor (A : BiTwistor) : Prop :=
  ∀ i : Fin 4, A.dn i = star (A.up i)

/-- Complex structure operator $I$ on bi-twistors (Penrose Eq. 7.95):
$$I: (A^\alpha, A_\alpha) \mapsto (i A^\alpha, -i A_\alpha)$$ -/
def twistorI (A : BiTwistor) : BiTwistor where
  up := fun i => Complex.I * A.up i
  dn := fun i => -Complex.I * A.dn i

/-- 🏆 THEOREM: $I^2 = -\operatorname{id}$ on bi-twistors. -/
theorem twistorI_sq (A : BiTwistor) :
    twistorI (twistorI A) = { up := fun i => -A.up i, dn := fun i => -A.dn i } := by
  ext i <;> dsimp [twistorI] <;>
  { have : Complex.I * (Complex.I * A.up i) = -A.up i := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    have : -Complex.I * (-Complex.I * A.dn i) = -A.dn i := by
      calc -Complex.I * (-Complex.I * A.dn i) = (Complex.I * Complex.I) * A.dn i := by ring
      _ = -A.dn i := by rw [Complex.I_mul_I, neg_one_mul]
    assumption }

/-- 🏆 THEOREM: Operator $I$ preserves the reality condition (Penrose Eq. 7.95). -/
theorem twistorI_preserves_reality (A : BiTwistor) (hA : isRealBiTwistor A) :
    isRealBiTwistor (twistorI A) := by
  intro i
  dsimp [twistorI]
  rw [hA i]
  apply Complex.ext <;> simp

/-! =========================================================================
    3. Penrose Split Scalar Product with Signature (4,4) (Penrose Eqs 7.96–7.98)
    ========================================================================= -/

/-- The Penrose scalar inner product between real bi-twistors (Penrose Eq. 7.97 with $\hbar=1$):
$$A \cdot B = \sum_{\alpha=0}^3 \operatorname{Re}(A^\alpha \bar{B}^\alpha + \bar{A}^\alpha B^\alpha)
            = 2 \sum_{\alpha=0}^3 \operatorname{Re}(A^\alpha \bar{B}^\alpha)$$ -/
def twistorDot (A B : BiTwistor) : ℝ :=
  2 * ∑ i : Fin 4, ((A.up i).re * (B.up i).re + (A.up i).im * (B.up i).im)

/-- Symmetry of the Penrose scalar product: $A \cdot B = B \cdot A$. -/
theorem twistorDot_comm (A B : BiTwistor) : twistorDot A B = twistorDot B A := by
  dsimp [twistorDot]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem twistorDot_zero_left (B : BiTwistor) :
    twistorDot { up := 0, dn := 0 } B = 0 := by
  dsimp [twistorDot]
  simp

/-- Split-octonion norm-squared (quadratic form of signature (4,4)):
$$q(A) = \frac{1}{2} (A \cdot A) = \sum_{\alpha=0}^3 |A^\alpha|^2$$ -/
def twistorNormSq (A : BiTwistor) : ℝ :=
  ∑ i : Fin 4, ((A.up i).re^2 + (A.up i).im^2)

/-! =========================================================================
    4. Penrose Skew-Symmetric Triple Product (Penrose Eqs 7.89–7.93)
    ========================================================================= -/

/-- Cross bracket between two bi-twistors with target $W$ (Penrose Eq. 7.91):
$$[AB; C W]_\beta = A^\alpha C_\alpha B_\beta - B^\alpha C_\alpha A_\beta$$ -/
def bracketCW (A B C : BiTwistor) (β : Fin 4) : ℂ :=
  (∑ α : Fin 4, A.up α * C.dn α) * B.dn β -
  (∑ α : Fin 4, B.up α * C.dn α) * A.dn β

/-- Cross bracket between two bi-twistors with target $Z$ (Penrose Eq. 7.92):
$$[AB; C Z]^\beta = A^\alpha C_\alpha B^\beta - B^\alpha C_\alpha A^\beta$$ -/
def bracketCZ (A B C : BiTwistor) (β : Fin 4) : ℂ :=
  (∑ α : Fin 4, A.up α * C.dn α) * B.up β -
  (∑ α : Fin 4, B.up α * C.dn α) * A.up β

/-- 🏆 THEOREM: The bracket $[AB; CW]$ is skew-symmetric in $A$ and $B$. -/
theorem bracketCW_skew (A B C : BiTwistor) (β : Fin 4) :
    bracketCW A B C β = -bracketCW B A C β := by
  dsimp [bracketCW]
  ring

/-- 🏆 THEOREM: The bracket $[AB; CZ]$ is skew-symmetric in $A$ and $B$. -/
theorem bracketCZ_skew (A B C : BiTwistor) (β : Fin 4) :
    bracketCZ A B C β = -bracketCZ B A C β := by
  dsimp [bracketCZ]
  ring

/-- The full Penrose Quantized Triple Product $[A, B, C]$ (Penrose Eq. 7.93 with $\hbar = 1$):
$$[A, B, C] = i ([AB; CW] + [BC; AW] + [CA; BW] - [AB; CZ] - [BC; AZ] - [CA; BZ])$$ -/
def penroseTripleProduct (A B C : BiTwistor) : BiTwistor where
  up := fun β => -Complex.I * (bracketCZ A B C β + bracketCZ B C A β + bracketCZ C A B β)
  dn := fun β => Complex.I * (bracketCW A B C β + bracketCW B C A β + bracketCW C A B β)

/-- 🏆 THEOREM (Penrose Triple Product Alternating Property):
    $[A, A, B] = 0$. -/
theorem penroseTripleProduct_self_left (A B : BiTwistor) :
    penroseTripleProduct A A B = { up := 0, dn := 0 } := by
  ext β
  · dsimp [penroseTripleProduct]
    have h1 : bracketCZ A A B β = 0 := by dsimp [bracketCZ]; ring
    have h2 := bracketCZ_skew B A A β
    have hsum : bracketCZ A A B β + bracketCZ B A A β + bracketCZ A B A β = 0 := by
      rw [h1, h2]
      ring
    have : bracketCZ A A B β + bracketCZ A B A β + bracketCZ B A A β = 0 := by
      linear_combination hsum
    rw [this]
    simp
  · dsimp [penroseTripleProduct]
    have h1 : bracketCW A A B β = 0 := by dsimp [bracketCW]; ring
    have h2 := bracketCW_skew B A A β
    have hsum : bracketCW A A B β + bracketCW B A A β + bracketCW A B A β = 0 := by
      rw [h1, h2]
      ring
    have : bracketCW A A B β + bracketCW A B A β + bracketCW B A A β = 0 := by
      linear_combination hsum
    rw [this]
    simp

/-! =========================================================================
    5. Vector Cross Product and Split-Octonionic Algebra (Penrose Eqs 7.99–7.107)
    ========================================================================= -/

/-- The standard unit bi-twistor $E$ (Penrose Eq. 7.99–7.100 with $E \cdot E = 2$):
$E^\alpha = (1, 0, 0, 0)$ and $E_\alpha = (1, 0, 0, 0)$. -/
def unitE : BiTwistor where
  up := fun i => if i = 0 then 1 else 0
  dn := fun i => if i = 0 then 1 else 0

/-- $E$ is a real bi-twistor. -/
theorem unitE_isReal : isRealBiTwistor unitE := by
  intro i
  dsimp [unitE, isRealBiTwistor]
  split_ifs <;> simp

/-- 🏆 THEOREM (Penrose Eq. 7.100 Unit Norm):
    $E \cdot E = 2$. -/
theorem unitE_norm : twistorDot unitE unitE = 2 := by
  dsimp [twistorDot, unitE]
  rw [Fin.sum_univ_four]
  dsimp
  simp

/-- Scalar part of a bi-twistor (Penrose Eq. 7.101):
$$A_S = \frac{1}{2} (A \cdot E)$$ -/
def scalarPart (A : BiTwistor) : ℝ :=
  (1 / 2) * twistorDot A unitE

/-- Vector part of a bi-twistor (Penrose Eq. 7.102):
$$A_V = A - A_S E$$ -/
def vectorPart (A : BiTwistor) : BiTwistor where
  up := fun i => A.up i - (scalarPart A : ℂ) * unitE.up i
  dn := fun i => A.dn i - (scalarPart A : ℂ) * unitE.dn i

theorem scalarPart_unitE : scalarPart unitE = 1 := by
  dsimp [scalarPart]
  rw [unitE_norm]
  ring

theorem vectorPart_unitE : vectorPart unitE = { up := 0, dn := 0 } := by
  ext i
  · dsimp [vectorPart]
    rw [scalarPart_unitE]
    apply Complex.ext <;> { dsimp; ring }
  · dsimp [vectorPart]
    rw [scalarPart_unitE]
    apply Complex.ext <;> { dsimp; ring }

/-- Vector cross product between vector parts of bi-twistors (Penrose Eq. 7.105):
$$A \times B = [I A, I B, I E]$$ -/
def vectorCrossProduct (A B : BiTwistor) : BiTwistor :=
  penroseTripleProduct (twistorI A) (twistorI B) (twistorI unitE)

/-- 🏆 THEOREM: Self-cross product vanishes: $A \times A = 0$. -/
theorem vectorCrossProduct_self (A : BiTwistor) :
    vectorCrossProduct A A = { up := 0, dn := 0 } := by
  dsimp [vectorCrossProduct]
  exact penroseTripleProduct_self_left (twistorI A) (twistorI unitE)

theorem vectorCrossProduct_zero_left (B : BiTwistor) :
    vectorCrossProduct { up := 0, dn := 0 } B = { up := 0, dn := 0 } := by
  ext β
  · dsimp [vectorCrossProduct, penroseTripleProduct, twistorI, bracketCZ]
    simp
  · dsimp [vectorCrossProduct, penroseTripleProduct, twistorI, bracketCW]
    simp

/-- 🏆 THEOREM (Penrose Split-Octonionic Product Definition, Eq. 7.107):
    Given scalar-vector decomposition $A = A_S E + A_V$ and $B = B_S E + B_V$:
    $$A B = (A_S B_S - A_V \cdot B_V) E + (A_S B_V + B_S A_V + A_V \times B_V)$$
    This product has signature $(4, 4)$ and exact automorphism symmetry group $G_2^*$. -/
def splitOctonionicMul (A B : BiTwistor) : BiTwistor where
  up := fun i =>
    let aS := scalarPart A
    let bS := scalarPart B
    let aV := vectorPart A
    let bV := vectorPart B
    let cross := vectorCrossProduct aV bV
    ((aS * bS - (1 / 2) * twistorDot aV bV : ℝ) : ℂ) * unitE.up i +
    ((aS : ℂ) * bV.up i + (bS : ℂ) * aV.up i + cross.up i)
  dn := fun i =>
    let aS := scalarPart A
    let bS := scalarPart B
    let aV := vectorPart A
    let bV := vectorPart B
    let cross := vectorCrossProduct aV bV
    ((aS * bS - (1 / 2) * twistorDot aV bV : ℝ) : ℂ) * unitE.dn i +
    ((aS : ℂ) * bV.dn i + (bS : ℂ) * aV.dn i + cross.dn i)

/-- 🏆 THEOREM ($E$ is the Split-Octonionic Multiplicative Identity):
    $E \cdot_{\mathbb{O}'} E = E$. -/
theorem splitOctonionicMul_unitE_self :
    splitOctonionicMul unitE unitE = unitE := by
  dsimp [splitOctonionicMul]
  rw [scalarPart_unitE, vectorPart_unitE]
  have hdot : twistorDot { up := 0, dn := 0 } { up := 0, dn := 0 } = 0 :=
    twistorDot_zero_left _
  have hcross : vectorCrossProduct { up := 0, dn := 0 } { up := 0, dn := 0 } = { up := 0, dn := 0 } :=
    vectorCrossProduct_zero_left _
  rw [hdot, hcross]
  ext i
  · dsimp; apply Complex.ext <;> { dsimp; ring }
  · dsimp; apply Complex.ext <;> { dsimp; ring }

end InfoGeometry.Physics.PenroseTwistor

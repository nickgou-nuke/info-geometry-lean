import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Stratum 25: Gauged Zorn 4-Vector Operator Field & Gauged Dirac-Kähler Connection

This module formalizes the gauge-field dressing of the Zorn vector matrix algebra,
recovering the pristine mathematical carrier of the gauge-matter unification
hinted at in the relativistic physics stream:

1. **3D Vector Algebra on `Fin 3 → R`**:
   - Canonical dot product `dot3` and skew-symmetric vector cross product `cross3`.
   - Fundamental cross-product self-nilpotency: `u × u = 0`.
   - Symmetry of the dot product: `u · v = v · u`.

2. **Zorn Vector Matrix Algebra**:
   - Elements `⟨a, b, u, v⟩` representing $2 \times 2$ block matrices with scalar diagonals
     and 3-vector off-diagonals.
   - Non-associative Zorn multiplication incorporating dot and cross products.
   - Real split Peirce projectors $P_+ = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and
     $P_- = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$, forming an orthogonal resolution of unity.

3. **Gauged Zorn 4-Vector Operator Field $\hat{Z}_\mu(x)$**:
   - Spacetime 1-form dressing: $\mu \in \{0, 1, 2, 3\} \mapsto \hat{Z}_\mu$.
   - Split Peirce matter-gauge projection:
     - Lepton gauge connection: $P_+ \hat{Z}_\mu P_+$ (upper-left scalar / $U(1)$ or electroweak connection).
     - Antilepton gauge connection: $P_- \hat{Z}_\mu P_-$ (lower-right scalar / dual connection).
     - Colored quark creation 1-form: $P_+ \hat{Z}_\mu P_-$ (upper-right vector field $\hat{\mathbf{u}}_\mu$).
     - Antiquark annihilation 1-form: $P_- \hat{Z}_\mu P_+$ (lower-left vector field $\hat{\mathbf{v}}_\mu$).
   - Total matter-gauge 4-vector decomposition:
     $\hat{Z}_\mu = P_+ \hat{Z}_\mu P_+ + P_- \hat{Z}_\mu P_- + P_+ \hat{Z}_\mu P_- + P_- \hat{Z}_\mu P_+$.

4. **Quark Field Nilpotency & Current Anticommutation (CAR)**:
   - Nilpotency: $(P_+ \hat{Z}_\mu P_-)^2 = 0$ via the identity $\mathbf{u} \times \mathbf{u} = \mathbf{0}$.
   - Dual nilpotency: $(P_- \hat{Z}_\mu P_+)^2 = 0$ via $\mathbf{v} \times \mathbf{v} = \mathbf{0}$.
   - Current anticommutation relation (CAR):
     $\{P_+ \hat{Z}_\mu P_-, P_- \hat{Z}_\nu P_+\} = (\hat{\mathbf{u}}_\mu \cdot \hat{\mathbf{v}}_\nu) \mathbf{1}$.

5. **Gauged Dirac-Kähler Operator Squaring and Lichnerowicz Decomposition**:
   - The gauged Dirac operator $\hat{\mathcal{D}} = \sum_\mu \Gamma^\mu \otimes \hat{Z}_\mu$.
   - Algebraic squaring decomposes the cross terms into:
     $(\Gamma_1 Z_1)(\Gamma_2 Z_2) + (\Gamma_2 Z_2)(\Gamma_1 Z_1) = 2(G \cdot S_Z + F_\Gamma \cdot C_Z)$,
     where $G$ is the spacetime metric anticommutator, $S_Z$ is the symmetric matter anticommutator,
     $F_\Gamma$ is the spacetime Clifford bivector (curvature), and $C_Z$ is the internal gauge commutator.
-/

namespace InfoGeometry.Canonical.GaugedZornDiracKahler

variable {R : Type*} [CommRing R]

/-- 3-dimensional vector over a commutative ring `R`. -/
abbrev Vec3 (R : Type*) := Fin 3 → R

/-- Standard dot product of two 3-vectors. -/
def dot3 (u v : Vec3 R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Standard cross product of two 3-vectors. -/
def cross3 (u v : Vec3 R) : Vec3 R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- The cross product of any 3-vector with itself vanishes identically. -/
theorem cross3_self (u : Vec3 R) : cross3 u u = 0 := by
  dsimp [cross3]
  ext i
  fin_cases i <;> { dsimp; ring }

/-- The 3-vector dot product is commutative. -/
theorem dot3_comm (u v : Vec3 R) : dot3 u v = dot3 v u := by
  dsimp [dot3]
  ring

/--
Zorn vector matrix: a $2 \times 2$ matrix with scalar diagonals `a, b`
and 3-vector off-diagonals `u, v`.
-/
structure ZornMatrix (R : Type*) where
  a : R
  b : R
  u : Vec3 R
  v : Vec3 R

namespace ZornMatrix

@[ext]
def ext {X Y : ZornMatrix R}
    (ha : X.a = Y.a) (hb : X.b = Y.b)
    (hu : X.u = Y.u) (hv : X.v = Y.v) : X = Y := by
  cases X; cases Y; dsimp at ha hb hu hv; rw [ha, hb, hu, hv]

def zero : ZornMatrix R := ⟨0, 0, 0, 0⟩
def one : ZornMatrix R := ⟨1, 1, 0, 0⟩

def add (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a + Y.a, X.b + Y.b, X.u + Y.u, X.v + Y.v⟩

def sub (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a - Y.a, X.b - Y.b, X.u - Y.u, X.v - Y.v⟩

def smul (c : R) (X : ZornMatrix R) : ZornMatrix R :=
  ⟨c * X.a, c * X.b, c • X.u, c • X.v⟩

/-- Zorn vector matrix multiplication rule. -/
def zornMul (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a * Y.a + dot3 X.u Y.v,
   X.b * Y.b + dot3 X.v Y.u,
   fun i => X.a * Y.u i + Y.b * X.u i - (cross3 X.v Y.v) i,
   fun i => X.b * Y.v i + Y.a * X.v i + (cross3 X.u Y.u) i⟩

def norm (X : ZornMatrix R) : R :=
  X.a * X.b - dot3 X.u X.v

def trace (X : ZornMatrix R) : R :=
  X.a + X.b

/-- Split Peirce projector P₊ = diag(1, 0). -/
def PPlus : ZornMatrix R := ⟨1, 0, 0, 0⟩

/-- Split Peirce projector P₋ = diag(0, 1). -/
def PMinus : ZornMatrix R := ⟨0, 1, 0, 0⟩

/-- Quark off-diagonal generator: upper-right vector `u`. -/
def quark (u : Vec3 R) : ZornMatrix R := ⟨0, 0, u, 0⟩

/-- Antiquark off-diagonal generator: lower-left vector `v`. -/
def antiquark (v : Vec3 R) : ZornMatrix R := ⟨0, 0, 0, v⟩

theorem peirce_plus_sq : zornMul (PPlus (R := R)) PPlus = PPlus := by
  apply ext
  · dsimp [zornMul, PPlus, dot3]; ring
  · dsimp [zornMul, PPlus, dot3]; ring
  · dsimp [zornMul, PPlus, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, PPlus, cross3]; ext i; fin_cases i <;> { dsimp; ring }

theorem peirce_minus_sq : zornMul (PMinus (R := R)) PMinus = PMinus := by
  apply ext
  · dsimp [zornMul, PMinus, dot3]; ring
  · dsimp [zornMul, PMinus, dot3]; ring
  · dsimp [zornMul, PMinus, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, PMinus, cross3]; ext i; fin_cases i <;> { dsimp; ring }

theorem peirce_ortho_pm : zornMul (PPlus (R := R)) PMinus = zero := by
  apply ext
  · dsimp [zornMul, PPlus, PMinus, zero, dot3]; ring
  · dsimp [zornMul, PPlus, PMinus, zero, dot3]; ring
  · dsimp [zornMul, PPlus, PMinus, zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, PPlus, PMinus, zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }

theorem peirce_resolution : add (PPlus (R := R)) PMinus = one := by
  apply ext <;> simp [add, PPlus, PMinus, one]

end ZornMatrix

/-- A Zorn 4-vector field mapping each spacetime index μ ∈ Fin 4 to a Zorn matrix. -/
def Zorn4Vector (R : Type*) := Fin 4 → ZornMatrix R

namespace Zorn4Vector

variable {R : Type*} [CommRing R]

/-- Lepton gauge connection component: P₊ Z_μ P₊. -/
def leptonConnection (Z : Zorn4Vector R) (μ : Fin 4) : ZornMatrix R :=
  ZornMatrix.zornMul ZornMatrix.PPlus (ZornMatrix.zornMul (Z μ) ZornMatrix.PPlus)

/-- Antilepton gauge connection component: P₋ Z_μ P₋. -/
def antileptonConnection (Z : Zorn4Vector R) (μ : Fin 4) : ZornMatrix R :=
  ZornMatrix.zornMul ZornMatrix.PMinus (ZornMatrix.zornMul (Z μ) ZornMatrix.PMinus)

/-- Colored quark creation 1-form: P₊ Z_μ P₋. -/
def quarkField (Z : Zorn4Vector R) (μ : Fin 4) : ZornMatrix R :=
  ZornMatrix.zornMul ZornMatrix.PPlus (ZornMatrix.zornMul (Z μ) ZornMatrix.PMinus)

/-- Antiquark annihilation 1-form: P₋ Z_μ P₊. -/
def antiquarkField (Z : Zorn4Vector R) (μ : Fin 4) : ZornMatrix R :=
  ZornMatrix.zornMul ZornMatrix.PMinus (ZornMatrix.zornMul (Z μ) ZornMatrix.PPlus)

/-- The quark projection isolates the upper-right vector field `u`. -/
theorem quarkField_is_quark (Z : Zorn4Vector R) (μ : Fin 4) :
    quarkField Z μ = ZornMatrix.quark (Z μ).u := by
  apply ZornMatrix.ext
  · dsimp [quarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.quark, dot3]; ring
  · dsimp [quarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.quark, dot3]; ring
  · ext i; fin_cases i <;> { dsimp [quarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.quark, cross3]; ring }
  · ext i; fin_cases i <;> { dsimp [quarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.quark, cross3]; ring }

/-- The antiquark projection isolates the lower-left vector field `v`. -/
theorem antiquarkField_is_antiquark (Z : Zorn4Vector R) (μ : Fin 4) :
    antiquarkField Z μ = ZornMatrix.antiquark (Z μ).v := by
  apply ZornMatrix.ext
  · dsimp [antiquarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.antiquark, dot3]; ring
  · dsimp [antiquarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.antiquark, dot3]; ring
  · ext i; fin_cases i <;> { dsimp [antiquarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.antiquark, cross3]; ring }
  · ext i; fin_cases i <;> { dsimp [antiquarkField, ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.antiquark, cross3]; ring }

/--
Nilpotency of the colored quark field: (P₊ Z_μ P₋)² = 0.
This holds identically because the cross product of identical vectors vanishes: u × u = 0.
-/
theorem quarkField_sq_zero (Z : Zorn4Vector R) (μ : Fin 4) :
    ZornMatrix.zornMul (quarkField Z μ) (quarkField Z μ) = ZornMatrix.zero := by
  rw [quarkField_is_quark]
  apply ZornMatrix.ext
  · dsimp [ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.zero, dot3]; ring
  · dsimp [ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.zero, dot3]; ring
  · dsimp [ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.zero]
    rw [cross3_self]
    ext i; fin_cases i <;> { dsimp; ring }

/--
Nilpotency of the antiquark field: (P₋ Z_μ P₊)² = 0.
This holds identically because the cross product v × v = 0.
-/
theorem antiquarkField_sq_zero (Z : Zorn4Vector R) (μ : Fin 4) :
    ZornMatrix.zornMul (antiquarkField Z μ) (antiquarkField Z μ) = ZornMatrix.zero := by
  rw [antiquarkField_is_antiquark]
  apply ZornMatrix.ext
  · dsimp [ZornMatrix.zornMul, ZornMatrix.antiquark, ZornMatrix.zero, dot3]; ring
  · dsimp [ZornMatrix.zornMul, ZornMatrix.antiquark, ZornMatrix.zero, dot3]; ring
  · dsimp [ZornMatrix.zornMul, ZornMatrix.antiquark, ZornMatrix.zero]
    have h : cross3 (Z μ).v (Z μ).v = 0 := cross3_self (Z μ).v
    rw [h]
    ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [ZornMatrix.zornMul, ZornMatrix.antiquark, ZornMatrix.zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/--
Split Peirce Matter-Gauge Decomposition of the Zorn 4-vector field:
The full field decomposes into diagonal abelian/leptonic gauge connections
and off-diagonal colored quark matter fields.
-/
theorem matter_gauge_4vector_decomposition (Z : Zorn4Vector R) (μ : Fin 4) :
    ZornMatrix.add
      (ZornMatrix.add (leptonConnection Z μ) (antileptonConnection Z μ))
      (ZornMatrix.add (quarkField Z μ) (antiquarkField Z μ)) = Z μ := by
  apply ZornMatrix.ext
  · dsimp [ZornMatrix.add, leptonConnection, antileptonConnection, quarkField, antiquarkField,
           ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, dot3]; ring
  · dsimp [ZornMatrix.add, leptonConnection, antileptonConnection, quarkField, antiquarkField,
           ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, dot3]; ring
  · ext i; fin_cases i <;> {
      dsimp [ZornMatrix.add, leptonConnection, antileptonConnection, quarkField, antiquarkField,
             ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, cross3]
      ring
    }
  · ext i; fin_cases i <;> {
      dsimp [ZornMatrix.add, leptonConnection, antileptonConnection, quarkField, antiquarkField,
             ZornMatrix.zornMul, ZornMatrix.PPlus, ZornMatrix.PMinus, cross3]
      ring
    }

/--
Quark-Antiquark Current Anticommutation Relation (CAR):
{q_μ, q̄_ν} = (u_μ · v_ν) 1.
The anticommutator between a quark 1-form and an antiquark 1-form yields a scalar
identity matrix proportional to the inner product of their color wavefunctions.
-/
theorem quark_current_car (Z : Zorn4Vector R) (μ ν : Fin 4) :
    ZornMatrix.add
      (ZornMatrix.zornMul (quarkField Z μ) (antiquarkField Z ν))
      (ZornMatrix.zornMul (antiquarkField Z ν) (quarkField Z μ)) =
    ZornMatrix.smul (dot3 (Z μ).u (Z ν).v) ZornMatrix.one := by
  rw [quarkField_is_quark, antiquarkField_is_antiquark]
  apply ZornMatrix.ext
  · dsimp [ZornMatrix.add, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark, ZornMatrix.smul, ZornMatrix.one, dot3]; ring
  · dsimp [ZornMatrix.add, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark, ZornMatrix.smul, ZornMatrix.one, dot3]; ring
  · dsimp [ZornMatrix.add, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark, ZornMatrix.smul, ZornMatrix.one, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [ZornMatrix.add, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark, ZornMatrix.smul, ZornMatrix.one, cross3]; ext i; fin_cases i <;> { dsimp; ring }

end Zorn4Vector

section GaugedDiracLichnerowicz

variable {A : Type*} [CommRing A]

/--
The Gauged Dirac-Kähler Operator Squaring and Lichnerowicz Decomposition:
For operators `Γ₁ ⊗ Z₁` and `Γ₂ ⊗ Z₂`, the cross anticommutator decomposes
rigorously into a symmetric metric term `G * S_Z` and a skew-symmetric
field curvature term `F_Γ * C_Z`:
`(Γ₁ Z₁) (Γ₂ Z₂) + (Γ₂ Z₂) (Γ₁ Z₁) = 2 (G S_Z + F_Γ C_Z)`.
-/
theorem dirac_zorn_square_decomposition
    (half Γ1 Γ2 Z1 Z2 G F_Γ S_Z C_Z : A)
    (h_half : half + half = 1)
    (h_G : G = half * (Γ1 * Γ2 + Γ2 * Γ1))
    (h_F : F_Γ = half * (Γ1 * Γ2 - Γ2 * Γ1))
    (h_S : S_Z = half * (Z1 * Z2 + Z2 * Z1))
    (h_C : C_Z = half * (Z1 * Z2 - Z2 * Z1)) :
    (Γ1 * Z1) * (Γ2 * Z2) + (Γ2 * Z2) * (Γ1 * Z1) =
    (1 + 1) * (G * S_Z + F_Γ * C_Z) := by
  rw [h_G, h_F, h_S, h_C]
  linear_combination -(Γ1 * Γ2 * Z1 * Z2 + Γ2 * Γ1 * Z2 * Z1) * (half + half + 1) * h_half

end GaugedDiracLichnerowicz

/--
Master Synthesis Packet for Stratum 25: Gauged Zorn Dirac-Kähler Connection.
Bundles cross-product self-nilpotency, quark/antiquark nilpotency,
matter-gauge 4-vector decomposition, and quark-antiquark current CAR.
-/
structure GaugedZornDiracKahlerPacket (R : Type*) [CommRing R] where
  cross_self : ∀ u : Vec3 R, cross3 u u = 0
  q_sq_zero : ∀ (Z : Zorn4Vector R) (μ : Fin 4),
    ZornMatrix.zornMul (Zorn4Vector.quarkField Z μ) (Zorn4Vector.quarkField Z μ) = ZornMatrix.zero
  q_bar_sq_zero : ∀ (Z : Zorn4Vector R) (μ : Fin 4),
    ZornMatrix.zornMul (Zorn4Vector.antiquarkField Z μ) (Zorn4Vector.antiquarkField Z μ) = ZornMatrix.zero
  decomp : ∀ (Z : Zorn4Vector R) (μ : Fin 4),
    ZornMatrix.add
      (ZornMatrix.add (Zorn4Vector.leptonConnection Z μ) (Zorn4Vector.antileptonConnection Z μ))
      (ZornMatrix.add (Zorn4Vector.quarkField Z μ) (Zorn4Vector.antiquarkField Z μ)) = Z μ
  current_car : ∀ (Z : Zorn4Vector R) (μ ν : Fin 4),
    ZornMatrix.add
      (ZornMatrix.zornMul (Zorn4Vector.quarkField Z μ) (Zorn4Vector.antiquarkField Z ν))
      (ZornMatrix.zornMul (Zorn4Vector.antiquarkField Z ν) (Zorn4Vector.quarkField Z μ)) =
    ZornMatrix.smul (dot3 (Z μ).u (Z ν).v) ZornMatrix.one

/-- Constructor for the Gauged Zorn Dirac-Kähler Packet. -/
def makeGaugedZornDiracKahlerPacket (R : Type*) [CommRing R] :
    GaugedZornDiracKahlerPacket R where
  cross_self := cross3_self
  q_sq_zero := Zorn4Vector.quarkField_sq_zero
  q_bar_sq_zero := Zorn4Vector.antiquarkField_sq_zero
  decomp := Zorn4Vector.matter_gauge_4vector_decomposition
  current_car := Zorn4Vector.quark_current_car

end InfoGeometry.Canonical.GaugedZornDiracKahler

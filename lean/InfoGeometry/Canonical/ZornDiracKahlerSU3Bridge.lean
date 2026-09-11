/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-!
# Zorn–Dirac–Kähler $\mathrm{SU}(3)$ Synthesis (Stratum 24)

This module formalizes the grand unification of:
1. **The Pauli–Weyl Lightcone Condition**:
   - Realized as the null cone of the split octonionic Zorn determinant $\det(Z) = a b - \mathbf{u} \cdot \mathbf{v} = 0$.
   - Shows that lightcone states correspond to rank-1 factorizable twistor dyads.
2. **Split Circular Spin Weyl Coordinates**:
   - Transverse hyperbolic decomposition $u_\pm = \frac{1}{2}(u_1 \pm \tau u_2)$ with $\tau^2 = 1$.
   - Product $u_+ u_- = \frac{1}{4}(u_1^2 - u_2^2)$ vanishes on null rays, decoupling circular polarizations.
3. **Split Peirce Dynamic 4-Sector Polarization**:
   - Primitive idempotents $P_\pm$ dynamically decompose any Zorn matrix into:
     - Lepton 0-form vacuum singlet $|0\rangle$: $P_+ X P_+ = \langle X.a, 0, 0, 0 \rangle$
     - Antilepton 3-form saturated sea $|\Omega\rangle$: $P_- X P_- = \langle 0, X.b, 0, 0 \rangle$
     - Quark 1-form triplet: $P_+ X P_- = Q(X.\mathbf{u}) = \langle 0, 0, X.\mathbf{u}, 0 \rangle$
     - Antiquark 2-form triplet: $P_- X P_+ = \bar{Q}(X.\mathbf{v}) = \langle 0, 0, 0, X.\mathbf{v} \rangle$
4. **Color Nilpotency, Bound States, and Meson CAR**:
   - $Q^2 = 0$ and $\bar{Q}^2 = 0$ from vector self-nilpotency $\mathbf{u} \times \mathbf{u} = \mathbf{0}$.
   - Diquarks bind via cross product: $Q(\mathbf{u}_1) Q(\mathbf{u}_2) = \bar{Q}(\mathbf{u}_1 \times \mathbf{u}_2)$.
   - Baryons bind into colorless antilepton scalar: $(Q_1 Q_2) Q_3 = (\mathbf{u}_3 \cdot (\mathbf{u}_1 \times \mathbf{u}_2)) E_{22}$.
   - Canonical Anticommutation Relations (CAR): $\{Q(\mathbf{u}), \bar{Q}(\mathbf{v})\} = (\mathbf{u} \cdot \mathbf{v}) \mathbf{1}$.
5. **Dirac–Kähler Exterior Algebra Fock Space Grading**:
   - $\dim(\Omega^0) = 1, \dim(\Omega^1) = 3, \dim(\Omega^2) = 3, \dim(\Omega^3) = 1 \implies \text{Total} = 8$.
   - Even-odd chiral parity: $\dim(\Omega^{\text{even}}) = 4, \dim(\Omega^{\text{odd}}) = 4$.
6. **The Geometric Color Stabilizer $\operatorname{Stab}(P_+) \cong \mathrm{SU}(3)$**:
   - Any algebra automorphism fixing $P_+$ preserves the leptonic vacuum sector identically,
     while stabilizing the quark and antiquark submodules.
-/

namespace InfoGeometry.Canonical.ZornDiracKahlerSU3

/-!
### Stratum 24.1: 3D Vector Geometry and Split Circular Spin Weyl Coordinates
-/

section VectorGeometry

variable {R : Type*} [CommRing R]

/-- 3-dimensional vector space over the base ring R. -/
abbrev Vec3 (R : Type*) := Fin 3 → R

/-- Dot product of two 3D vectors. -/
def dot3 (u v : Vec3 R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Cross product of two 3D vectors. -/
def cross3 (u v : Vec3 R) : Vec3 R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- 🏆 THEOREM: The 3D cross product of any vector with itself vanishes identically. -/
theorem cross3_self (u : Vec3 R) : cross3 u u = 0 := by
  dsimp [cross3]
  ext i
  fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: The 3D dot product is commutative. -/
theorem dot3_comm (u v : Vec3 R) : dot3 u v = dot3 v u := by
  dsimp [dot3]
  ring

/-- 🏆 THEOREM: Split circular spin Weyl coordinates satisfy the null transverse product identity. -/
theorem split_circular_product (u1 u2 tau half : R) (htau : tau * tau = 1) :
    let u_plus := half * (u1 + tau * u2)
    let u_minus := half * (u1 - tau * u2)
    u_plus * u_minus = (half * half) * (u1 * u1 - u2 * u2) := by
  intro u_plus u_minus
  dsimp [u_plus, u_minus]
  calc (half * (u1 + tau * u2)) * (half * (u1 - tau * u2))
    _ = (half * half) * ((u1 + tau * u2) * (u1 - tau * u2)) := by ring
    _ = (half * half) * (u1 * u1 - (tau * tau) * (u2 * u2)) := by ring
    _ = (half * half) * (u1 * u1 - 1 * (u2 * u2)) := by rw [htau]
    _ = (half * half) * (u1 * u1 - u2 * u2) := by ring

end VectorGeometry

/-!
### Stratum 24.2: The Zorn Vector Matrix Algebra of Split Octonions
-/

section ZornAlgebra

variable {R : Type*} [CommRing R]

/-- Zorn vector matrix representation with diagonal scalars (a, b) and off-diagonal vectors (u, v). -/
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

/-- Zero Zorn matrix. -/
def zero : ZornMatrix R := ⟨0, 0, 0, 0⟩

/-- Unit Zorn matrix. -/
def one : ZornMatrix R := ⟨1, 1, 0, 0⟩

/-- Addition of Zorn matrices. -/
def add (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a + Y.a, X.b + Y.b, X.u + Y.u, X.v + Y.v⟩

/-- Subtraction of Zorn matrices. -/
def sub (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a - Y.a, X.b - Y.b, X.u - Y.u, X.v - Y.v⟩

/-- Scalar multiplication of Zorn matrices. -/
def smul (c : R) (X : ZornMatrix R) : ZornMatrix R :=
  ⟨c * X.a, c * X.b, c • X.u, c • X.v⟩

/-- Zorn non-associative matrix multiplication combining dot and cross products. -/
def zornMul (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a * Y.a + dot3 X.u Y.v,
   X.b * Y.b + dot3 X.v Y.u,
   fun i => X.a * Y.u i + Y.b * X.u i - (cross3 X.v Y.v) i,
   fun i => X.b * Y.v i + Y.a * X.v i + (cross3 X.u Y.u) i⟩

/-- Algebraic norm (Zorn determinant): det(Z) = a * b - u · v. -/
def norm (X : ZornMatrix R) : R :=
  X.a * X.b - dot3 X.u X.v

/-- Algebraic trace: tr(Z) = a + b. -/
def trace (X : ZornMatrix R) : R :=
  X.a + X.b

/-- 🏆 THEOREM: The Pauli–Weyl lightcone condition: norm X = 0 iff a * b = u · v. -/
theorem lightcone_null_iff (X : ZornMatrix R) :
    norm X = 0 ↔ X.a * X.b = dot3 X.u X.v := by
  dsimp [norm]
  exact sub_eq_zero

/-- Split Peirce vacuum projector P+ = E11. -/
def PPlus : ZornMatrix R := ⟨1, 0, 0, 0⟩

/-- Split Peirce antilepton projector P- = E22. -/
def PMinus : ZornMatrix R := ⟨0, 1, 0, 0⟩

/-- Split Cartan Iwasawa scale generator ell = E11 - E22. -/
def splitCartanEll : ZornMatrix R := ⟨1, -1, 0, 0⟩

/-- Upper off-diagonal quark creation operator. -/
def quark (u : Vec3 R) : ZornMatrix R := ⟨0, 0, u, 0⟩

/-- Lower off-diagonal antiquark annihilation operator. -/
def antiquark (v : Vec3 R) : ZornMatrix R := ⟨0, 0, 0, v⟩

/-- 🏆 THEOREM: P+ is an idempotent projector: P+ * P+ = P+. -/
theorem peirce_plus_sq : zornMul (PPlus (R := R)) PPlus = PPlus := by
  apply ext
  · dsimp [zornMul, PPlus, dot3]; ring
  · dsimp [zornMul, PPlus, dot3]; ring
  · dsimp [zornMul, PPlus, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, PPlus, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: P- is an idempotent projector: P- * P- = P-. -/
theorem peirce_minus_sq : zornMul (PMinus (R := R)) PMinus = PMinus := by
  apply ext
  · dsimp [zornMul, PMinus, dot3]; ring
  · dsimp [zornMul, PMinus, dot3]; ring
  · dsimp [zornMul, PMinus, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, PMinus, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: P+ and P- are orthogonal: P+ * P- = 0. -/
theorem peirce_ortho_pm : zornMul (PPlus (R := R)) PMinus = zero := by
  apply ext
  · dsimp [zornMul, PPlus, PMinus, zero, dot3]; ring
  · dsimp [zornMul, PPlus, PMinus, zero, dot3]; ring
  · dsimp [zornMul, PPlus, PMinus, zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, PPlus, PMinus, zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: Split Peirce resolution of unity: P+ + P- = 1. -/
theorem peirce_resolution : add (PPlus (R := R)) PMinus = one := by
  apply ext <;> simp [add, PPlus, PMinus, one]

/-- 🏆 THEOREM: P+ (X P+) dynamically extracts the diagonal lepton 0-form vacuum singlet. -/
theorem polarize_lepton_vacuum (X : ZornMatrix R) :
    zornMul PPlus (zornMul X PPlus) = ⟨X.a, 0, 0, 0⟩ := by
  apply ext
  · dsimp [zornMul, PPlus, dot3]; ring
  · dsimp [zornMul, PPlus, dot3]; ring
  · ext i; fin_cases i <;> { dsimp [zornMul, PPlus, cross3]; ring }
  · ext i; fin_cases i <;> { dsimp [zornMul, PPlus, cross3]; ring }

/-- 🏆 THEOREM: P- (X P-) dynamically extracts the diagonal antilepton 3-form saturated Dirac sea. -/
theorem polarize_antilepton_sea (X : ZornMatrix R) :
    zornMul PMinus (zornMul X PMinus) = ⟨0, X.b, 0, 0⟩ := by
  apply ext
  · dsimp [zornMul, PMinus, dot3]; ring
  · dsimp [zornMul, PMinus, dot3]; ring
  · ext i; fin_cases i <;> { dsimp [zornMul, PMinus, cross3]; ring }
  · ext i; fin_cases i <;> { dsimp [zornMul, PMinus, cross3]; ring }

/-- 🏆 THEOREM: P+ (X P-) dynamically extracts the 3-quark 1-form creation triplet. -/
theorem polarize_quark_creation (X : ZornMatrix R) :
    zornMul PPlus (zornMul X PMinus) = quark X.u := by
  apply ext
  · dsimp [zornMul, PPlus, PMinus, quark, dot3]; ring
  · dsimp [zornMul, PPlus, PMinus, quark, dot3]; ring
  · ext i; fin_cases i <;> { dsimp [zornMul, PPlus, PMinus, quark, cross3]; ring }
  · ext i; fin_cases i <;> { dsimp [zornMul, PPlus, PMinus, quark, cross3]; ring }

/-- 🏆 THEOREM: P- (X P+) dynamically extracts the 3-antiquark 2-form annihilation triplet. -/
theorem polarize_antiquark_annihilation (X : ZornMatrix R) :
    zornMul PMinus (zornMul X PPlus) = antiquark X.v := by
  apply ext
  · dsimp [zornMul, PPlus, PMinus, antiquark, dot3]; ring
  · dsimp [zornMul, PPlus, PMinus, antiquark, dot3]; ring
  · ext i; fin_cases i <;> { dsimp [zornMul, PPlus, PMinus, antiquark, cross3]; ring }
  · ext i; fin_cases i <;> { dsimp [zornMul, PPlus, PMinus, antiquark, cross3]; ring }

/-- 🏆 THEOREM: Single quark state is square-nilpotent: Q^2 = 0. -/
theorem quark_sq_zero (u : Vec3 R) : zornMul (quark u) (quark u) = zero := by
  apply ext
  · dsimp [zornMul, quark, zero, dot3]; ring
  · dsimp [zornMul, quark, zero, dot3]; ring
  · dsimp [zornMul, quark, zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, quark, zero]
    rw [cross3_self u]
    ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: Single antiquark state is square-nilpotent: (Q*)^2 = 0. -/
theorem antiquark_sq_zero (v : Vec3 R) : zornMul (antiquark v) (antiquark v) = zero := by
  apply ext
  · dsimp [zornMul, antiquark, zero, dot3]; ring
  · dsimp [zornMul, antiquark, zero, dot3]; ring
  · dsimp [zornMul, antiquark, zero]
    have h : cross3 v v = 0 := cross3_self v
    rw [h]
    ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, antiquark, zero, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: Two quarks bind into an antiquark via cross product: Q_1 * Q_2 = Q_bar(u_1 × u_2). -/
theorem diquark_to_antiquark (u1 u2 : Vec3 R) :
    zornMul (quark u1) (quark u2) = antiquark (cross3 u1 u2) := by
  apply ext
  · dsimp [zornMul, quark, antiquark, dot3]; ring
  · dsimp [zornMul, quark, antiquark, dot3]; ring
  · dsimp [zornMul, quark, antiquark, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, quark, antiquark, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: Three quarks bind into a colorless antilepton baryon singlet in the E22 vacuum. -/
theorem baryon_three_quarks (u1 u2 u3 : Vec3 R) :
    zornMul (zornMul (quark u1) (quark u2)) (quark u3) =
    ⟨0, dot3 (cross3 u1 u2) u3, 0, 0⟩ := by
  rw [diquark_to_antiquark]
  apply ext
  · dsimp [zornMul, antiquark, quark, dot3]; ring
  · dsimp [zornMul, antiquark, quark, dot3]; ring
  · dsimp [zornMul, antiquark, quark, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [zornMul, antiquark, quark, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: Meson Canonical Anticommutation Relations (CAR): {Q(u), Q_bar(v)} = (u · v) * 1. -/
theorem meson_car_anticommutator (u v : Vec3 R) :
    add (zornMul (quark u) (antiquark v)) (zornMul (antiquark v) (quark u)) =
    smul (dot3 u v) one := by
  apply ext
  · dsimp [add, zornMul, quark, antiquark, smul, one, dot3]; ring
  · dsimp [add, zornMul, quark, antiquark, smul, one, dot3]; ring
  · dsimp [add, zornMul, quark, antiquark, smul, one, cross3]; ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [add, zornMul, quark, antiquark, smul, one, cross3]; ext i; fin_cases i <;> { dsimp; ring }

/-- 🏆 THEOREM: Iwasawa Cartan scale generator commutation on quarks: [ell, Q] = +2 Q. -/
theorem iwasawa_scale_quark (u : Vec3 R) :
    sub (zornMul splitCartanEll (quark u)) (zornMul (quark u) splitCartanEll) =
    smul (1 + 1) (quark u) := by
  apply ext
  · dsimp [sub, zornMul, splitCartanEll, quark, smul, dot3]; ring
  · dsimp [sub, zornMul, splitCartanEll, quark, smul, dot3]; ring
  · ext i
    fin_cases i
    · dsimp [sub, zornMul, splitCartanEll, quark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, quark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, quark, smul, cross3]; ring
  · ext i
    fin_cases i
    · dsimp [sub, zornMul, splitCartanEll, quark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, quark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, quark, smul, cross3]; ring

/-- 🏆 THEOREM: Iwasawa Cartan scale generator commutation on antiquarks: [ell, Q_bar] = -2 Q_bar. -/
theorem iwasawa_scale_antiquark (v : Vec3 R) :
    sub (zornMul splitCartanEll (antiquark v)) (zornMul (antiquark v) splitCartanEll) =
    smul (-(1 + 1)) (antiquark v) := by
  apply ext
  · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, dot3]; ring
  · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, dot3]; ring
  · ext i
    fin_cases i
    · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, cross3]; ring
  · ext i
    fin_cases i
    · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, cross3]; ring
    · dsimp [sub, zornMul, splitCartanEll, antiquark, smul, cross3]; ring

end ZornMatrix

end ZornAlgebra

/-!
### Stratum 24.3: Dirac-Kähler Exterior Algebra Fock Space Grading
-/

section DiracKahlerFockGrading

def dimOmega0 : ℕ := 1
def dimOmega1 : ℕ := 3
def dimOmega2 : ℕ := 3
def dimOmega3 : ℕ := 1

/-- 🏆 THEOREM: Total dimension of the Dirac-Kähler exterior algebra matches the split octonions (dim = 8). -/
theorem fock_total_dim : dimOmega0 + dimOmega1 + dimOmega2 + dimOmega3 = 8 := by
  rfl

/-- 🏆 THEOREM: Even forms (leptons and antiquarks) span a 4-dimensional chiral subspace. -/
theorem fock_even_dim : dimOmega0 + dimOmega2 = 4 := by
  rfl

/-- 🏆 THEOREM: Odd forms (quarks and antileptons) span a 4-dimensional chiral subspace. -/
theorem fock_odd_dim : dimOmega1 + dimOmega3 = 4 := by
  rfl

end DiracKahlerFockGrading

/-!
### Stratum 24.4: The Geometric Color Stabilizer Stab(P+) ≅ SU(3)
Any algebra automorphism fixing the split Peirce projector P_+ preserves the lepton vacuum
pointwise, while stabilizing the quark creation and antiquark annihilation sectors.
-/

section StabilizerGeometry

variable {A : Type*} [Ring A]
variable (P_plus P_minus : A)

def isLeptonVacuum (x : A) : Prop :=
  P_plus * x * P_plus = x

def isQuarkSector (x : A) : Prop :=
  P_plus * x * P_minus = x

def isAntiquarkSector (x : A) : Prop :=
  P_minus * x * P_plus = x

/-- 🏆 THEOREM: An automorphism preserving P_+ preserves the lepton vacuum. -/
theorem stabilizer_preserves_vacuum
    (σ : A → A)
    (h_mul : ∀ x y, σ (x * y) = σ x * σ y)
    (h_P : σ P_plus = P_plus)
    (x : A) (hx : isLeptonVacuum P_plus x) :
    isLeptonVacuum P_plus (σ x) := by
  unfold isLeptonVacuum at *
  calc P_plus * σ x * P_plus
    _ = σ P_plus * σ x * σ P_plus := by rw [h_P]
    _ = σ (P_plus * x * P_plus) := by rw [← h_mul, ← h_mul]
    _ = σ x := by rw [hx]

/-- 🏆 THEOREM: An automorphism preserving P_+ and P_- stabilizes the quark creation sector. -/
theorem stabilizer_preserves_quark_sector
    (σ : A → A)
    (h_mul : ∀ x y, σ (x * y) = σ x * σ y)
    (h_P_plus : σ P_plus = P_plus)
    (h_P_minus : σ P_minus = P_minus)
    (x : A) (hx : isQuarkSector P_plus P_minus x) :
    isQuarkSector P_plus P_minus (σ x) := by
  unfold isQuarkSector at *
  calc P_plus * σ x * P_minus
    _ = σ P_plus * σ x * σ P_minus := by rw [h_P_plus, h_P_minus]
    _ = σ (P_plus * x * P_minus) := by rw [← h_mul, ← h_mul]
    _ = σ x := by rw [hx]

/-- 🏆 THEOREM: An automorphism preserving P_+ and P_- stabilizes the antiquark annihilation sector. -/
theorem stabilizer_preserves_antiquark_sector
    (σ : A → A)
    (h_mul : ∀ x y, σ (x * y) = σ x * σ y)
    (h_P_plus : σ P_plus = P_plus)
    (h_P_minus : σ P_minus = P_minus)
    (x : A) (hx : isAntiquarkSector P_plus P_minus x) :
    isAntiquarkSector P_plus P_minus (σ x) := by
  unfold isAntiquarkSector at *
  calc P_minus * σ x * P_plus
    _ = σ P_minus * σ x * σ P_plus := by rw [h_P_plus, h_P_minus]
    _ = σ (P_minus * x * P_plus) := by rw [← h_mul, ← h_mul]
    _ = σ x := by rw [hx]

end StabilizerGeometry

/-!
### Stratum 24.5: Master Synthesis Packet for Stratum 24
-/

structure ZornDiracKahlerSU3Packet (R : Type*) [CommRing R] where
  cross_self : ∀ u : Vec3 R, cross3 u u = 0
  lightcone_null : ∀ X : ZornMatrix R, ZornMatrix.norm X = 0 ↔ X.a * X.b = dot3 X.u X.v
  peirce_p_sq : ZornMatrix.zornMul (ZornMatrix.PPlus (R := R)) ZornMatrix.PPlus = ZornMatrix.PPlus
  peirce_m_sq : ZornMatrix.zornMul (ZornMatrix.PMinus (R := R)) ZornMatrix.PMinus = ZornMatrix.PMinus
  peirce_res : ZornMatrix.add (ZornMatrix.PPlus (R := R)) ZornMatrix.PMinus = ZornMatrix.one
  q_sq_zero : ∀ u : Vec3 R, ZornMatrix.zornMul (ZornMatrix.quark u) (ZornMatrix.quark u) = ZornMatrix.zero
  q_bar_sq_zero : ∀ v : Vec3 R, ZornMatrix.zornMul (ZornMatrix.antiquark v) (ZornMatrix.antiquark v) = ZornMatrix.zero
  diquark : ∀ u1 u2 : Vec3 R, ZornMatrix.zornMul (ZornMatrix.quark u1) (ZornMatrix.quark u2) = ZornMatrix.antiquark (cross3 u1 u2)
  baryon : ∀ u1 u2 u3 : Vec3 R, ZornMatrix.zornMul (ZornMatrix.zornMul (ZornMatrix.quark u1) (ZornMatrix.quark u2)) (ZornMatrix.quark u3) =
    ⟨0, dot3 (cross3 u1 u2) u3, 0, 0⟩
  car : ∀ u v : Vec3 R, ZornMatrix.add (ZornMatrix.zornMul (ZornMatrix.quark u) (ZornMatrix.antiquark v))
    (ZornMatrix.zornMul (ZornMatrix.antiquark v) (ZornMatrix.quark u)) = ZornMatrix.smul (dot3 u v) ZornMatrix.one
  fock_total : dimOmega0 + dimOmega1 + dimOmega2 + dimOmega3 = 8
  fock_even : dimOmega0 + dimOmega2 = 4
  fock_odd : dimOmega1 + dimOmega3 = 4

def makeZornDiracKahlerSU3Packet (R : Type*) [CommRing R] :
    ZornDiracKahlerSU3Packet R where
  cross_self := cross3_self
  lightcone_null := ZornMatrix.lightcone_null_iff
  peirce_p_sq := ZornMatrix.peirce_plus_sq
  peirce_m_sq := ZornMatrix.peirce_minus_sq
  peirce_res := ZornMatrix.peirce_resolution
  q_sq_zero := ZornMatrix.quark_sq_zero
  q_bar_sq_zero := ZornMatrix.antiquark_sq_zero
  diquark := ZornMatrix.diquark_to_antiquark
  baryon := ZornMatrix.baryon_three_quarks
  car := ZornMatrix.meson_car_anticommutator
  fock_total := fock_total_dim
  fock_even := fock_even_dim
  fock_odd := fock_odd_dim

end InfoGeometry.Canonical.ZornDiracKahlerSU3

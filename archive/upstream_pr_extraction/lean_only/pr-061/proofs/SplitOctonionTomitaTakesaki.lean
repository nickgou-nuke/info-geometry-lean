import proofs.OctonionMatrixEncodings
import InfoGeometry.Canonical.IntegralZornII44Bridge

/-!
# Split-octonion Peirce Involutions and Para-Hermitian Geometry

This file formalizes the complementary Zorn idempotents (e_\pm),
the split unit (ℓ = e_+ - e_-), the induced left and right para-complex
splittings, and the involutive reflection (X ↦ (ℓ X) ℓ) that negates
the off-diagonal Peirce components. After real scalar extension, left
multiplication by ℓ defines a para-Hermitian structure compatible with
the split norm.

These identities are a finite-dimensional algebraic analogue of grading
and modular-reflection structures; they do not by themselves instantiate
Tomita–Takesaki theory, as there is no von Neumann algebra or true operator
commutant. Nonassociativity strictly prevents right-multipliers from forming
the commutant of left-multipliers.
-/

noncomputable section

namespace SplitOctonionPeirce

open OctonionMatrixEncodings

/-! ## Compatibility with the canonical integral lattice carrier -/

/-- Coordinate-preserving map from the historical integer Zorn record to the
canonical integral lattice carrier used by `IntegralZornII44Bridge`. -/
def toIntegralZorn (X : Zorn) : IntegralZornII44Bridge.IntegralZorn :=
  (X.a, X.u, (X.v, X.b))

/-- Coordinate-preserving inverse to `toIntegralZorn`. -/
def ofIntegralZorn (X : IntegralZornII44Bridge.IntegralZorn) : Zorn where
  a := X.a
  u := X.u
  v := X.v
  b := X.b

/-- The legacy record and the canonical integral lattice carrier contain
exactly the same coordinate data. -/
def integralCarrierEquiv : Zorn ≃ IntegralZornII44Bridge.IntegralZorn where
  toFun := toIntegralZorn
  invFun := ofIntegralZorn
  left_inv X := by cases X; rfl
  right_inv X := by rcases X with ⟨a, u, v, b⟩; rfl

/-- Projector P₊ (e_+) on the Zorn algebra -/
def P_plus : Zorn where
  a := 1; u := fun _ => 0; v := fun _ => 0; b := 0

/-- Projector P₋ (e_-) on the Zorn algebra -/
def P_minus : Zorn where
  a := 0; u := fun _ => 0; v := fun _ => 0; b := 1

/-- Identity element of the Zorn algebra -/
def I : Zorn where
  a := 1; u := fun _ => 0; v := fun _ => 0; b := 1

/-- Zero element of the Zorn algebra -/
def Z_zero : Zorn where
  a := 0; u := fun _ => 0; v := fun _ => 0; b := 0

/-- Split unit ℓ = e₊ - e₋. This is an algebra element, not a Tomita modular conjugation. -/
def ell : Zorn where
  a := 1; u := fun _ => 0; v := fun _ => 0; b := -1

/-- Zorn scalar multiplication -/
def zorn_scale (c : ℤ) (X : Zorn) : Zorn where
  a := c * X.a
  u := fun i => c * X.u i
  v := fun i => c * X.v i
  b := c * X.b

theorem P_plus_idempotent : zornMul P_plus P_plus = P_plus := by
  apply zorn_ext
  · simp [zornMul, P_plus, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_plus, cross3, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_plus, cross3, dot3]
  · simp [zornMul, P_plus, dot3]

theorem P_minus_idempotent : zornMul P_minus P_minus = P_minus := by
  apply zorn_ext
  · simp [zornMul, P_minus, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_minus, cross3, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_minus, cross3, dot3]
  · simp [zornMul, P_minus, dot3]

theorem P_plus_mul_P_minus : zornMul P_plus P_minus = Z_zero := by
  apply zorn_ext
  · simp [zornMul, P_plus, P_minus, Z_zero, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_plus, P_minus, Z_zero, cross3, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_plus, P_minus, Z_zero, cross3, dot3]
  · simp [zornMul, P_plus, P_minus, Z_zero, dot3]

theorem P_minus_mul_P_plus : zornMul P_minus P_plus = Z_zero := by
  apply zorn_ext
  · simp [zornMul, P_minus, P_plus, Z_zero, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_minus, P_plus, Z_zero, cross3, dot3]
  · funext i; fin_cases i <;> simp [zornMul, P_minus, P_plus, Z_zero, cross3, dot3]
  · simp [zornMul, P_minus, P_plus, Z_zero, dot3]

theorem ell_sq_eq_one : zornMul ell ell = I := by
  apply zorn_ext
  · simp [zornMul, ell, I, dot3]
  · funext i; fin_cases i <;> simp [zornMul, ell, I, cross3, dot3]
  · funext i; fin_cases i <;> simp [zornMul, ell, I, cross3, dot3]
  · simp [zornMul, ell, I, dot3]

def Z_off (u v : Vec3) : Zorn where
  a := 0; u := u; v := v; b := 0

def neg_Z_off (u v : Vec3) : Zorn where
  a := 0; u := fun i => -u i; v := fun i => -v i; b := 0

/-- ℓ-sandwich reflection negates the off-diagonal components -/
theorem ell_reflection_offDiagonal (u v : Vec3) :
    zornMul (zornMul ell (Z_off u v)) ell = neg_Z_off u v := by
  apply zorn_ext
  · simp [zornMul, ell, Z_off, neg_Z_off, dot3]
  · funext i; fin_cases i <;> simp [zornMul, ell, Z_off, neg_Z_off, cross3, dot3]
  · funext i; fin_cases i <;> simp [zornMul, ell, Z_off, neg_Z_off, cross3, dot3]
  · simp [zornMul, ell, Z_off, neg_Z_off, dot3]

/-- The exact nilpotent result for the off-diagonal sector -/
theorem Z_off_sq (u v : Vec3) :
    zornMul (Z_off u v) (Z_off u v) = { a := dot3 u v, u := fun _ => 0, v := fun _ => 0, b := dot3 v u } := by
  apply zorn_ext
  · simp [zornMul, Z_off, dot3]
  · funext i; fin_cases i <;> simp [zornMul, Z_off, cross3, dot3] <;> ring
  · funext i; fin_cases i <;> simp [zornMul, Z_off, cross3, dot3] <;> ring
  · simp [zornMul, Z_off, dot3]

/-- The canonical conjugation of the Zorn algebra -/
def zornStar (X : Zorn) : Zorn where
  a := X.b
  u := fun i => -X.u i
  v := fun i => -X.v i
  b := X.a

/-- Exact left/right regular intertwining via the canonical anti-involution.
    This is the genuine modular-style relation present in the nonassociative algebra. -/
theorem zornStar_left_right (X Y : Zorn) :
    zornStar (zornMul X (zornStar Y)) = zornMul Y (zornStar X) := by
  apply zorn_ext
  · simp [zornStar, zornMul, dot3, Fin.sum_univ_three]; ring
  · funext i; fin_cases i <;>
      simp [zornStar, zornMul, cross3, dot3, Fin.sum_univ_three] <;> ring
  · funext i; fin_cases i <;>
      simp [zornStar, zornMul, cross3, dot3, Fin.sum_univ_three] <;> ring
  · simp [zornStar, zornMul, dot3, Fin.sum_univ_three]; ring

/-!
### Hyperbolic Rotations (Hestenes Space-Time Bivectors)

Because the split unit ℓ squares to +1, its action generates a para-complex
structure. In spacetime algebra, exponentiating a bivector that squares to +1
generates a hyperbolic rotation (a Lorentz boost).

We formalize the discrete algebraic equivalent of this boost along the
diagonal causal planes, and prove it acts as an isometry for the split norm!
-/

/-- The intrinsic Split Octonion Norm (Minkowski metric determinant) -/
def zornNorm (X : Zorn) : ℤ :=
  X.a * X.b - dot3 X.u X.v

/-- The historical integer norm is definitionally the canonical integral
Zorn lattice norm under `integralCarrierEquiv`. -/
theorem integralCarrierEquiv_norm (X : Zorn) :
    IntegralZornII44Bridge.integralZornNorm (integralCarrierEquiv X) =
      zornNorm X := by
  simp [integralCarrierEquiv, toIntegralZorn,
    IntegralZornII44Bridge.integralZornNorm, zornNorm, dot3,
    IntegralZornII44Bridge.IntegralZorn.a,
    IntegralZornII44Bridge.IntegralZorn.u,
    IntegralZornII44Bridge.IntegralZorn.v,
    IntegralZornII44Bridge.IntegralZorn.b]

/-- The same norm is transported to the canonical real Zorn carrier by the
existing integral lattice embedding. -/
theorem legacy_real_norm_bridge (X : Zorn) :
    ZornCore.det
        (IntegralZornII44Bridge.integralToCoreZorn (integralCarrierEquiv X)) =
      (zornNorm X : ℝ) := by
  rw [IntegralZornII44Bridge.integralToCoreZorn_det,
    integralCarrierEquiv_norm]

/-- A discrete Hyperbolic Rotation (Lorentz Boost) parameterized by k and k⁻¹ -/
def HyperbolicBoost (k k_inv : ℤ) : Zorn where
  a := k; u := fun _ => 0; v := fun _ => 0; b := k_inv

/-- A hyperbolic boost preserves the intrinsic split norm (it is an SO(4,4) isometry!) -/
theorem Boost_preserves_norm (k k_inv : ℤ) (hk : k * k_inv = 1) (X : Zorn) :
    let B := HyperbolicBoost k k_inv
    zornNorm (zornMul (zornMul B X) B) = zornNorm X := by
  -- The diagonal and vector products each contain two inverse pairs.
  have h2 : k * X.a * k * (k_inv * X.b * k_inv) = X.a * X.b := by
    calc k * X.a * k * (k_inv * X.b * k_inv)
      _ = (k * k_inv) * (k * k_inv) * (X.a * X.b) := by ring
      _ = 1 * 1 * (X.a * X.b) := by rw [hk]
      _ = X.a * X.b := by ring

  have h3 : ∀ x y : ℤ, k_inv * (k * x) * (k * (k_inv * y)) = x * y := by
    intro x y
    calc
      k_inv * (k * x) * (k * (k_inv * y)) =
          (k * k_inv) * (k * k_inv) * (x * y) := by ring
      _ = x * y := by rw [hk]; ring

  -- Expand the Zorn algebra operations and apply the local lemmas
  simp [zornNorm, HyperbolicBoost, zornMul, dot3, cross3,
    Fin.sum_univ_three, h2, h3]

/-!
### Split-Quaternions (M₂(ℝ) Spinors) & The Twistor Subalgebra

The split-quaternions form a 4-dimensional associative subalgebra inside the
split-octonions. By restricting the off-diagonal vectors to a single geometric axis
(e.g., the first coordinate i=0), the non-associative cross products completely vanish.

This leaves an exact algebraic copy of M₂(ℝ) (or M₂(ℤ) in our discrete lattice).
This 4D subalgebra natively underpins the SL(2, ℝ) spin group and the
null-cone geometry of Penrose Twistors!
-/

/-- A Zorn matrix is a Split-Quaternion if its off-diagonal vectors are restricted to the 0th axis -/
def isSplitQuaternion (X : Zorn) : Prop :=
  X.u 1 = 0 ∧ X.u 2 = 0 ∧ X.v 1 = 0 ∧ X.v 2 = 0

/-- The fundamental obstruction to associativity in the octonions is the cross product.
    Because split-quaternions are collinear on the 0th axis, they are strictly associative!
    This provides the exact associative SL(2, ℝ) spinor geometry needed for Twistors. -/
theorem split_quaternion_associative (X Y Z : Zorn)
    (hX : isSplitQuaternion X) (hY : isSplitQuaternion Y) (hZ : isSplitQuaternion Z) :
    zornMul (zornMul X Y) Z = zornMul X (zornMul Y Z) := by
  rcases hX with ⟨hx_u1, hx_u2, hx_v1, hx_v2⟩
  rcases hY with ⟨hy_u1, hy_u2, hy_v1, hy_v2⟩
  rcases hZ with ⟨hz_u1, hz_u2, hz_v1, hz_v2⟩
  have hx_u : X.u = fun i => if i = 0 then X.u 0 else 0 := by
    funext i; fin_cases i <;> simp [hx_u1, hx_u2]
  have hx_v : X.v = fun i => if i = 0 then X.v 0 else 0 := by
    funext i; fin_cases i <;> simp [hx_v1, hx_v2]
  have hy_u : Y.u = fun i => if i = 0 then Y.u 0 else 0 := by
    funext i; fin_cases i <;> simp [hy_u1, hy_u2]
  have hy_v : Y.v = fun i => if i = 0 then Y.v 0 else 0 := by
    funext i; fin_cases i <;> simp [hy_v1, hy_v2]
  have hz_u : Z.u = fun i => if i = 0 then Z.u 0 else 0 := by
    funext i; fin_cases i <;> simp [hz_u1, hz_u2]
  have hz_v : Z.v = fun i => if i = 0 then Z.v 0 else 0 := by
    funext i; fin_cases i <;> simp [hz_v1, hz_v2]
  apply zorn_ext
  · simp only [zornMul]
    rw [hx_u, hx_v, hy_u, hy_v, hz_u, hz_v]
    simp [dot3, cross3]
    ring
  · funext i
    simp only [zornMul]
    rw [hx_u, hx_v, hy_u, hy_v, hz_u, hz_v]
    fin_cases i <;> simp [dot3, cross3]
    ring
  · funext i
    simp only [zornMul]
    rw [hx_u, hx_v, hy_u, hy_v, hz_u, hz_v]
    fin_cases i <;> simp [dot3, cross3]
    ring
  · simp only [zornMul]
    rw [hx_u, hx_v, hy_u, hy_v, hz_u, hz_v]
    simp [dot3, cross3]
    ring

/-!
### Integral dot/cross-preserving transformations

The following theorem is retained under its historical API name.  Its actual
hypotheses describe an integral transformation preserving `dot3`, `cross3`,
and the required linear combinations.  No identification with a complex
special-unitary group is made by this theorem.

We formalize this by proving that any vector transformation U that preserves 
`dot3` and `cross3` (along with linearity) acts as a perfect algebraic 
automorphism on the entire split-octonion space.
-/

/-- Apply a vector transformation (gauge transformation) to the color off-diagonals -/
def applyGauge (X : Zorn) (U : (Fin 3 → ℤ) → (Fin 3 → ℤ)) : Zorn where
  a := X.a
  u := U X.u
  v := U X.v
  b := X.b

/-- If a transformation preserves the integral 3D invariants and the required
linear combinations, its coordinatewise action preserves Zorn multiplication. -/
theorem SU3_gauge_is_automorphism (U : (Fin 3 → ℤ) → (Fin 3 → ℤ))
    (h_dot : ∀ x y, dot3 (U x) (U y) = dot3 x y)
    (h_cross : ∀ x y, U (cross3 x y) = cross3 (U x) (U y))
    (h_linear_add : ∀ a b x y, U (fun i => a * x i + b * y i) = fun i => a * U x i + b * U y i)
    (h_linear_sub : ∀ x y, U (fun i => x i - y i) = fun i => U x i - U y i)
    (X Y : Zorn) :
    applyGauge (zornMul X Y) U = zornMul (applyGauge X U) (applyGauge Y U) := by
  apply zorn_ext
  · -- Diagonal a matches because the dot product is invariant
    simp [applyGauge, zornMul]
    rw [h_dot]
  · -- Upper vector u matches because of linearity and cross product invariance
    funext i
    simp [applyGauge, zornMul]
    have h_sub := congr_fun (h_linear_sub (fun j => X.a * Y.u j + Y.b * X.u j) (cross3 X.v Y.v)) i
    have h_add := congr_fun (h_linear_add X.a Y.b Y.u X.u) i
    have h_cr := congr_fun (h_cross X.v Y.v) i
    rw [h_sub, h_add, h_cr]
  · -- Lower vector v matches identically
    funext i
    simp [applyGauge, zornMul]
    have h_outer := congr_fun
      (h_linear_add 1 1
        (fun j => Y.a * X.v j + X.b * Y.v j)
        (cross3 X.u Y.u)) i
    have h_inner := congr_fun
      (h_linear_add Y.a X.b X.v Y.v) i
    have h_cr := congr_fun (h_cross X.u Y.u) i
    rw [show U (fun j => Y.a * X.v j + X.b * Y.v j + cross3 X.u Y.u j) i =
        U (fun j => 1 * (Y.a * X.v j + X.b * Y.v j) + 1 * cross3 X.u Y.u j) i by
          congr 2; funext j; ring]
    rw [h_outer, h_inner, h_cr]
    ring
  · -- Diagonal b matches because the dot product is invariant
    simp [applyGauge, zornMul]
    rw [h_dot]

/-- Upper nilpotent operator (quark color state) -/
def N_upper (u : Vec3) : Zorn where
  a := 0; u := u; v := fun _ => 0; b := 0

/-- The Non-Associative Associator [X, Y, Z] = (X*Y)*Z - X*(Y*Z) -/
def associator (X Y Z : Zorn) : Zorn where
  a := (zornMul (zornMul X Y) Z).a - (zornMul X (zornMul Y Z)).a
  u := fun i => (zornMul (zornMul X Y) Z).u i - (zornMul X (zornMul Y Z)).u i
  v := fun i => (zornMul (zornMul X Y) Z).v i - (zornMul X (zornMul Y Z)).v i
  b := (zornMul (zornMul X Y) Z).b - (zornMul X (zornMul Y Z)).b

/-- The product of three upper nilpotents (quarks) with left-bracketing 
    yields the color determinant on the P₋ projector -/
theorem baryon_left_bracketing (u1 u2 u3 : Fin 3 → ℤ) :
    zornMul (zornMul (N_upper u1) (N_upper u2)) (N_upper u3) = 
    { a := 0, u := fun _ => 0, v := fun _ => 0, b := dot3 (cross3 u1 u2) u3 } := by
  apply zorn_ext
  · simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring
  · funext i; fin_cases i <;> (simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring)
  · funext i; fin_cases i <;> (simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring)
  · simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring

/-- The product of three upper nilpotents (quarks) with right-bracketing 
    yields the positive color determinant on the P₊ projector -/
theorem baryon_right_bracketing (u1 u2 u3 : Fin 3 → ℤ) :
    zornMul (N_upper u1) (zornMul (N_upper u2) (N_upper u3)) = 
    { a := dot3 u1 (cross3 u2 u3), u := fun _ => 0, v := fun _ => 0, b := 0 } := by
  apply zorn_ext
  · simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring
  · funext i; fin_cases i <;> (simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring)
  · funext i; fin_cases i <;> (simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring)
  · simp [zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring

/-- The Baryon Confinement Theorem: The associator of three quarks (upper nilpotents)
    collapses exactly into a diagonal scalar multiple of the split unit ell.
    This scalar is the color determinant (scalar triple product). -/
theorem baryon_associator_singlet (u1 u2 u3 : Fin 3 → ℤ) :
    associator (N_upper u1) (N_upper u2) (N_upper u3) = 
    zorn_scale (- dot3 (cross3 u1 u2) u3) ell := by
  apply zorn_ext
  · simp [associator, zorn_scale, ell, zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring
  · funext i; fin_cases i <;> (simp [associator, zorn_scale, ell, zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring)
  · funext i; fin_cases i <;> (simp [associator, zorn_scale, ell, zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring)
  · simp [associator, zorn_scale, ell, zornMul, N_upper, dot3, cross3, Fin.sum_univ_three]; try ring

/-- Lower nilpotent operator (anti-quark color state) -/
def N_lower (v : Vec3) : Zorn where
  a := 0; u := fun _ => 0; v := v; b := 0

/-- The Anti-Baryon Confinement Theorem: The associator of three anti-quarks (lower nilpotents)
    collapses into the EXACT SAME diagonal scalar multiple of the split unit ell.
    This scalar is the anti-color determinant. -/
theorem antibaryon_associator_singlet (v1 v2 v3 : Fin 3 → ℤ) :
    associator (N_lower v1) (N_lower v2) (N_lower v3) = 
    zorn_scale (- dot3 (cross3 v1 v2) v3) ell := by
  apply zorn_ext
  · simp [associator, zorn_scale, ell, zornMul, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring
  · funext i; fin_cases i <;> (simp [associator, zorn_scale, ell, zornMul, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring)
  · funext i; fin_cases i <;> (simp [associator, zorn_scale, ell, zornMul, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring)
  · simp [associator, zorn_scale, ell, zornMul, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring

/-- The symmetric product (anticommutator) for Mesons -/
def zornSymMul (X Y : Zorn) : Zorn where
  a := (zornMul X Y).a + (zornMul Y X).a
  u := fun i => (zornMul X Y).u i + (zornMul Y X).u i
  v := fun i => (zornMul X Y).v i + (zornMul Y X).v i
  b := (zornMul X Y).b + (zornMul Y X).b

/-- The Meson Confinement Theorem: The symmetric product of a quark and anti-quark
    collapses exactly into a diagonal scalar multiple of the Identity matrix I.
    This scalar is the color dot product. -/
theorem meson_symmetric_singlet (u v : Fin 3 → ℤ) :
    zornSymMul (N_upper u) (N_lower v) = 
    zorn_scale (dot3 u v) I := by
  apply zorn_ext
  · simp [zornSymMul, zorn_scale, I, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring
  · funext i; fin_cases i <;> (simp [zornSymMul, zorn_scale, I, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring)
  · funext i; fin_cases i <;> (simp [zornSymMul, zorn_scale, I, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring)
  · simp [zornSymMul, zorn_scale, I, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring

/-- The antisymmetric product (commutator) for Paracomplex Mesons -/
def zornCommMul (X Y : Zorn) : Zorn where
  a := (zornMul X Y).a - (zornMul Y X).a
  u := fun i => (zornMul X Y).u i - (zornMul Y X).u i
  v := fun i => (zornMul X Y).v i - (zornMul Y X).v i
  b := (zornMul X Y).b - (zornMul Y X).b

/-- The Paracomplex Meson Theorem: The commutator of a quark and anti-quark
    collapses exactly into a diagonal scalar multiple of the split-unit ell. -/
theorem meson_antisymmetric_singlet (u v : Fin 3 → ℤ) :
    zornCommMul (N_upper u) (N_lower v) = 
    zorn_scale (dot3 u v) ell := by
  apply zorn_ext
  · simp [zornCommMul, zorn_scale, ell, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring
  · funext i; fin_cases i <;> (simp [zornCommMul, zorn_scale, ell, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring)
  · funext i; fin_cases i <;> (simp [zornCommMul, zorn_scale, ell, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring)
  · simp [zornCommMul, zorn_scale, ell, zornMul, N_upper, N_lower, dot3, cross3, Fin.sum_univ_three]; try ring

end SplitOctonionPeirce

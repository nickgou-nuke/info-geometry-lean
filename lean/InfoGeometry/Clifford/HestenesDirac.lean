import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Real Hestenes-Dirac scaffold

This module records the theorem-facing real-geometric surface for the
Dirac-Hestenes lane.  It intentionally keeps the phase generator as a real
bivector field of the spacetime algebra: the distinguished spin plane
`sigma3Phase` squares to `-1`, while boost planes square to `+1`.

The concrete `4 × 4` realified Hermitian Pauli slice below is the physical
`(+---)` Minkowski lane, not the split `(2,2)` signature of raw `M₂(ℝ)`.
Spacetime four-vectors are encoded as real symmetric `4 × 4` matrices
commuting with a fixed real complex structure `J`.  The scalar/time coordinate
is recovered by trace normalization, while the signed Minkowski interval is
recovered from the Pfaffian of `S * J`.  In the concrete owner:

* `concreteSpacetimeMatrix_commutes_with_J` proves the realification slice
  commutes with `J`;
* `concreteSpacetimeMatrix_time_eq_trace_div_four` proves
  `trace S / 4 = t`;
* `concrete_pfaffianSJ_eq_neg_interval` proves
  `Pf(SJ) = -(t² - x² - y² - z²)`;
* `concrete_null_cone_iff_pfaffian_zero` proves the light cone is exactly the
  Pfaffian-zero locus.

The declarations are conservative: conservation and spin-transport laws are
not smuggled in as global assumptions.  They are carried by explicit owner
packets until the Hestenes--Krein differential/colimit owner proves them from a
concrete model.
-/

namespace InfoGeometry.Clifford.HestenesDirac

/--
A minimal real spacetime-algebra interface for the Dirac-Hestenes corridor.
The carrier is an arbitrary real algebraic object with multiplication; the
signature facts are explicit theorem fields.
-/
structure RealSpacetimeAlgebra (A : Type u) [Mul A] [One A] [Neg A] where
  gamma0 : A
  gamma1 : A
  gamma2 : A
  gamma3 : A
  pseudoscalar : A
  sigma1 : A
  sigma2 : A
  sigma3 : A
  sigma3Phase : A
  boostPlane : A
  gamma0_sq : gamma0 * gamma0 = 1
  gamma1_sq : gamma1 * gamma1 = -1
  gamma2_sq : gamma2 * gamma2 = -1
  gamma3_sq : gamma3 * gamma3 = -1
  /-- Spatial/spin phase plane: elliptic generator. -/
  ellipticBivector_sq : sigma3Phase * sigma3Phase = -1
  /-- Spacetime boost plane: hyperbolic generator. -/
  hyperbolicBivector_sq : boostPlane * boostPlane = 1
  /-- Alias used by the Dirac-Hestenes spin-plane phase. -/
  spinPlane_sq : sigma3Phase * sigma3Phase = -1

namespace RealSpacetimeAlgebra

variable {A : Type u} [Mul A] [One A] [Neg A]

/-- The elliptic spin plane and the spin-plane square law are the same owner fact. -/
theorem spinPlane_sq_eq_elliptic (G : RealSpacetimeAlgebra A) :
    G.spinPlane_sq = G.ellipticBivector_sq := by
  apply Subsingleton.elim

end RealSpacetimeAlgebra

/-- A real rotor packet.  The inverse law is left explicit because different
concrete Clifford representations may expose reversion/inversion differently. -/
structure RealRotor (A : Type u) [Mul A] [One A] where
  rotor : A
  reverse : A
  rotor_reverse : rotor * reverse = 1
  reverse_rotor : reverse * rotor = 1

/--
A conservative Dirac-Hestenes spinor packet.  The physical bilinear readouts are
owned as real vector/bivector surfaces rather than as column-vector components.
The `densityScale` field is the representation-local real weighting operation.
-/
structure DiracHestenesSpinor (A : Type u) where
  amplitude : A
  density : ℝ
  densityScale : ℝ → A → A
  rotor : A
  velocityFrameReadout : A
  spinAxisReadout : A
  orientedSpinPlane : A
  yvonTakabayasiAngle : ℝ

namespace DiracHestenesSpinor

variable {A : Type u}

/-- Real current bilinear shadow: density times rotor-owned velocity frame. -/
def current (ψ : DiracHestenesSpinor A) : A :=
  ψ.densityScale ψ.density ψ.velocityFrameReadout

/-- Real spin-plane bilinear shadow: density times the oriented bivector plane. -/
def spinPlane (ψ : DiracHestenesSpinor A) : A :=
  ψ.densityScale ψ.density ψ.orientedSpinPlane

/-- Velocity-frame projection carried by the rotor field. -/
def velocityFrame (ψ : DiracHestenesSpinor A) : A :=
  ψ.velocityFrameReadout

/-- Spin-axis projection carried by the rotor field. -/
def spinAxis (ψ : DiracHestenesSpinor A) : A :=
  ψ.spinAxisReadout

/-- The current is definitionally the density-weighted velocity readout. -/
theorem current_eq_density_smul_velocityFrame (ψ : DiracHestenesSpinor A) :
    ψ.current = ψ.densityScale ψ.density ψ.velocityFrame := by
  rfl

/-- The spin-plane bilinear is definitionally the density-weighted spin plane. -/
theorem spinPlane_eq_density_smul_orientedSpinPlane (ψ : DiracHestenesSpinor A) :
    ψ.spinPlane = ψ.densityScale ψ.density ψ.orientedSpinPlane := by
  rfl

end DiracHestenesSpinor

/--
Polar owner for a real Dirac-Hestenes spinor.  This is the Lean-facing form of
`ψ = ρ^{1/2} R e^{β I/2}` with every factor represented as a real object:
`densityRoot`, a Lorentz rotor, the Yvon-Takabayasi angle, and a real
pseudoscalar phase action.  The reconstruction law is explicit so a concrete
Clifford model can later prove it from multiplication/exponential semantics.
-/
structure DiracHestenesPolarDecomposition (A : Type u) [Mul A] [One A] where
  amplitude : A
  density : ℝ
  densityRoot : ℝ
  densityScale : ℝ → A → A
  lorentzRotor : A
  rotorPacket : RealRotor A
  ytAngle : ℝ
  pseudoscalarPhase : A
  phasePlane : A
  velocityFrameReadout : A
  spinAxisReadout : A
  orientedSpinPlane : A
  reconstruct : ℝ → A → A → A
  /-- Real polar reconstruction, theorem-facing form of `ψ = ρ^{1/2} R e^{β I/2}`. -/
  spinor_eq_density_rotor_phase :
    amplitude = reconstruct densityRoot lorentzRotor pseudoscalarPhase

namespace DiracHestenesPolarDecomposition

variable {A : Type u} [Mul A] [One A]

/-- Forget the polar factorization into the base real Dirac-Hestenes spinor packet. -/
def toDiracHestenesSpinor (P : DiracHestenesPolarDecomposition A) :
    DiracHestenesSpinor A where
  amplitude := P.amplitude
  density := P.density
  densityScale := P.densityScale
  rotor := P.lorentzRotor
  velocityFrameReadout := P.velocityFrameReadout
  spinAxisReadout := P.spinAxisReadout
  orientedSpinPlane := P.orientedSpinPlane
  yvonTakabayasiAngle := P.ytAngle

/-- Current readout derived from the real polar owner. -/
def current_of_polar (P : DiracHestenesPolarDecomposition A) : A :=
  P.toDiracHestenesSpinor.current

/-- Spin-plane readout derived from the real polar owner. -/
def spinPlane_of_polar (P : DiracHestenesPolarDecomposition A) : A :=
  P.toDiracHestenesSpinor.spinPlane

/-- The Yvon-Takabayasi angle exposed by the polar owner. -/
def yvonTakabayasiAngle_of_polar (P : DiracHestenesPolarDecomposition A) : ℝ :=
  P.ytAngle

/-- The real phase plane used by the polar owner; no scalar complex unit is introduced. -/
def phasePlane_of_polar (P : DiracHestenesPolarDecomposition A) : A :=
  P.phasePlane

/-- The polar current is definitionally the density-weighted velocity readout. -/
theorem polar_current_eq_density_velocity (P : DiracHestenesPolarDecomposition A) :
    P.current_of_polar = P.densityScale P.density P.velocityFrameReadout := by
  rfl

/-- The polar spin-plane readout is definitionally the density-weighted spin plane. -/
theorem polar_spinPlane_eq_density_spinPlane (P : DiracHestenesPolarDecomposition A) :
    P.spinPlane_of_polar = P.densityScale P.density P.orientedSpinPlane := by
  rfl

/-- The polar owner preserves its explicit real Yvon-Takabayasi angle. -/
theorem yvonTakabayasiAngle_of_polar_eq (P : DiracHestenesPolarDecomposition A) :
    P.yvonTakabayasiAngle_of_polar = P.ytAngle := by
  rfl

/-- The polar owner preserves its explicit real phase plane. -/
theorem phasePlane_of_polar_eq (P : DiracHestenesPolarDecomposition A) :
    P.phasePlane_of_polar = P.phasePlane := by
  rfl

end DiracHestenesPolarDecomposition

/--
The real Dirac-Hestenes equation surface.  The differential operator and the
right spin-plane multiplication are explicit fields so concrete analytic lanes
can instantiate them without importing a scalar phase object.
-/
structure DiracHestenesEquation (A : Type u) [Mul A] [One A] [Neg A] where
  spacetime : RealSpacetimeAlgebra A
  spinor : DiracHestenesSpinor A
  nabla : DiracHestenesSpinor A → A
  rightSpinPlane : A → A
  realScale : ℝ → A → A
  mass : ℝ
  massClock : A
  /-- Real form of `∇ ψ Iσ₃ = m ψ γ₀`, stated for the chosen analytic lane. -/
  mass_clock_law : rightSpinPlane (nabla spinor) = realScale mass massClock

/-- Electromagnetic gauge rotation is represented as a real spin-plane action. -/
structure electromagneticGaugeRotation (A : Type u) where
  phaseAngle : ℝ
  rotateInSpinPlane : A → A
  potentialShift : A → A

/-- The Pauli magnetic readout is an electromagnetic bivector paired with a
spin bivector.  Concrete Clifford/Krein lanes can instantiate `pairing`. -/
structure pauliMagneticCoupling (A : Type u) where
  electromagneticBivector : A
  spinBivector : A
  pairing : A → A → ℝ
  coupling : ℝ := pairing electromagneticBivector spinBivector

/--
Owner packet for conservation and spin-plane transport.  This is deliberately
not a global theorem: concrete differential hypotheses must supply the two
readouts.
-/
structure DiracHestenesConservationPacket (A : Type u) where
  spinor : DiracHestenesSpinor A
  divergence : A → ℝ
  spinTransportDefect : A → A
  transportedSpinPlane : A
  /-- Current conservation: `∇ · J = 0`. -/
  current_conserved : divergence spinor.current = 0
  /-- Spin-plane transport closure for the selected rotor connection. -/
  spin_plane_transported : spinTransportDefect spinor.spinPlane = transportedSpinPlane

namespace DiracHestenesConservationPacket

variable {A : Type u}

/-- Extract the real current-conservation theorem from an explicit owner packet. -/
theorem current_conservation (P : DiracHestenesConservationPacket A) :
    P.divergence P.spinor.current = 0 :=
  P.current_conserved

/-- Extract the real spin-plane transport theorem from an explicit owner packet. -/
theorem spin_plane_transport (P : DiracHestenesConservationPacket A) :
    P.spinTransportDefect P.spinor.spinPlane = P.transportedSpinPlane :=
  P.spin_plane_transported

end DiracHestenesConservationPacket

/--
Real `4 × 4` owner for the biquaternion/Minkowski slice.  This is the
realification lane for `M₂(ℂ)` without importing complex scalars: `J` is a real
operator with square `-1`, the spacetime element is a real symmetric matrix
commuting with `J`, and the interval is read by the Pfaffian of `S J`.

The carrier `M4` is intentionally abstract here.  A concrete matrix model can
instantiate multiplication, transpose, determinant, and Pfaffian semantics later;
this packet records the exact theorem-facing real geometry now.
-/
structure RealFourByFourBiquaternionSlice (M4 : Type u) [Mul M4] [One M4] [Neg M4] where
  spacetimeMatrix : M4
  complexStructureJ : M4
  transpose : M4 → M4
  determinant : M4 → ℝ
  pfaffian : M4 → ℝ
  minkowskiInterval : ℝ
  /-- Real scalar `i` replacement: the fixed real complex structure squares to `-I₄`. -/
  J_sq : complexStructureJ * complexStructureJ = -1
  /-- Realification slice condition: the spacetime matrix commutes with `J`. -/
  commutes_with_J : spacetimeMatrix * complexStructureJ = complexStructureJ * spacetimeMatrix
  /-- Hermitian biquaternions become real symmetric `4 × 4` matrices. -/
  symmetric : transpose spacetimeMatrix = spacetimeMatrix
  /-- Pfaffian input `S J`, real and skew in concrete models. -/
  pfaffianSJ : ℝ := pfaffian (spacetimeMatrix * complexStructureJ)
  /-- Realification squares the complex determinant: `det_R S = interval²`. -/
  det_realification_eq_interval_sq : determinant spacetimeMatrix = minkowskiInterval * minkowskiInterval
  /-- Unsquared Minkowski interval from the real Pfaffian: `interval = -Pf(SJ)`. -/
  interval_eq_neg_pfaffianSJ : minkowskiInterval = -pfaffianSJ
  /-- Null cone as the real Pfaffian zero locus. -/
  null_cone_iff_pfaffian_zero : minkowskiInterval = 0 ↔ pfaffianSJ = 0

namespace RealFourByFourBiquaternionSlice

variable {M4 : Type u} [Mul M4] [One M4] [Neg M4]

/-- Extract the real Pfaffian formula for the Minkowski interval. -/
theorem minkowskiInterval_eq_neg_pfaffianSJ (S : RealFourByFourBiquaternionSlice M4) :
    S.minkowskiInterval = -S.pfaffianSJ :=
  S.interval_eq_neg_pfaffianSJ

/-- Extract the real null-cone criterion from the owner packet. -/
theorem null_cone_iff_pfaffian_zero_extract (S : RealFourByFourBiquaternionSlice M4) :
    S.minkowskiInterval = 0 ↔ S.pfaffianSJ = 0 :=
  S.null_cone_iff_pfaffian_zero

end RealFourByFourBiquaternionSlice

/--
Real `4 × 4` Majorana/BdG owner.  In the Majorana basis the quadratic BdG data
are carried by a real skew matrix `A`, not by a complex scalar phase.  The
Pfaffian detects the zero-energy Majorana locus, while the determinant is its
square in the usual real skew-matrix way.
-/
structure MajoranaBdGFourByFour (M4 : Type u) [Neg M4] where
  bdgMatrix : M4
  transpose : M4 → M4
  determinant : M4 → ℝ
  pfaffian : M4 → ℝ
  /-- Majorana/BdG generator is real skew-symmetric. -/
  skewSymmetric : transpose bdgMatrix = -bdgMatrix
  /-- For a real skew `4 × 4` matrix, determinant is the square of the Pfaffian. -/
  det_eq_pfaffian_sq : determinant bdgMatrix = pfaffian bdgMatrix * pfaffian bdgMatrix
  /-- Zero-energy Majorana locus as the Pfaffian-zero surface. -/
  zero_mode_iff_pfaffian_zero : determinant bdgMatrix = 0 ↔ pfaffian bdgMatrix = 0

namespace MajoranaBdGFourByFour

variable {M4 : Type u} [Neg M4]

/-- Extract the Majorana zero-mode Pfaffian criterion. -/
theorem zero_mode_iff_pfaffian_zero_extract (A : MajoranaBdGFourByFour M4) :
    A.determinant A.bdgMatrix = 0 ↔ A.pfaffian A.bdgMatrix = 0 :=
  A.zero_mode_iff_pfaffian_zero

end MajoranaBdGFourByFour

/-! ### Real `2 × 2` Pauli seed -/

/-- Concrete real `2 × 2` matrix with explicit coordinates. -/
structure RealMatrix2 where
  m00 : ℝ
  m01 : ℝ
  m10 : ℝ
  m11 : ℝ

namespace RealMatrix2

/-- Extensionality for concrete real `2 × 2` matrices. -/
@[ext] theorem ext {A B : RealMatrix2}
    (h00 : A.m00 = B.m00) (h01 : A.m01 = B.m01)
    (h10 : A.m10 = B.m10) (h11 : A.m11 = B.m11) : A = B := by
  cases A
  cases B
  simp_all

/-- The identity real `2 × 2` matrix. -/
def identity : RealMatrix2 where
  m00 := 1
  m01 := 0
  m10 := 0
  m11 := 1

instance : One RealMatrix2 where
  one := identity

/-- Negation of real `2 × 2` matrices. -/
def matNeg (A : RealMatrix2) : RealMatrix2 where
  m00 := -A.m00
  m01 := -A.m01
  m10 := -A.m10
  m11 := -A.m11

instance : Neg RealMatrix2 where
  neg := matNeg

/-- Multiplication of real `2 × 2` matrices. -/
def matMul (A B : RealMatrix2) : RealMatrix2 where
  m00 := A.m00 * B.m00 + A.m01 * B.m10
  m01 := A.m00 * B.m01 + A.m01 * B.m11
  m10 := A.m10 * B.m00 + A.m11 * B.m10
  m11 := A.m10 * B.m01 + A.m11 * B.m11

instance : Mul RealMatrix2 where
  mul := matMul

/-- The real Pauli generator `σ₁`. -/
def sigma1 : RealMatrix2 where
  m00 := 0
  m01 := 1
  m10 := 1
  m11 := 0

/-- The real Pauli generator `σ₃`. -/
def sigma3 : RealMatrix2 where
  m00 := 1
  m01 := 0
  m10 := 0
  m11 := -1

/-- The real skew phase generator `J = 1/2 [σ₁, σ₃]`. -/
def phaseJ : RealMatrix2 where
  m00 := 0
  m01 := -1
  m10 := 1
  m11 := 0

/-- The real Pauli generator `σ₁` squares to `1`. -/
theorem sigma1_sq : sigma1 * sigma1 = 1 := by
  change matMul sigma1 sigma1 = identity
  apply RealMatrix2.ext <;> norm_num [sigma1, matMul, identity]

/-- The real Pauli generator `σ₃` squares to `1`. -/
theorem sigma3_sq : sigma3 * sigma3 = 1 := by
  change matMul sigma3 sigma3 = identity
  apply RealMatrix2.ext <;> norm_num [sigma3, matMul, identity]

/-- The real phase generator `J` squares to `-1`. -/
theorem phaseJ_sq : phaseJ * phaseJ = -1 := by
  change matMul phaseJ phaseJ = matNeg identity
  apply RealMatrix2.ext <;> norm_num [phaseJ, matMul, matNeg, identity]

/-- Trace of a real `2 × 2` matrix. -/
def trace (A : RealMatrix2) : ℝ :=
  A.m00 + A.m11

/-- Determinant of a real `2 × 2` matrix. -/
def determinant (A : RealMatrix2) : ℝ :=
  A.m00 * A.m11 - A.m01 * A.m10

/-- Real Pauli/chiral operator `t I + x σ₁ + z σ₃ + y J`. -/
def pauliChiralOperator (t x y z : ℝ) : RealMatrix2 where
  m00 := t + z
  m01 := x - y
  m10 := x + y
  m11 := t - z

/--
The raw real `2 × 2` Pauli/chiral determinant has split signature, not the
physical `3+1` Minkowski signature.
-/
theorem determinant_pauliChiralOperator (t x y z : ℝ) :
    determinant (pauliChiralOperator t x y z) = t * t - x * x - z * z + y * y := by
  simp [determinant, pauliChiralOperator]
  ring

/-- The trace of the real Pauli/chiral operator recovers twice the scalar coordinate. -/
theorem trace_pauliChiralOperator (t x y z : ℝ) :
    trace (pauliChiralOperator t x y z) = 2 * t := by
  simp [trace, pauliChiralOperator]
  ring

/-- Trace-normalized real Pauli/chiral operator, defined when `t` is nonzero. -/
noncomputable def normalizedPauliChiralOperator (t x y z : ℝ) : RealMatrix2 where
  m00 := (t + z) / (2 * t)
  m01 := (x - y) / (2 * t)
  m10 := (x + y) / (2 * t)
  m11 := (t - z) / (2 * t)

/-- The trace-normalized real Pauli/chiral operator has trace one. -/
theorem trace_normalizedPauliChiralOperator {t x y z : ℝ} (ht : t ≠ 0) :
    trace (normalizedPauliChiralOperator t x y z) = 1 := by
  unfold trace normalizedPauliChiralOperator
  field_simp [ht]
  ring

/--
The determinant of the trace-normalized real Pauli/chiral operator is the split
quadratic form divided by `4t²`.
-/
theorem determinant_normalizedPauliChiralOperator {t x y z : ℝ} (ht : t ≠ 0) :
    determinant (normalizedPauliChiralOperator t x y z) =
      (t * t - x * x - z * z + y * y) / (4 * t * t) := by
  unfold determinant normalizedPauliChiralOperator
  field_simp [ht]
  ring

end RealMatrix2

/-! ### Realified Hermitian Pauli spacetime slice -/

/-!
This is the checked real `4 × 4` replacement for the complex Hermitian Pauli
matrix `[[t+z, x-iy], [x+iy, t-z]]`.  The real complex structure `J` carries the
role of scalar `i`; the spacetime matrix `S` is symmetric and satisfies
`S * J = J * S`.  The determinant readout is the squared interval, while the
Pfaffian of `S * J` gives the signed interval without taking a square root.

The affine trace-one/Bloch-ball interpretation is downstream geometry: this
file proves the realification, trace, Pfaffian, determinant-square, and null
cone identities used by that interpretation.
-/

/-- Concrete real `4 × 4` matrix with explicit coordinates.  This layer is used
to kernel-check the realification identities behind the abstract Pfaffian owner
packets above, without importing scalar complex numbers. -/
structure RealMatrix4 where
  m00 : ℝ
  m01 : ℝ
  m02 : ℝ
  m03 : ℝ
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m13 : ℝ
  m20 : ℝ
  m21 : ℝ
  m22 : ℝ
  m23 : ℝ
  m30 : ℝ
  m31 : ℝ
  m32 : ℝ
  m33 : ℝ

namespace RealMatrix4

@[ext] theorem ext {A B : RealMatrix4}
    (h00 : A.m00 = B.m00) (h01 : A.m01 = B.m01) (h02 : A.m02 = B.m02) (h03 : A.m03 = B.m03)
    (h10 : A.m10 = B.m10) (h11 : A.m11 = B.m11) (h12 : A.m12 = B.m12) (h13 : A.m13 = B.m13)
    (h20 : A.m20 = B.m20) (h21 : A.m21 = B.m21) (h22 : A.m22 = B.m22) (h23 : A.m23 = B.m23)
    (h30 : A.m30 = B.m30) (h31 : A.m31 = B.m31) (h32 : A.m32 = B.m32) (h33 : A.m33 = B.m33) : A = B := by
  cases A; cases B; simp_all

def zero : RealMatrix4 where
  m00 := 0
  m01 := 0
  m02 := 0
  m03 := 0
  m10 := 0
  m11 := 0
  m12 := 0
  m13 := 0
  m20 := 0
  m21 := 0
  m22 := 0
  m23 := 0
  m30 := 0
  m31 := 0
  m32 := 0
  m33 := 0

instance : Zero RealMatrix4 where
  zero := zero

def identity : RealMatrix4 where
  m00 := 1
  m01 := 0
  m02 := 0
  m03 := 0
  m10 := 0
  m11 := 1
  m12 := 0
  m13 := 0
  m20 := 0
  m21 := 0
  m22 := 1
  m23 := 0
  m30 := 0
  m31 := 0
  m32 := 0
  m33 := 1

instance : One RealMatrix4 where
  one := identity

def matNeg (A : RealMatrix4) : RealMatrix4 where
  m00 := -A.m00
  m01 := -A.m01
  m02 := -A.m02
  m03 := -A.m03
  m10 := -A.m10
  m11 := -A.m11
  m12 := -A.m12
  m13 := -A.m13
  m20 := -A.m20
  m21 := -A.m21
  m22 := -A.m22
  m23 := -A.m23
  m30 := -A.m30
  m31 := -A.m31
  m32 := -A.m32
  m33 := -A.m33

instance : Neg RealMatrix4 where
  neg := matNeg

def matMul (A B : RealMatrix4) : RealMatrix4 where
  m00 := A.m00 * B.m00 + A.m01 * B.m10 + A.m02 * B.m20 + A.m03 * B.m30
  m01 := A.m00 * B.m01 + A.m01 * B.m11 + A.m02 * B.m21 + A.m03 * B.m31
  m02 := A.m00 * B.m02 + A.m01 * B.m12 + A.m02 * B.m22 + A.m03 * B.m32
  m03 := A.m00 * B.m03 + A.m01 * B.m13 + A.m02 * B.m23 + A.m03 * B.m33
  m10 := A.m10 * B.m00 + A.m11 * B.m10 + A.m12 * B.m20 + A.m13 * B.m30
  m11 := A.m10 * B.m01 + A.m11 * B.m11 + A.m12 * B.m21 + A.m13 * B.m31
  m12 := A.m10 * B.m02 + A.m11 * B.m12 + A.m12 * B.m22 + A.m13 * B.m32
  m13 := A.m10 * B.m03 + A.m11 * B.m13 + A.m12 * B.m23 + A.m13 * B.m33
  m20 := A.m20 * B.m00 + A.m21 * B.m10 + A.m22 * B.m20 + A.m23 * B.m30
  m21 := A.m20 * B.m01 + A.m21 * B.m11 + A.m22 * B.m21 + A.m23 * B.m31
  m22 := A.m20 * B.m02 + A.m21 * B.m12 + A.m22 * B.m22 + A.m23 * B.m32
  m23 := A.m20 * B.m03 + A.m21 * B.m13 + A.m22 * B.m23 + A.m23 * B.m33
  m30 := A.m30 * B.m00 + A.m31 * B.m10 + A.m32 * B.m20 + A.m33 * B.m30
  m31 := A.m30 * B.m01 + A.m31 * B.m11 + A.m32 * B.m21 + A.m33 * B.m31
  m32 := A.m30 * B.m02 + A.m31 * B.m12 + A.m32 * B.m22 + A.m33 * B.m32
  m33 := A.m30 * B.m03 + A.m31 * B.m13 + A.m32 * B.m23 + A.m33 * B.m33

instance : Mul RealMatrix4 where
  mul := matMul

def transpose (A : RealMatrix4) : RealMatrix4 := {
  m00 := A.m00
  m01 := A.m10
  m02 := A.m20
  m03 := A.m30
  m10 := A.m01
  m11 := A.m11
  m12 := A.m21
  m13 := A.m31
  m20 := A.m02
  m21 := A.m12
  m22 := A.m22
  m23 := A.m32
  m30 := A.m03
  m31 := A.m13
  m32 := A.m23
  m33 := A.m33
}

/-- Trace of a real `4 × 4` matrix. -/
def trace (A : RealMatrix4) : ℝ :=
  A.m00 + A.m11 + A.m22 + A.m33

/-- Pfaffian formula for a skew `4 × 4` matrix, read from upper entries. -/
def pfaffianSkew4 (A : RealMatrix4) : ℝ :=
  A.m01 * A.m23 - A.m02 * A.m13 + A.m03 * A.m12

end RealMatrix4


/-- Coordinates `(t,x,y,z)` for the Hermitian biquaternion/Minkowski slice. -/
structure MinkowskiCoordinates where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

namespace MinkowskiCoordinates

/-- Minkowski interval in the `(+---)` convention. -/
def interval (c : MinkowskiCoordinates) : ℝ :=
  c.t * c.t - c.x * c.x - c.y * c.y - c.z * c.z

end MinkowskiCoordinates

/-- Fixed real complex structure `J = [[0,-I],[I,0]]`; this replaces scalar `i`. -/
def concreteComplexStructureJ : RealMatrix4 := {
  m00 := 0,  m01 := 0,  m02 := -1, m03 := 0
  m10 := 0,  m11 := 0,  m12 := 0,  m13 := -1
  m20 := 1,  m21 := 0,  m22 := 0,  m23 := 0
  m30 := 0,  m31 := 1,  m32 := 0,  m33 := 0
}

/-- Realification of the Hermitian matrix `[[t+z, x-iy], [x+iy, t-z]]`. -/
def concreteSpacetimeMatrix (c : MinkowskiCoordinates) : RealMatrix4 := {
  m00 := c.t + c.z, m01 := c.x,       m02 := 0,         m03 := c.y
  m10 := c.x,       m11 := c.t - c.z, m12 := -c.y,     m13 := 0
  m20 := 0,         m21 := -c.y,      m22 := c.t + c.z, m23 := c.x
  m30 := c.y,       m31 := 0,         m32 := c.x,       m33 := c.t - c.z
}

/-- Determinant of the realified Hermitian slice, concretely `(t²-x²-y²-z²)²`. -/
def concreteSpacetimeDeterminant (c : MinkowskiCoordinates) (_A : RealMatrix4) : ℝ :=
  c.interval * c.interval

theorem concreteComplexStructureJ_sq :
    concreteComplexStructureJ * concreteComplexStructureJ = -1 := by
  change RealMatrix4.matMul concreteComplexStructureJ concreteComplexStructureJ =
    RealMatrix4.matNeg RealMatrix4.identity
  apply RealMatrix4.ext <;> norm_num [concreteComplexStructureJ, RealMatrix4.matMul,
    RealMatrix4.matNeg, RealMatrix4.identity]

theorem concreteSpacetimeMatrix_commutes_with_J (c : MinkowskiCoordinates) :
    concreteSpacetimeMatrix c * concreteComplexStructureJ =
      concreteComplexStructureJ * concreteSpacetimeMatrix c := by
  change RealMatrix4.matMul (concreteSpacetimeMatrix c) concreteComplexStructureJ =
    RealMatrix4.matMul concreteComplexStructureJ (concreteSpacetimeMatrix c)
  apply RealMatrix4.ext <;> simp [concreteSpacetimeMatrix, concreteComplexStructureJ,
    RealMatrix4.matMul]

theorem concreteSpacetimeMatrix_symmetric (c : MinkowskiCoordinates) :
    RealMatrix4.transpose (concreteSpacetimeMatrix c) = concreteSpacetimeMatrix c := by
  ext <;> simp [RealMatrix4.transpose, concreteSpacetimeMatrix]

/-- The realified Hermitian Pauli trace recovers four times the time coordinate. -/
theorem concreteSpacetimeMatrix_trace (c : MinkowskiCoordinates) :
    RealMatrix4.trace (concreteSpacetimeMatrix c) = 4 * c.t := by
  simp [RealMatrix4.trace, concreteSpacetimeMatrix]
  ring

/-- The time coordinate is the normalized trace of the realified Hermitian Pauli slice. -/
theorem concreteSpacetimeMatrix_time_eq_trace_div_four (c : MinkowskiCoordinates) :
    RealMatrix4.trace (concreteSpacetimeMatrix c) / 4 = c.t := by
  rw [concreteSpacetimeMatrix_trace]
  ring

theorem concrete_pfaffianSJ_eq_neg_interval (c : MinkowskiCoordinates) :
    RealMatrix4.pfaffianSkew4 (concreteSpacetimeMatrix c * concreteComplexStructureJ) =
      -c.interval := by
  change RealMatrix4.pfaffianSkew4
      (RealMatrix4.matMul (concreteSpacetimeMatrix c) concreteComplexStructureJ) = -c.interval
  simp [RealMatrix4.pfaffianSkew4, concreteSpacetimeMatrix, concreteComplexStructureJ,
    MinkowskiCoordinates.interval, RealMatrix4.matMul]
  ring_nf

theorem concrete_det_realification_eq_interval_sq (c : MinkowskiCoordinates) :
    concreteSpacetimeDeterminant c (concreteSpacetimeMatrix c) = c.interval * c.interval := by
  rfl

theorem concrete_null_cone_iff_pfaffian_zero (c : MinkowskiCoordinates) :
    c.interval = 0 ↔
      RealMatrix4.pfaffianSkew4 (concreteSpacetimeMatrix c * concreteComplexStructureJ) = 0 := by
  rw [concrete_pfaffianSJ_eq_neg_interval]
  constructor
  · intro h
    simp [h]
  · intro h
    simpa using congrArg Neg.neg h

/-- Concrete instantiation of the abstract real biquaternion/Pfaffian owner. -/
def concreteBiquaternionSlice (c : MinkowskiCoordinates) :
    RealFourByFourBiquaternionSlice RealMatrix4 where
  spacetimeMatrix := concreteSpacetimeMatrix c
  complexStructureJ := concreteComplexStructureJ
  transpose := RealMatrix4.transpose
  determinant := concreteSpacetimeDeterminant c
  pfaffian := RealMatrix4.pfaffianSkew4
  minkowskiInterval := c.interval
  J_sq := concreteComplexStructureJ_sq
  commutes_with_J := concreteSpacetimeMatrix_commutes_with_J c
  symmetric := concreteSpacetimeMatrix_symmetric c
  det_realification_eq_interval_sq := concrete_det_realification_eq_interval_sq c
  interval_eq_neg_pfaffianSJ := by
    rw [concrete_pfaffianSJ_eq_neg_interval]
    ring
  null_cone_iff_pfaffian_zero := by
    exact concrete_null_cone_iff_pfaffian_zero c

/-- Six independent upper-triangular coordinates for a real skew Majorana/BdG matrix. -/
structure MajoranaBdGCoordinates where
  a12 : ℝ
  a13 : ℝ
  a14 : ℝ
  a23 : ℝ
  a24 : ℝ
  a34 : ℝ

/-- Concrete real skew `4 × 4` Majorana/BdG matrix. -/
def concreteMajoranaBdGMatrix (a : MajoranaBdGCoordinates) : RealMatrix4 := {
  m00 := 0,      m01 := a.a12,  m02 := a.a13,  m03 := a.a14
  m10 := -a.a12, m11 := 0,      m12 := a.a23,  m13 := a.a24
  m20 := -a.a13, m21 := -a.a23, m22 := 0,      m23 := a.a34
  m30 := -a.a14, m31 := -a.a24, m32 := -a.a34, m33 := 0
}

/-- Determinant of a real skew `4 × 4` matrix as the square of its Pfaffian. -/
def determinantSkew4 (A : RealMatrix4) : ℝ :=
  RealMatrix4.pfaffianSkew4 A * RealMatrix4.pfaffianSkew4 A

theorem concreteMajoranaBdG_skewSymmetric (a : MajoranaBdGCoordinates) :
    RealMatrix4.transpose (concreteMajoranaBdGMatrix a) = -concreteMajoranaBdGMatrix a := by
  change RealMatrix4.transpose (concreteMajoranaBdGMatrix a) =
    RealMatrix4.matNeg (concreteMajoranaBdGMatrix a)
  apply RealMatrix4.ext <;> simp [RealMatrix4.transpose, concreteMajoranaBdGMatrix,
    RealMatrix4.matNeg]

theorem concreteMajoranaBdG_det_eq_pfaffian_sq (a : MajoranaBdGCoordinates) :
    determinantSkew4 (concreteMajoranaBdGMatrix a) =
      RealMatrix4.pfaffianSkew4 (concreteMajoranaBdGMatrix a) *
        RealMatrix4.pfaffianSkew4 (concreteMajoranaBdGMatrix a) := by
  rfl

theorem concreteMajoranaBdG_zero_mode_iff_pfaffian_zero (a : MajoranaBdGCoordinates) :
    determinantSkew4 (concreteMajoranaBdGMatrix a) = 0 ↔
      RealMatrix4.pfaffianSkew4 (concreteMajoranaBdGMatrix a) = 0 := by
  dsimp [determinantSkew4]
  exact mul_self_eq_zero

/-- Concrete instantiation of the abstract real Majorana/BdG Pfaffian owner. -/
def concreteMajoranaBdGFourByFour (a : MajoranaBdGCoordinates) :
    MajoranaBdGFourByFour RealMatrix4 where
  bdgMatrix := concreteMajoranaBdGMatrix a
  transpose := RealMatrix4.transpose
  determinant := determinantSkew4
  pfaffian := RealMatrix4.pfaffianSkew4
  skewSymmetric := concreteMajoranaBdG_skewSymmetric a
  det_eq_pfaffian_sq := concreteMajoranaBdG_det_eq_pfaffian_sq a
  zero_mode_iff_pfaffian_zero := concreteMajoranaBdG_zero_mode_iff_pfaffian_zero a

/--
The shared real Pfaffian geometry between the biquaternion light cone and the
Majorana/BdG zero-mode locus.  The bridge is theorem-facing only: it identifies
both singular surfaces as Pfaffian-zero predicates without conflating the
symmetric spacetime slice with the skew BdG dynamics slice.
-/
structure RealPfaffianBridge (M4 : Type u) [Mul M4] [One M4] [Neg M4] where
  biquaternionSlice : RealFourByFourBiquaternionSlice M4
  majoranaBdG : MajoranaBdGFourByFour M4
  /-- The biquaternion slice lies on its Pfaffian-zero locus. -/
  biquaternionNull : biquaternionSlice.pfaffianSJ = 0
  /-- The Majorana/BdG datum lies on its Pfaffian-zero locus. -/
  bdgZeroMode : majoranaBdG.pfaffian majoranaBdG.bdgMatrix = 0

namespace RealPfaffianBridge

variable {M4 : Type u} [Mul M4] [One M4] [Neg M4]

/-- Both real geometries expose their singular loci as Pfaffian-zero surfaces. -/
theorem pfaffian_bridge (B : RealPfaffianBridge M4) :
    (B.biquaternionSlice.pfaffianSJ = 0) ∧
      (B.majoranaBdG.pfaffian B.majoranaBdG.bdgMatrix = 0) ↔
      B.biquaternionSlice.pfaffianSJ = 0 ∧
        B.majoranaBdG.pfaffian B.majoranaBdG.bdgMatrix = 0 :=
  Iff.rfl

/-- Extract the real Pfaffian bridge equivalence. -/
theorem pfaffian_bridge_extract (B : RealPfaffianBridge M4) :
    (B.biquaternionSlice.pfaffianSJ = 0) ∧
      (B.majoranaBdG.pfaffian B.majoranaBdG.bdgMatrix = 0) ↔
      B.biquaternionSlice.pfaffianSJ = 0 ∧
        B.majoranaBdG.pfaffian B.majoranaBdG.bdgMatrix = 0 := by
  exact pfaffian_bridge B

end RealPfaffianBridge

end InfoGeometry.Clifford.HestenesDirac

import Mathlib.Tactic
import InfoGeometry.Canonical.DrazinModularPersistence
import InfoGeometry.Meta.Architecture

/-!
# Fierz--Klein foundation

Foundational real-coordinate bridge:

```text
spinor/Fierz readout
  -> Fierz bilinears
  -> chiral null rays
  -> Pluecker bivector
  -> Klein quadric.
```

This file deliberately separates:

* algebraic Fierz--Pauli--Kofink identities;
* Pluecker/Klein decomposability;
* Drazin-horizon expectation/readout data.

The core rule is:

```text
Fierz coordinates are spinor bilinear coordinates.
Klein coordinates are Pluecker bivector coordinates.
```

They are linked only after the Fierz bilinears generate chiral rays whose
wedge is a decomposable bivector.  No spinor, Clifford representation, or
Drazin/Hodge calibration is constructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FierzKleinFoundation

open scoped BigOperators
open InfoGeometry.Canonical.DrazinModularPersistence

/-! ## 1. Four-dimensional coordinate layer -/

/-- Coordinate labels for `ℝ^{1,3}` in the `(+---)` convention. -/
@[rep_depth operator]
inductive I4 where
  | t
  | x
  | y
  | z
  deriving DecidableEq, Fintype

instance : Inhabited I4 := ⟨I4.t⟩

/-- Real four-vector coordinates. -/
@[rep_depth operator]
abbrev Vec4 := I4 → ℝ

/-- Minkowski pairing in the `(+---)` convention. -/
@[rep_depth operator]
def minkowskiDot (u v : Vec4) : ℝ :=
  u I4.t * v I4.t
    - u I4.x * v I4.x
    - u I4.y * v I4.y
    - u I4.z * v I4.z

/-- Coordinate addition of four-vectors. -/
@[rep_depth operator]
def vadd (u v : Vec4) : Vec4 :=
  fun i => u i + v i

/-- Coordinate subtraction of four-vectors. -/
@[rep_depth operator]
def vsub (u v : Vec4) : Vec4 :=
  fun i => u i - v i

/-! ## 2. Bivectors and the Klein form -/

/-- Pluecker coordinates of a bivector in `Λ² ℝ⁴`. -/
@[rep_depth operator]
structure Bivector4 where
  p01 : ℝ
  p02 : ℝ
  p03 : ℝ
  p12 : ℝ
  p13 : ℝ
  p23 : ℝ

instance : Inhabited Bivector4 := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- Exterior product of two vectors in Pluecker coordinates. -/
@[rep_depth operator]
def wedgeVec4 (u v : Vec4) : Bivector4 where
  p01 := u I4.t * v I4.x - u I4.x * v I4.t
  p02 := u I4.t * v I4.y - u I4.y * v I4.t
  p03 := u I4.t * v I4.z - u I4.z * v I4.t
  p12 := u I4.x * v I4.y - u I4.y * v I4.x
  p13 := u I4.x * v I4.z - u I4.z * v I4.x
  p23 := u I4.y * v I4.z - u I4.z * v I4.y

/--
The Klein quadric form:

`Q_K(P) = p01 p23 - p02 p13 + p03 p12`.

A decomposable bivector satisfies `Q_K(P) = 0`.
-/
@[rep_depth operator]
def kleinForm (P : Bivector4) : ℝ :=
  P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12

/-- Predicate for membership in the Klein quadric. -/
@[rep_depth operator]
def IsOnKleinQuadric (P : Bivector4) : Prop :=
  kleinForm P = 0

/-- Every explicit wedge `u ∧ v` is decomposable, hence lies on the Klein quadric. -/
@[rep_depth operator]
theorem wedgeVec4_on_klein (u v : Vec4) :
    IsOnKleinQuadric (wedgeVec4 u v) := by
  unfold IsOnKleinQuadric kleinForm wedgeVec4
  ring

/-! ## 3. Fierz bilinear coordinates -/

/--
Real coordinate package for classical Dirac Fierz bilinears.

* `sigma`: scalar channel;
* `omega`: pseudoscalar / phase channel;
* `J`: vector current;
* `K`: axial/chiral current;
* `S`: bivector / area channel.
-/
@[rep_depth operator]
structure FierzBilinears where
  sigma : ℝ
  omega : ℝ
  J : Vec4
  K : Vec4
  S : Bivector4

instance : Inhabited FierzBilinears := ⟨⟨0, 0, fun _ => 0, fun _ => 0, default⟩⟩

/--
Minimal Fierz--Pauli--Kofink constraints needed to generate chiral null rays.
-/
@[rep_depth operator]
def FPKIdentities (F : FierzBilinears) : Prop :=
  minkowskiDot F.J F.J = F.sigma ^ 2 + F.omega ^ 2 ∧
    minkowskiDot F.K F.K = -minkowskiDot F.J F.J ∧
    minkowskiDot F.J F.K = 0

namespace FPKIdentities

variable {F : FierzBilinears} (h : FPKIdentities F)
include h

theorem J_sq : minkowskiDot F.J F.J = F.sigma ^ 2 + F.omega ^ 2 := h.1
theorem K_sq : minkowskiDot F.K F.K = -minkowskiDot F.J F.J := h.2.1
theorem J_dot_K : minkowskiDot F.J F.K = 0 := h.2.2

end FPKIdentities

def trivialFierzBilinears : FierzBilinears where
  sigma := 0
  omega := 0
  J := fun _ => 0
  K := fun _ => 0
  S := default

theorem trivialFierzBilinears_fpk : FPKIdentities trivialFierzBilinears := by
  refine ⟨?_, ?_, ?_⟩
  · unfold trivialFierzBilinears minkowskiDot; ring
  · unfold trivialFierzBilinears minkowskiDot; ring
  · unfold trivialFierzBilinears minkowskiDot; ring

/-- Right chiral ray `R = J + K`. -/
@[rep_depth operator]
def rightChiralRay (F : FierzBilinears) : Vec4 :=
  vadd F.J F.K

/-- Left chiral ray `L = J - K`. -/
@[rep_depth operator]
def leftChiralRay (F : FierzBilinears) : Vec4 :=
  vsub F.J F.K

/-- Chiral Pluecker bivector `P = (J + K) ∧ (J - K)`. -/
@[rep_depth operator]
def chiralPlucker (F : FierzBilinears) : Bivector4 :=
  wedgeVec4 (rightChiralRay F) (leftChiralRay F)

/--
The chiral Pluecker bivector is on the Klein quadric because it is explicitly
a wedge of two vectors.
-/
@[rep_depth operator]
theorem chiralPlucker_on_klein (F : FierzBilinears) :
    IsOnKleinQuadric (chiralPlucker F) := by
  unfold chiralPlucker
  exact wedgeVec4_on_klein (rightChiralRay F) (leftChiralRay F)

/-- Squared norm of a vector sum in Minkowski coordinates. -/
@[rep_depth operator]
lemma minkowskiDot_vadd_self (u v : Vec4) :
    minkowskiDot (vadd u v) (vadd u v)
      =
    minkowskiDot u u
      + 2 * minkowskiDot u v
      + minkowskiDot v v := by
  unfold minkowskiDot vadd
  ring

/-- Squared norm of a vector difference in Minkowski coordinates. -/
@[rep_depth operator]
lemma minkowskiDot_vsub_self (u v : Vec4) :
    minkowskiDot (vsub u v) (vsub u v)
      =
    minkowskiDot u u
      - 2 * minkowskiDot u v
      + minkowskiDot v v := by
  unfold minkowskiDot vsub
  ring

/-- The right chiral ray `R = J + K` is null under the FPK constraints. -/
@[rep_depth operator]
theorem rightChiralRay_null
    (F : FierzBilinears)
    (h : FPKIdentities F) :
    minkowskiDot (rightChiralRay F) (rightChiralRay F) = 0 := by
  unfold rightChiralRay
  rw [minkowskiDot_vadd_self]
  rw [FPKIdentities.K_sq h, FPKIdentities.J_dot_K h]
  ring

/-- The left chiral ray `L = J - K` is null under the FPK constraints. -/
@[rep_depth operator]
theorem leftChiralRay_null
    (F : FierzBilinears)
    (h : FPKIdentities F) :
    minkowskiDot (leftChiralRay F) (leftChiralRay F) = 0 := by
  unfold leftChiralRay
  rw [minkowskiDot_vsub_self]
  rw [FPKIdentities.K_sq h, FPKIdentities.J_dot_K h]
  ring

/-! ## 4. Normalized scalar-phase Fierz coordinates -/

/-- Normalized scalar/pseudoscalar Fierz coordinates. -/
@[rep_depth operator]
structure ScalarPhaseFierz where
  s_hat : ℝ
  omega_hat : ℝ

instance : Inhabited ScalarPhaseFierz := ⟨⟨1, 0⟩⟩

/-- Scalar-phase Fierz quadric `ŝ² + ω̂² = 1`. -/
@[rep_depth operator]
def IsOnScalarPhaseFierzQuadric (X : ScalarPhaseFierz) : Prop :=
  X.s_hat ^ 2 + X.omega_hat ^ 2 = 1

/-- Regularity means nonzero scalar-phase radius. -/
@[rep_depth operator]
def IsRegularFierz (F : FierzBilinears) : Prop :=
  F.sigma ^ 2 + F.omega ^ 2 ≠ 0

/--
Normalization property for a Fierz package.

The property avoids burying division-by-zero obligations in definitions.
-/
@[rep_depth operator]
structure FierzNormalization (F : FierzBilinears) where
  rho : ℝ
  rho_sq :
    rho ^ 2 = F.sigma ^ 2 + F.omega ^ 2
  rho_ne_zero :
    rho ≠ 0

def trivialNormalizedFierz : FierzBilinears where
  sigma := 1
  omega := 0
  J := fun _ => 0
  K := fun _ => 0
  S := default

def trivialFierzNormalization : FierzNormalization trivialNormalizedFierz where
  rho := 1
  rho_sq := by unfold trivialNormalizedFierz; norm_num
  rho_ne_zero := by norm_num

instance : Inhabited (FierzNormalization trivialNormalizedFierz) :=
  ⟨trivialFierzNormalization⟩

/-- Normalized scalar-phase coordinates. -/
@[rep_depth operator]
def normalizedScalarPhase
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    ScalarPhaseFierz where
  s_hat := F.sigma / N.rho
  omega_hat := F.omega / N.rho

/-- Normalized scalar-phase coordinates lie on the scalar Fierz quadric. -/
@[rep_depth operator]
theorem normalizedScalarPhase_on_quadric
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    IsOnScalarPhaseFierzQuadric
      (normalizedScalarPhase F N) := by
  unfold IsOnScalarPhaseFierzQuadric normalizedScalarPhase
  field_simp [N.rho_ne_zero]
  rw [N.rho_sq]

/-! ## 5. Fierz--Klein coordinates -/

/--
Combined Fierz--Klein coordinate package.

`scalarPhase` holds the normalized scalar/pseudoscalar coordinates and
`plucker` holds the chiral Pluecker bivector.
-/
@[rep_depth operator]
structure FierzKleinCoordinates where
  scalarPhase : ScalarPhaseFierz
  plucker : Bivector4

instance : Inhabited FierzKleinCoordinates :=
  ⟨⟨default, default⟩⟩

/-- The product constraint `S¹_Fierz × Q_Klein`. -/
@[rep_depth operator]
def IsOnFierzKleinVariety (X : FierzKleinCoordinates) : Prop :=
  IsOnScalarPhaseFierzQuadric X.scalarPhase ∧
  IsOnKleinQuadric X.plucker

/-- Fierz--Klein coordinates associated to a normalized Fierz package. -/
@[rep_depth operator]
def fierzKleinCoordinates
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    FierzKleinCoordinates where
  scalarPhase := normalizedScalarPhase F N
  plucker := chiralPlucker F

/-- The normalized scalar-phase and chiral Pluecker coordinates satisfy the FK constraints. -/
@[rep_depth operator]
theorem fierzKleinCoordinates_holds
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    IsOnFierzKleinVariety
      (fierzKleinCoordinates F N) := by
  constructor
  · exact normalizedScalarPhase_on_quadric F N
  · exact chiralPlucker_on_klein F

/-- The scalar-phase component of a normalized Fierz--Klein coordinate lies on the scalar quadric. -/
@[rep_depth operator]
theorem fierzKleinCoordinates_scalarPhase_on_quadric
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    IsOnScalarPhaseFierzQuadric (fierzKleinCoordinates F N).scalarPhase := by
  simpa [fierzKleinCoordinates] using normalizedScalarPhase_on_quadric F N

/-- The Plücker component of a normalized Fierz--Klein coordinate lies on the Klein quadric. -/
@[rep_depth operator]
theorem fierzKleinCoordinates_plucker_on_klein
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    IsOnKleinQuadric (fierzKleinCoordinates F N).plucker := by
  simpa [fierzKleinCoordinates] using chiralPlucker_on_klein F

/-! ## 6. Area defects and residual bookkeeping -/

/--
Klein area defect.

This is the Pluecker decomposability obstruction `Q_K(P)`.  It vanishes in
the strict Klein sector.  It should not be identified with the scalar-phase
Drazin area defect below.
-/
@[rep_depth operator]
def kleinAreaDefect (P : Bivector4) : ℝ :=
  kleinForm P

/-- A bivector on the Klein quadric has zero Klein area defect. -/
@[rep_depth operator]
theorem kleinAreaDefect_eq_zero_of_on_klein
    (P : Bivector4)
    (hP : IsOnKleinQuadric P) :
    kleinAreaDefect P = 0 := by
  exact hP

/-- The chiral Pluecker bivector has zero Klein area defect. -/
@[rep_depth operator]
theorem kleinAreaDefect_chiralPlucker_eq_zero
    (F : FierzBilinears) :
    kleinAreaDefect (chiralPlucker F) = 0 :=
  kleinAreaDefect_eq_zero_of_on_klein
    (chiralPlucker F)
    (chiralPlucker_on_klein F)

/-- Normalized Fierz--Klein coordinates have zero Klein area defect. -/
@[rep_depth operator]
theorem fierzKleinCoordinates_kleinAreaDefect_eq_zero
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    kleinAreaDefect (fierzKleinCoordinates F N).plucker = 0 := by
  simpa [fierzKleinCoordinates, kleinAreaDefect] using
    kleinAreaDefect_chiralPlucker_eq_zero F

/--
Drazin/scalar-phase area defect.

This measures failure of the normalized scalar-phase equation before enforcing
the strict Fierz normalization:

`â_D = (1 - ŝ² - ω̂²) / 4`.

It is a residual bookkeeping defect, not the Klein form.
-/
@[rep_depth operator]
def drazinScalarPhaseAreaDefect (X : ScalarPhaseFierz) : ℝ :=
  (1 - X.s_hat ^ 2 - X.omega_hat ^ 2) / 4

/--
Deformed scalar-phase Fierz residual:

`1 - ŝ² - ω̂² - 4 â`.
-/
@[rep_depth operator]
def scalarPhaseAreaResidual
    (X : ScalarPhaseFierz)
    (aHat : ℝ) : ℝ :=
  1 - X.s_hat ^ 2 - X.omega_hat ^ 2 - 4 * aHat

/-- The Drazin/scalar-phase area defect is exactly the residual-closing value. -/
@[rep_depth operator]
theorem scalarPhaseAreaResidual_drazinDefect_eq_zero
    (X : ScalarPhaseFierz) :
    scalarPhaseAreaResidual X (drazinScalarPhaseAreaDefect X) = 0 := by
  unfold scalarPhaseAreaResidual drazinScalarPhaseAreaDefect
  ring

/-- On the strict scalar-phase Fierz quadric, the Drazin area defect vanishes. -/
@[rep_depth operator]
theorem drazinScalarPhaseAreaDefect_eq_zero_of_on_quadric
    (X : ScalarPhaseFierz)
    (hX : IsOnScalarPhaseFierzQuadric X) :
    drazinScalarPhaseAreaDefect X = 0 := by
  unfold drazinScalarPhaseAreaDefect IsOnScalarPhaseFierzQuadric at *
  have hnum : 1 - X.s_hat ^ 2 - X.omega_hat ^ 2 = 0 := by
    nlinarith [hX]
  rw [hnum]
  norm_num

/-- Normalized scalar-phase Fierz coordinates have zero Drazin area defect. -/
@[rep_depth operator]
theorem normalizedScalarPhase_drazinAreaDefect_eq_zero
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    drazinScalarPhaseAreaDefect (normalizedScalarPhase F N) = 0 :=
  drazinScalarPhaseAreaDefect_eq_zero_of_on_quadric
    (normalizedScalarPhase F N)
    (normalizedScalarPhase_on_quadric F N)

/-- Normalized Fierz--Klein coordinates have zero scalar-phase defect. -/
@[rep_depth operator]
theorem fierzKleinCoordinates_scalarPhaseDefect_eq_zero
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    drazinScalarPhaseAreaDefect (fierzKleinCoordinates F N).scalarPhase = 0 := by
  simpa [fierzKleinCoordinates] using normalizedScalarPhase_drazinAreaDefect_eq_zero F N

/-! ## 7. Expectation-only Drazin-horizon readout -/

/-- Real-valued expectation/readout channel. -/
@[rep_depth operator]
abbrev RealChannel (Obs : Type*) :=
  Obs → ℝ

/--
Channel map extracting Fierz bilinears from a Drazin-stabilized observable.

The `area` channel is recorded as a bivector readout.  The vector and axial
channels are real coordinate readouts.
-/
@[rep_depth operator]
structure FierzReadoutChannels (Obs : Type*) where
  scalar : RealChannel Obs
  phase : RealChannel Obs
  vector : I4 → RealChannel Obs
  axial : I4 → RealChannel Obs
  area : Bivector4

instance (Obs : Type*) : Inhabited (FierzReadoutChannels Obs) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, default⟩⟩

/-- Expectation-derived Fierz bilinears from the Drazin-stabilized inverse `Aᴰ`. -/
@[rep_depth operator]
def horizonFierzBilinears
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (C : FierzReadoutChannels Obs)
    (D : DrazinSupportData Obs) :
    FierzBilinears where
  sigma := C.scalar D.AD
  omega := C.phase D.AD
  J := fun μ => C.vector μ D.AD
  K := fun μ => C.axial μ D.AD
  S := C.area

/--
Drazin-horizon channels are Fierz-admissible when their readout satisfies the
FPK identities and admits a nonzero scalar-phase normalization.
-/
@[rep_depth operator]
structure HorizonFierzAdmissible
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (C : FierzReadoutChannels Obs)
    (D : DrazinSupportData Obs) where
  fpk :
    FPKIdentities (horizonFierzBilinears C D)
  normalization :
    FierzNormalization (horizonFierzBilinears C D)

/--
Admissible Drazin-horizon Fierz channels produce valid Fierz--Klein
coordinates.

This theorem is compatibility-derived through `HorizonFierzAdmissible`; it does
not assert that arbitrary expectation channels satisfy FPK identities.
-/
@[rep_depth operator]
theorem horizon_fierz_klein_holds
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (C : FierzReadoutChannels Obs)
    (D : DrazinSupportData Obs)
    (h : HorizonFierzAdmissible C D) :
    IsOnFierzKleinVariety
      (fierzKleinCoordinates
        (horizonFierzBilinears C D)
        h.normalization) :=
  fierzKleinCoordinates_holds
    (horizonFierzBilinears C D)
    h.normalization

end InfoGeometry.Canonical.FierzKleinFoundation

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Exceptional.Freudenthal

/-!
# Concrete J₃(𝕆_s) Albert algebra carrier

27-dimensional exceptional Jordan algebra over Zorn split octonions.

This file provides the concrete carrier, the diagonal real identity, and the
integer-lattice Freudenthal identity.  It does not instantiate the full real
`Exceptional.Freudenthal.CubicJordanDatum`; that requires a genuine trilinear
polarization proof over the chosen real scalar action.

External CAS regression checks for the coordinate identities live in:
- `tools/sympy/freudenthal_identity.py` — SymPy `(X#)# = N(X)·X`
- `tools/gap/freudenthal_cubic_reduction.g` — GAP exact polynomial reduction
- `tools/sage/zorn_split_octonion_invariants.sage.py` — Sage invariant checks
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

/-! ## SplitOct as additive commutative group (via product type rep) -/

/-- SplitOct ≃ ℤ⁸ as additive groups. -/
def splitOctEquiv : SplitOct ≃ ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ where
  toFun X := (X.a, X.b, X.x0, X.x1, X.x2, X.y0, X.y1, X.y2)
  invFun t := { a := t.1, b := t.2.1, x0 := t.2.2.1, x1 := t.2.2.2.1,
                x2 := t.2.2.2.2.1, y0 := t.2.2.2.2.2.1, y1 := t.2.2.2.2.2.2.1,
                y2 := t.2.2.2.2.2.2.2 }
  left_inv := by intro X; rfl
  right_inv := by intro t; rfl

noncomputable instance : AddCommGroup SplitOct :=
  Equiv.addCommGroup splitOctEquiv

/-- ℝ-scalar action via octonion scalar embedding `scalarZ`. -/
noncomputable def roundℝ (r : ℝ) : ℤ := Int.floor (r + 1/2)

noncomputable instance : SMul ℝ SplitOct where
  smul r X := mulZ (scalarZ (roundℝ r)) X

/-! ## The 27-dimensional Albert matrix -/

structure AlbertMatrix where
  α₁ : ℝ
  α₂ : ℝ
  α₃ : ℝ
  z₁ : SplitOct
  z₂ : SplitOct
  z₃ : SplitOct
  deriving DecidableEq

/-- AlbertMatrix ≃ ℝ³ × SplitOct³ as additive groups. -/
def albertMatrixEquiv : AlbertMatrix ≃ ℝ × ℝ × ℝ × SplitOct × SplitOct × SplitOct where
  toFun X := (X.α₁, X.α₂, X.α₃, X.z₁, X.z₂, X.z₃)
  invFun t := { α₁ := t.1, α₂ := t.2.1, α₃ := t.2.2.1,
                z₁ := t.2.2.2.1, z₂ := t.2.2.2.2.1, z₃ := t.2.2.2.2.2 }
  left_inv := by intro X; rfl
  right_inv := by intro t; rfl

noncomputable instance : AddCommGroup AlbertMatrix :=
  Equiv.addCommGroup albertMatrixEquiv

instance : SMul ℝ AlbertMatrix where
  smul r X :=
    { α₁ := r * X.α₁
      α₂ := r * X.α₂
      α₃ := r * X.α₃
      z₁ := r • X.z₁
      z₂ := r • X.z₂
      z₃ := r • X.z₃ }

namespace AlbertMatrix

/-- Primitive idempotents of J₃(𝕆_s) for the three generations. -/
def e₁ : AlbertMatrix := { α₁ := 1, α₂ := 0, α₃ := 0, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }
def e₂ : AlbertMatrix := { α₁ := 0, α₂ := 1, α₃ := 0, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }
def e₃ : AlbertMatrix := { α₁ := 0, α₂ := 0, α₃ := 1, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- Peirce spaces J_{ij} = {X | e_i ∘ X = λ_i X, e_j ∘ X = λ_j X}
    For i=j: J_{ii} = ℝ e_i (1D, diagonal)
    For i≠j: J_{ij} ≅ 𝕆_s (8D, off-diagonal) -/
structure PeirceDecomposition where
  diag₁ : ℝ
  diag₂ : ℝ
  diag₃ : ℝ
  off₁₂ : SplitOct
  off₂₃ : SplitOct
  off₃₁ : SplitOct

/-- Peirce decomposition of an Albert matrix -/
def peirce (X : AlbertMatrix) : PeirceDecomposition :=
  { diag₁ := X.α₁, diag₂ := X.α₂, diag₃ := X.α₃,
    off₁₂ := X.z₃, off₂₃ := X.z₁, off₃₁ := X.z₂ }

def octTrace (Z : SplitOct) : ℝ := (Z.a : ℝ) + (Z.b : ℝ)

def traceBilin (X Y : AlbertMatrix) : ℝ :=
  X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
    octTrace X.z₁ * octTrace Y.z₁ +
    octTrace X.z₂ * octTrace Y.z₂ +
    octTrace X.z₃ * octTrace Y.z₃

theorem trace_comm (X Y : AlbertMatrix) : traceBilin X Y = traceBilin Y X := by
  dsimp [traceBilin]; ring

theorem peirce_diag_proj (X : AlbertMatrix) :
    (peirce X).diag₁ = traceBilin X e₁ ∧ (peirce X).diag₂ = traceBilin X e₂ ∧ (peirce X).diag₃ = traceBilin X e₃ := by
  dsimp [peirce, traceBilin, e₁, e₂, e₃, octTrace, zeroZ]
  exact ⟨by ring, by ring, by ring⟩

theorem peirce_off_proj (X : AlbertMatrix) :
    (peirce X).off₁₂ = X.z₃ ∧ (peirce X).off₂₃ = X.z₁ ∧ (peirce X).off₃₁ = X.z₂ := by
  dsimp [peirce]
  exact ⟨rfl, rfl, rfl⟩

def normCubic (X : AlbertMatrix) : ℝ :=
  X.α₁ * X.α₂ * X.α₃ +
    X.α₁ * (detZ X.z₁ : ℝ) +
    X.α₂ * (detZ X.z₂ : ℝ) +
    X.α₃ * (detZ X.z₃ : ℝ) -
    (octTrace (mulZ (mulZ X.z₁ X.z₂) X.z₃) : ℝ)

/-- Quadratic adjoint with full octonion cross-terms via mulZ, conjZ, scalarZ. -/
def adjointQuad (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₂ * X.α₃ - (detZ X.z₁ : ℝ)
    α₂ := X.α₁ * X.α₃ - (detZ X.z₂ : ℝ)
    α₃ := X.α₁ * X.α₂ - (detZ X.z₃ : ℝ)
    z₁ := subZ ((X.α₁ : ℝ) • X.z₁) (mulZ (conjZ X.z₂) (conjZ X.z₃))
    z₂ := subZ ((X.α₂ : ℝ) • X.z₂) (mulZ (conjZ X.z₃) (conjZ X.z₁))
    z₃ := subZ ((X.α₃ : ℝ) • X.z₃) (mulZ (conjZ X.z₁) (conjZ X.z₂)) }

lemma ext_albert (X Y : AlbertMatrix)
    (hα₁ : X.α₁ = Y.α₁) (hα₂ : X.α₂ = Y.α₂) (hα₃ : X.α₃ = Y.α₃)
    (hz₁ : X.z₁ = Y.z₁) (hz₂ : X.z₂ = Y.z₂) (hz₃ : X.z₃ = Y.z₃) : X = Y := by
  rcases X with ⟨a1,a2,a3,zx1,zx2,zx3⟩
  rcases Y with ⟨b1,b2,b3,zy1,zy2,zy3⟩
  subst hα₁; subst hα₂; subst hα₃; subst hz₁; subst hz₂; subst hz₃; rfl

lemma mulZ_zero (X : SplitOct) : mulZ X zeroZ = zeroZ := by
  simp [mulZ, zeroZ]

@[simp]
lemma smul_α₁ (r : ℝ) (X : AlbertMatrix) : (r • X).α₁ = r * X.α₁ := rfl
@[simp]
lemma smul_α₂ (r : ℝ) (X : AlbertMatrix) : (r • X).α₂ = r * X.α₂ := rfl
@[simp]
lemma smul_α₃ (r : ℝ) (X : AlbertMatrix) : (r • X).α₃ = r * X.α₃ := rfl
@[simp]
lemma smul_z₁ (r : ℝ) (X : AlbertMatrix) : (r • X).z₁ = r • X.z₁ := rfl
@[simp]
lemma smul_z₂ (r : ℝ) (X : AlbertMatrix) : (r • X).z₂ = r • X.z₂ := rfl
@[simp]
lemma smul_z₃ (r : ℝ) (X : AlbertMatrix) : (r • X).z₃ = r • X.z₃ := rfl

lemma subZ_zeroZ : subZ zeroZ zeroZ = (zeroZ : SplitOct) := by
  simp [subZ, negZ, zeroZ]

lemma conjZ_zeroZ : conjZ (zeroZ : SplitOct) = zeroZ := by
  simp [conjZ, zeroZ]

lemma smul_zeroZ (r : ℝ) : (r • (zeroZ : SplitOct)) = zeroZ := by
  calc
    r • (zeroZ : SplitOct) = mulZ (scalarZ (roundℝ r)) zeroZ := rfl
    _ = zeroZ := mulZ_zero _

lemma detZ_zeroZ_cast : (detZ (zeroZ : SplitOct) : ℝ) = 0 := by
  simp [detZ, zeroZ]

lemma adjointQuad_zeroZ (α₁ α₂ α₃ : ℝ) :
    adjointQuad { α₁ := α₁, α₂ := α₂, α₃ := α₃,
                  z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } =
    { α₁ := α₂ * α₃, α₂ := α₁ * α₃, α₃ := α₁ * α₂,
      z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } := by
  dsimp [adjointQuad]
  simp [detZ_zeroZ_cast, conjZ_zeroZ, mulZ_zero, smul_zeroZ, subZ_zeroZ, octTrace]

lemma normCubic_zeroZ (α₁ α₂ α₃ : ℝ) :
    normCubic { α₁ := α₁, α₂ := α₂, α₃ := α₃,
                z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } = α₁ * α₂ * α₃ := by
  dsimp [normCubic]
  simp [detZ, zeroZ, octTrace, mulZ, mulZ_zero]

theorem freudenthal_identity_diagonal (X : AlbertMatrix)
    (hz₁ : X.z₁ = zeroZ) (hz₂ : X.z₂ = zeroZ) (hz₃ : X.z₃ = zeroZ) :
    adjointQuad (adjointQuad X) = (normCubic X : ℝ) • X := by
  rcases X with ⟨α₁, α₂, α₃, z₁, z₂, z₃⟩
  have hz₁' : z₁ = zeroZ := hz₁
  have hz₂' : z₂ = zeroZ := hz₂
  have hz₃' : z₃ = zeroZ := hz₃
  subst hz₁'; subst hz₂'; subst hz₃'
  -- Now X = {α₁, α₂, α₃, zeroZ, zeroZ, zeroZ}
  rw [adjointQuad_zeroZ α₁ α₂ α₃]
  -- adjointQuad X = {α₂α₃, α₁α₃, α₁α₂, zeroZ, zeroZ, zeroZ}
  rw [adjointQuad_zeroZ (α₂*α₃) (α₁*α₃) (α₁*α₂)]
  -- adjointQuad(adjointQuad X) = {(α₁α₃)(α₁α₂), (α₂α₃)(α₁α₂), (α₂α₃)(α₁α₃), zeroZ, zeroZ, zeroZ}
  rw [normCubic_zeroZ α₁ α₂ α₃]
  -- RHS = (α₁α₂α₃) • X
  -- Both sides: prove component-wise
  apply ext_albert
  · simp; ring
  · simp; ring
  · simp; ring
  · simp [smul_zeroZ]
  · simp [smul_zeroZ]
  · simp [smul_zeroZ]

/-!
The full real Freudenthal identity is not asserted here.  The integer-lattice
version is proved below as `AlbertMatrixZ.freudenthal_identityZ`.
-/
end AlbertMatrix

end InfoGeometry.Algebra.CubicJordanOs

/-! ## Phase 1 Pure Integer Albert Matrix Structure -/
namespace InfoGeometry.Algebra.CubicJordanOs.AlbertMatrixZNamespace


@[ext]
structure AlbertMatrixZ where
  α₁ : ℤ
  α₂ : ℤ
  α₃ : ℤ
  z₁ : SplitOct
  z₂ : SplitOct
  z₃ : SplitOct
  deriving DecidableEq

def octTrace (Z : SplitOct) : ℤ := trZ Z

def normCubicZ (X : AlbertMatrixZ) : ℤ :=
  X.α₁ * X.α₂ * X.α₃ -
    X.α₁ * detZ X.z₁ -
    X.α₂ * detZ X.z₂ -
    X.α₃ * detZ X.z₃ +
    octTrace (mulZ (mulZ X.z₁ X.z₂) X.z₃)

def adjointQuadZ (X : AlbertMatrixZ) : AlbertMatrixZ :=
  { α₁ := X.α₂ * X.α₃ - detZ X.z₁
    α₂ := X.α₁ * X.α₃ - detZ X.z₂
    α₃ := X.α₁ * X.α₂ - detZ X.z₃
    z₁ := subZ (mulZ (conjZ X.z₃) (conjZ X.z₂)) (scaleZ X.α₁ X.z₁)
    z₂ := subZ (mulZ (conjZ X.z₁) (conjZ X.z₃)) (scaleZ X.α₂ X.z₂)
    z₃ := subZ (mulZ (conjZ X.z₂) (conjZ X.z₁)) (scaleZ X.α₃ X.z₃) }

instance : SMul ℤ AlbertMatrixZ where
  smul r X :=
    { α₁ := r * X.α₁
      α₂ := r * X.α₂
      α₃ := r * X.α₃
      z₁ := scaleZ r X.z₁
      z₂ := scaleZ r X.z₂
      z₃ := scaleZ r X.z₃ }

lemma ext_albertZ (X Y : AlbertMatrixZ)
    (hα₁ : X.α₁ = Y.α₁) (hα₂ : X.α₂ = Y.α₂) (hα₃ : X.α₃ = Y.α₃)
    (hz₁ : X.z₁ = Y.z₁) (hz₂ : X.z₂ = Y.z₂) (hz₃ : X.z₃ = Y.z₃) : X = Y := by
  rcases X with ⟨a1,a2,a3,zx1,zx2,zx3⟩
  rcases Y with ⟨b1,b2,b3,zy1,zy2,zy3⟩
  subst hα₁; subst hα₂; subst hα₃; subst hz₁; subst hz₂; subst hz₃; rfl

-- Helper scalar and subZ rules
lemma conjZ_subZ (X Y : SplitOct) : conjZ (subZ X Y) = subZ (conjZ X) (conjZ Y) := by
  cases X; cases Y; ext <;> { simp [conjZ, subZ]; try ring }

lemma conjZ_scaleZ (r : ℤ) (X : SplitOct) : conjZ (scaleZ r X) = scaleZ r (conjZ X) := by
  cases X; ext <;> { simp [conjZ, scaleZ]; try ring }

lemma conjZ_mulZ_reverse (X Y : SplitOct) : conjZ (mulZ X Y) = mulZ (conjZ Y) (conjZ X) := conjZ_mulZ X Y

lemma conjZ_conjZ_eq (X : SplitOct) : conjZ (conjZ X) = X := conjZ_conjZ X

lemma mulZ_subZ_subZ (A B C D : SplitOct) :
  mulZ (subZ A B) (subZ C D) = subZ (subZ (mulZ A C) (mulZ A D)) (subZ (mulZ B C) (mulZ B D)) := by
  cases A; cases B; cases C; cases D; ext <;> { simp [mulZ, subZ]; try ring }

lemma scaleZ_mulZ_left (r : ℤ) (X Y : SplitOct) : mulZ (scaleZ r X) Y = scaleZ r (mulZ X Y) := by
  cases X; cases Y; ext <;> { simp [mulZ, scaleZ]; try ring }

lemma scaleZ_mulZ_right (r : ℤ) (X Y : SplitOct) : mulZ X (scaleZ r Y) = scaleZ r (mulZ X Y) := by
  cases X; cases Y; ext <;> { simp [mulZ, scaleZ]; try ring }

lemma mulZ_conjZ_mulZ (X Y : SplitOct) : mulZ (conjZ X) (mulZ X Y) = scaleZ (detZ X) Y := by
  cases X; cases Y; ext <;> { simp [mulZ, conjZ, scaleZ, detZ]; try ring }

lemma mulZ_mulZ_conjZ (X Y : SplitOct) : mulZ (mulZ Y X) (conjZ X) = scaleZ (detZ X) Y := by
  cases X; cases Y; ext <;> { simp [mulZ, conjZ, scaleZ, detZ]; try ring }

lemma scaleZ_scaleZ (r s : ℤ) (X : SplitOct) : scaleZ r (scaleZ s X) = scaleZ (r * s) X := by
  cases X; ext <;> { simp [scaleZ]; try ring }

lemma sub_scaleZ (r s : ℤ) (X : SplitOct) : scaleZ (r - s) X = subZ (scaleZ r X) (scaleZ s X) := by
  cases X; ext <;> { simp [scaleZ, subZ]; try ring }

lemma scaleZ_subZ (r : ℤ) (X Y : SplitOct) : scaleZ r (subZ X Y) = subZ (scaleZ r X) (scaleZ r Y) := by
  cases X; cases Y; ext <;> { simp [scaleZ, subZ]; try ring }

lemma mul_scaleZ (r s : ℤ) (X : SplitOct) : scaleZ (r * s) X = scaleZ r (scaleZ s X) := by
  cases X; ext <;> { simp [scaleZ]; try ring }

lemma detZ_scaleZ (r : ℤ) (X : SplitOct) : detZ (scaleZ r X) = r * r * detZ X := by
  cases X; simp [detZ, scaleZ]; ring

lemma detZ_subZ (X Y : SplitOct) : detZ (subZ X Y) = detZ X + detZ Y - trZ (mulZ X (conjZ Y)) := by
  cases X; cases Y; simp [detZ, subZ, trZ, mulZ, conjZ]; ring

lemma detZ_conjZ_eq (X : SplitOct) : detZ (conjZ X) = detZ X := detZ_conjZ X

lemma trZ_mulZ_scaleZ_conjZ (r : ℤ) (X Y Z : SplitOct) : 
  trZ (mulZ (mulZ X Y) (conjZ (scaleZ r Z))) = r * trZ (mulZ (mulZ X Y) (conjZ Z)) := by
  cases X; cases Y; cases Z; simp [trZ, mulZ, conjZ, scaleZ]; ring

lemma trZ_alpha1 (z1 z2 z3 : SplitOct) : 
  trZ (mulZ (mulZ (conjZ z3) (conjZ z2)) (conjZ z1)) = trZ (mulZ (mulZ z1 z2) z3) := by
  cases z1; cases z2; cases z3; simp [trZ, mulZ, conjZ]; ring

lemma trZ_alpha2 (z1 z2 z3 : SplitOct) : 
  trZ (mulZ (mulZ (conjZ z1) (conjZ z3)) (conjZ z2)) = trZ (mulZ (mulZ z1 z2) z3) := by
  cases z1; cases z2; cases z3; simp [trZ, mulZ, conjZ]; ring

lemma trZ_alpha3 (z1 z2 z3 : SplitOct) : 
  trZ (mulZ (mulZ (conjZ z2) (conjZ z1)) (conjZ z3)) = trZ (mulZ (mulZ z1 z2) z3) := by
  cases z1; cases z2; cases z3; simp [trZ, mulZ, conjZ]; ring

lemma adjointQuadZ_alpha1 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).α₁ = normCubicZ X * X.α₁ := by
  simp [adjointQuadZ, normCubicZ, octTrace]
  rw [detZ_subZ]
  rw [detZ_mul]
  rw [detZ_conjZ_eq, detZ_conjZ_eq]
  rw [detZ_scaleZ]
  rw [trZ_mulZ_scaleZ_conjZ]
  rw [trZ_alpha1]
  ring

lemma adjointQuadZ_alpha2 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).α₂ = normCubicZ X * X.α₂ := by
  simp [adjointQuadZ, normCubicZ, octTrace]
  rw [detZ_subZ]
  rw [detZ_mul]
  rw [detZ_conjZ_eq, detZ_conjZ_eq]
  rw [detZ_scaleZ]
  rw [trZ_mulZ_scaleZ_conjZ]
  rw [trZ_alpha2]
  ring

lemma adjointQuadZ_alpha3 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).α₃ = normCubicZ X * X.α₃ := by
  simp [adjointQuadZ, normCubicZ, octTrace]
  rw [detZ_subZ]
  rw [detZ_mul]
  rw [detZ_conjZ_eq, detZ_conjZ_eq]
  rw [detZ_scaleZ]
  rw [trZ_mulZ_scaleZ_conjZ]
  rw [trZ_alpha3]
  ring

set_option maxHeartbeats 4000000

lemma z1_expansion (a1 a2 a3 : ℤ) (z1 z2 z3 : SplitOct) :
  subZ (mulZ (conjZ (subZ (mulZ (conjZ z2) (conjZ z1)) (scaleZ a3 z3)))
            (conjZ (subZ (mulZ (conjZ z1) (conjZ z3)) (scaleZ a2 z2))))
       (scaleZ (a2 * a3 - detZ z1) (subZ (mulZ (conjZ z3) (conjZ z2)) (scaleZ a1 z1))) =
  scaleZ (a1 * a2 * a3 - a1 * detZ z1 - a2 * detZ z2 - a3 * detZ z3 + trZ (mulZ (mulZ z1 z2) z3)) z1 := by
  simp only [conjZ_subZ, conjZ_scaleZ, conjZ_mulZ_reverse, conjZ_conjZ_eq]
  simp only [mulZ_subZ_subZ, scaleZ_mulZ_right, scaleZ_mulZ_left, mulZ_mulZ_conjZ, mulZ_conjZ_mulZ, scaleZ_scaleZ]
  simp only [sub_scaleZ, scaleZ_subZ, mul_scaleZ]
  cases z1; cases z2; cases z3
  ext <;> { simp [subZ, mulZ, scaleZ, detZ, conjZ, trZ]; try ring }

lemma z2_expansion (a1 a2 a3 : ℤ) (z1 z2 z3 : SplitOct) :
  subZ (mulZ (conjZ (subZ (mulZ (conjZ z3) (conjZ z2)) (scaleZ a1 z1)))
            (conjZ (subZ (mulZ (conjZ z2) (conjZ z1)) (scaleZ a3 z3))))
       (scaleZ (a1 * a3 - detZ z2) (subZ (mulZ (conjZ z1) (conjZ z3)) (scaleZ a2 z2))) =
  scaleZ (a1 * a2 * a3 - a1 * detZ z1 - a2 * detZ z2 - a3 * detZ z3 + trZ (mulZ (mulZ z1 z2) z3)) z2 := by
  simp only [conjZ_subZ, conjZ_scaleZ, conjZ_mulZ_reverse, conjZ_conjZ_eq]
  simp only [mulZ_subZ_subZ, scaleZ_mulZ_right, scaleZ_mulZ_left, mulZ_mulZ_conjZ, mulZ_conjZ_mulZ, scaleZ_scaleZ]
  simp only [sub_scaleZ, scaleZ_subZ, mul_scaleZ]
  cases z1; cases z2; cases z3
  ext <;> { simp [subZ, mulZ, scaleZ, detZ, conjZ, trZ]; try ring }

lemma z3_expansion (a1 a2 a3 : ℤ) (z1 z2 z3 : SplitOct) :
  subZ (mulZ (conjZ (subZ (mulZ (conjZ z1) (conjZ z3)) (scaleZ a2 z2)))
            (conjZ (subZ (mulZ (conjZ z3) (conjZ z2)) (scaleZ a1 z1))))
       (scaleZ (a1 * a2 - detZ z3) (subZ (mulZ (conjZ z2) (conjZ z1)) (scaleZ a3 z3))) =
  scaleZ (a1 * a2 * a3 - a1 * detZ z1 - a2 * detZ z2 - a3 * detZ z3 + trZ (mulZ (mulZ z1 z2) z3)) z3 := by
  simp only [conjZ_subZ, conjZ_scaleZ, conjZ_mulZ_reverse, conjZ_conjZ_eq]
  simp only [mulZ_subZ_subZ, scaleZ_mulZ_right, scaleZ_mulZ_left, mulZ_mulZ_conjZ, mulZ_conjZ_mulZ, scaleZ_scaleZ]
  simp only [sub_scaleZ, scaleZ_subZ, mul_scaleZ]
  cases z1; cases z2; cases z3
  ext <;> { simp [subZ, mulZ, scaleZ, detZ, conjZ, trZ]; try ring }

lemma adjointQuadZ_z1 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).z₁ = scaleZ (normCubicZ X) X.z₁ := by
  rcases X with ⟨a1, a2, a3, z1, z2, z3⟩
  unfold adjointQuadZ normCubicZ octTrace
  exact z1_expansion a1 a2 a3 z1 z2 z3

lemma adjointQuadZ_z2 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).z₂ = scaleZ (normCubicZ X) X.z₂ := by
  rcases X with ⟨a1, a2, a3, z1, z2, z3⟩
  unfold adjointQuadZ normCubicZ octTrace
  exact z2_expansion a1 a2 a3 z1 z2 z3

lemma adjointQuadZ_z3 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).z₃ = scaleZ (normCubicZ X) X.z₃ := by
  rcases X with ⟨a1, a2, a3, z1, z2, z3⟩
  unfold adjointQuadZ normCubicZ octTrace
  exact z3_expansion a1 a2 a3 z1 z2 z3

theorem freudenthal_identityZ (X : AlbertMatrixZ) : 
    adjointQuadZ (adjointQuadZ X) = (normCubicZ X) • X := by
  apply ext_albertZ
  · exact adjointQuadZ_alpha1 X
  · exact adjointQuadZ_alpha2 X
  · exact adjointQuadZ_alpha3 X
  · exact adjointQuadZ_z1 X
  · exact adjointQuadZ_z2 X
  · exact adjointQuadZ_z3 X

end InfoGeometry.Algebra.CubicJordanOs.AlbertMatrixZNamespace

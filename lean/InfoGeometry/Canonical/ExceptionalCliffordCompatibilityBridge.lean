import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge
import InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import InfoGeometry.Canonical.PACNativeCliffordBridge
import InfoGeometry.Algebra.SplitAlbertF4Classification

set_option linter.unusedSimpArgs false

/-!
# Split-Exceptional–Clifford Compatibility Boundary

This owner records the exact finite carrier and dimension compatibilities
available between the **split-real** exceptional Jordan/Zorn tower and the
Clifford/Witt tower.  The real-form convention is fixed by the split carriers:

* `𝔤₂(2)` comes from derivations/automorphisms of the real split octonions;
* `𝔣₄(4)` comes from derivations of the split Albert algebra `H₃(𝕆_s)`;
* `𝔢₆(6)` is the reduced-structure dimension over the same split Albert carrier;
* `𝔢₇(7)` is the split TKK/conformal 3-grading;
* `𝔢₈(8)` is the split Freudenthal/quasi-conformal 5-grading.

The file deliberately records only those carrier and dimension statements that
are currently theorem-backed.  It does not manufacture Lie-algebra
identifications or an exceptional-algebra representation intertwiner into the
`Cl(5,5)` spinor carrier.

1. **Split exceptional dimensions:**
   $$\dim \mathfrak g_{2(2)}=14,\quad
     \dim \mathfrak f_{4(4)}=52,\quad
     \dim \mathfrak e_{6(6)}=78,$$
   $$\dim \mathfrak e_{7(7)}=27+(78+1)+27=133,$$
   $$\dim \mathfrak e_{8(8)}=1+56+(133+1)+56+1=248.$$

2. **Carrier embedding** `W_{4,4} ↪ W_{5,5} = W_{4,4} ⊕ H`:
   $$\pi_{5,4}(\iota_{4,5}(x))=x.$$

3. **Split-octonion orthogonal chain:**
   $$\dim \mathfrak g_{2(2)}=14<\dim\mathfrak{so}(4,4)=28<
     \dim\mathfrak{so}(5,5)=45.$$
-/

noncomputable section

namespace InfoGeometry.Canonical.ExceptionalCliffordCompatibilityBridge

open Matrix
open ProjectiveAffineConformalClosure55
open CanonicalZornProjectiveTKKBridge
open InfoGeometry.Algebra.F4Classification

/-- Dimension of the real split `𝔤₂(2) = Der(𝕆_s)`. -/
def dim_g2_split : ℕ := 14

/-- Dimension of the split Albert algebra `H₃(𝕆_s)`. -/
def dim_albert_J3 : ℕ := dimAlbertAlgebra

/-- Dimension of `𝔣₄(4) = Der(H₃(𝕆_s))`, read from the split-Albert owner. -/
def dim_f44 : ℕ := dimF4Derivations

/-- Dimension of the traceless split Albert carrier. -/
def dim_albert_traceless : ℕ := 26

/-- Dimension of the reduced structure algebra `𝔢₆(6)` of split `H₃(𝕆_s)`. -/
def dim_e66 : ℕ := dim_f44 + dim_albert_traceless

/-- Grade-zero dimension in the split `𝔢₇(7)` TKK 3-grading. -/
def dim_g0_e7 : ℕ := dim_e66 + 1

/-- Split `𝔢₇(7)` TKK dimension. -/
def dim_e77 : ℕ := dim_albert_J3 + dim_g0_e7 + dim_albert_J3

/-- The split-octonion derivation dimension is `14`. -/
theorem g2_split_dim_exact : dim_g2_split = 14 := by
  rfl

/-- The split Albert derivation algebra has dimension `52`, hence the `F₄(4)` ledger. -/
theorem f44_dim_exact : dim_f44 = 52 := by
  exact f4_derivation_dimension_eq_52

/-- The reduced structure dimension over split Albert is `52 + 26 = 78`. -/
theorem e66_dim_exact : dim_e66 = 78 := by
  rw [dim_e66, dim_f44, dim_albert_traceless]
  exact congrArg (fun n => n + 26) f4_derivation_dimension_eq_52

/-- Exact split TKK grading dimension `27 + (78 + 1) + 27 = 133`. -/
theorem e77_dim_exact : dim_e77 = 133 := by
  simp [dim_e77, dim_g0_e7, dim_albert_J3, dim_e66, dim_f44,
    dim_albert_traceless, dimAlbertAlgebra, dimRealDiagonal,
    numOffDiagonalSectors, dimSplitOctonions, dimF4Derivations,
    dimSO8LieAlgebra]

/-- Freudenthal charge carrier dimension for the split Albert algebra. -/
def dim_freudenthal_56 : ℕ := 56

/-- Grade-zero dimension in the split `𝔢₈(8)` five-grading. -/
def dim_g0_e8 : ℕ := dim_e77 + 1

/-- Split `𝔢₈(8)` quasi-conformal dimension. -/
def dim_e88 : ℕ := 1 + dim_freudenthal_56 + dim_g0_e8 + dim_freudenthal_56 + 1

/-- Exact split Freudenthal five-grading dimension `1 + 56 + 134 + 56 + 1 = 248`. -/
theorem e88_dim_exact : dim_e88 = 248 := by
  simp [dim_e88, dim_g0_e8, dim_e77, dim_g0_e7, dim_albert_J3,
    dim_e66, dim_f44, dim_albert_traceless, dim_freudenthal_56,
    dimAlbertAlgebra, dimRealDiagonal, numOffDiagonalSectors,
    dimSplitOctonions, dimF4Derivations, dimSO8LieAlgebra]

/-- Strict dimension growth along the split exceptional tower. -/
theorem split_exceptional_dimension_chain :
    dim_g2_split < dim_f44 ∧ dim_f44 < dim_e66 ∧
      dim_e66 < dim_e77 ∧ dim_e77 < dim_e88 := by
  norm_num [dim_g2_split, dim_f44, dim_e66, dim_e77, dim_g0_e7,
    dim_e88, dim_g0_e8, dim_albert_J3, dim_albert_traceless,
    dim_freudenthal_56, dimAlbertAlgebra, dimRealDiagonal,
    numOffDiagonalSectors, dimSplitOctonions, dimF4Derivations,
    dimSO8LieAlgebra]

/-- 8-dimensional split-octonion / `W_{4,4}` carrier. -/
abbrev Carrier8 := InfoGeometry.Algebra.FiniteSpin.Vec8R

/-- 10-dimensional `W_{5,5}` carrier = `W_{4,4} ⊕ H`. -/
abbrev Carrier10 := InfoGeometry.Algebra.FiniteSpin.Vec10R

/-- Canonical embedding `ι_{4,5} : W_{4,4} ↪ W_{5,5}`. -/
def embed4to5 (x : Carrier8) : Carrier10 :=
  fun i =>
    if h : i.val < 8 then
      x ⟨i.val, h⟩
    else
      0

/-- Left-inverse projection `π_{5,4} : W_{5,5} ↠ W_{4,4}`. -/
def project5to4 (y : Carrier10) : Carrier8 :=
  fun i => y ⟨i.val, by omega⟩

/-- Exact left-invertibility of the Witt carrier embedding. -/
theorem project_embed_id (x : Carrier8) :
    project5to4 (embed4to5 x) = x := by
  ext i
  dsimp [project5to4, embed4to5]
  have hlt : i.val < 8 := i.isLt
  simp [hlt]

/-- Orthogonal dimension chain attached to the split-octonion carrier. -/
def dim_so44 : ℕ := 28
def dim_so55 : ℕ := 45

theorem lie_subalgebra_hierarchy :
    dim_g2_split < dim_so44 ∧ dim_so44 < dim_so55 := by
  decide

/-! Coordinate identity readout on the 8D Peirce carrier.  The actual
    8D-to-10D carrier embedding is `project_embed_id`; a
    split-exceptional-to-spinor representation map remains a separate target. -/
def peirceCarrierIdentityReadout : Carrier8 ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  LinearEquiv.refl ℝ (Fin 8 → ℝ)

/-! ## The full finite chiral carrier readback

`Carrier8` is deliberately the existing eight-slot coordinate carrier.  The
maps below identify it with the already-owned `PACSplit44` and real Zorn
coordinates.  They do not add a second octonion multiplication or a second
Clifford carrier.
-/

def pac44ToCarrier8 (x : PACSplit44) : Carrier8 :=
  ![x.x0, x.x1, x.x2, x.x3, x.y0, x.y1, x.y2, x.y3]

def carrier8ToPAC44 (x : Carrier8) : PACSplit44 where
  x0 := x 0
  x1 := x 1
  x2 := x 2
  x3 := x 3
  y0 := x 4
  y1 := x 5
  y2 := x 6
  y3 := x 7

theorem carrier8ToPAC44_pac44ToCarrier8 (x : PACSplit44) :
    carrier8ToPAC44 (pac44ToCarrier8 x) = x := by
  cases x
  rfl

theorem pac44ToCarrier8_carrier8ToPAC44 (x : Carrier8) :
    pac44ToCarrier8 (carrier8ToPAC44 x) = x := by
  funext i
  fin_cases i <;> rfl

noncomputable def pac44Carrier8Equiv : PACSplit44 ≃ Carrier8 where
  toFun := pac44ToCarrier8
  invFun := carrier8ToPAC44
  left_inv := carrier8ToPAC44_pac44ToCarrier8
  right_inv := pac44ToCarrier8_carrier8ToPAC44

def carrier8Quadratic (x : Carrier8) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 -
    (x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2)

theorem carrier8Quadratic_pac44 (x : PACSplit44) :
    carrier8Quadratic (pac44ToCarrier8 x) = Q44 x := by
  simp [carrier8Quadratic, pac44ToCarrier8, Q44]

noncomputable def zornToCarrier8Equiv : ZornCore.Zorn ≃ Carrier8 :=
  CanonicalZornProjectiveTKKBridge.pac44CoreZornEquiv.symm.trans
    pac44Carrier8Equiv

theorem zornToCarrier8Equiv_quadratic (X : ZornCore.Zorn) :
    carrier8Quadratic (zornToCarrier8Equiv X) = ZornCore.det X := by
  change carrier8Quadratic
      (pac44ToCarrier8
        (CanonicalZornProjectiveTKKBridge.coreZornToPAC44 X)) =
    ZornCore.det X
  rw [carrier8Quadratic_pac44]
  exact CanonicalZornProjectiveTKKBridge.coreZornToPAC44_Q44 X

theorem zornToCarrier8Equiv_injective :
    Function.Injective zornToCarrier8Equiv :=
  zornToCarrier8Equiv.injective

theorem zornToCarrier8Equiv_surjective :
    Function.Surjective zornToCarrier8Equiv :=
  zornToCarrier8Equiv.surjective

theorem zornToCarrier8Equiv_null_iff (X : ZornCore.Zorn) :
    carrier8Quadratic (zornToCarrier8Equiv X) = 0 ↔
      ZornCore.det X = 0 := by
  rw [zornToCarrier8Equiv_quadratic]

theorem carrier8ToPAC44_apply (x : Carrier8) :
    carrier8ToPAC44 x =
      { x0 := x 0, x1 := x 1, x2 := x 2, x3 := x 3,
        y0 := x 4, y1 := x 5, y2 := x 6, y3 := x 7 } := rfl

/-! ## Affine-chart readback into the native null Clifford carrier

The following map uses the existing conformal affine section.  It is a map
on chosen representatives, not a map from projective equivalence classes to
individual Clifford elements.
-/

def carrier8NativeNullVector (x : Carrier8) :
    InfoGeometry.Clifford.Clifford55.V55 :=
  InfoGeometry.Canonical.PACNativeCliffordBridge.pac44NativeNullVector
    (carrier8ToPAC44 x)

theorem carrier8NativeNullVector_Q55 (x : Carrier8) :
    InfoGeometry.Clifford.Clifford55.Q55 (carrier8NativeNullVector x) = 0 := by
  exact InfoGeometry.Canonical.PACNativeCliffordBridge.pac44NativeNullVector_Q55
    (carrier8ToPAC44 x)

theorem carrier8NativeNullClifford_sq_zero (x : Carrier8) :
    InfoGeometry.Clifford.Clifford55.ι55 (carrier8NativeNullVector x) *
        InfoGeometry.Clifford.Clifford55.ι55 (carrier8NativeNullVector x) = 0 := by
  exact InfoGeometry.Canonical.PACNativeCliffordBridge.pac44NativeNullClifford_sq_zero
    (carrier8ToPAC44 x)

end InfoGeometry.Canonical.ExceptionalCliffordCompatibilityBridge

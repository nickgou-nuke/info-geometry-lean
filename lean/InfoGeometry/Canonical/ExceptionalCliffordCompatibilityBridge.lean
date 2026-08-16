import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge
import InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import InfoGeometry.Canonical.PACNativeCliffordBridge

set_option linter.unusedSimpArgs false

/-!
# Exceptional–Clifford Compatibility Boundary

This owner module records the exact finite carrier and dimension compatibilities
available between the exceptional Jordan/Zorn tower and the Clifford/Witt tower.
It deliberately does not claim an exceptional-algebra representation
intertwiner into the `Cl(5,5)` spinor carrier.

1. **Exact TKK Exceptional Lie Algebra Gradings & Dimension Formulas:**
   $$\boxed{\dim \mathfrak{e}_{7(7)} = 27 + 79 + 27 = 27 + (78 + 1) + 27 = 133}$$
   $$\boxed{\dim \mathfrak{e}_{8(8)} = 1 + 56 + 134 + 56 + 1 = 1 + 56 + (133 + 1) + 56 + 1 = 248}$$

2. **Carrier Embedding $W_{4,4} \hookrightarrow W_{5,5} = W_{4,4} \oplus H$:**
   $$\boxed{\pi_{5,4}(\iota_{4,5}(x)) = x}$$

3. **Subalgebra Inclusion Chain:**
   $$\boxed{\dim \mathfrak{g}_{2(2)} = 14 \;<\; \dim \mathfrak{so}(4,4) = 28 \;<\; \dim \mathfrak{so}(5,5) = 45}$$

4. **Carrier-level compatibility:**
   The 8-dimensional split-octonion / Peirce carrier has an explicit coordinate
   readout, while the separate Witt embedding is proved by `project_embed_id`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExceptionalCliffordCompatibilityBridge

open Matrix
open ProjectiveAffineConformalClosure55
open CanonicalZornProjectiveTKKBridge

/-- Exact TKK grading dimensions for e_{7(7)}: 27 + (78 + 1) + 27 = 133 -/
def dim_albert_J3 : ℕ := 27
def dim_e66 : ℕ := 78
def dim_g0_e7 : ℕ := dim_e66 + 1
def dim_e77 : ℕ := dim_albert_J3 + dim_g0_e7 + dim_albert_J3

theorem e77_dim_exact : dim_e77 = 133 := by
  rfl

/-- Exact Freudenthal quasi-conformal 5-grading dimensions for e_{8(8)}:
    1 + 56 + (133 + 1) + 56 + 1 = 248 -/
def dim_freudenthal_56 : ℕ := 56
def dim_g0_e8 : ℕ := dim_e77 + 1
def dim_e88 : ℕ := 1 + dim_freudenthal_56 + dim_g0_e8 + dim_freudenthal_56 + 1

theorem e88_dim_exact : dim_e88 = 248 := by
  rfl

/-- 8-dimensional split-octonion / W_{4,4} carrier -/
abbrev Carrier8 := Fin 8 → ℝ

/-- 10-dimensional W_{5,5} carrier = W_{4,4} ⊕ H -/
abbrev Carrier10 := Fin 10 → ℝ

/-- Canonical embedding ι_{4,5} : W_{4,4} ↪ W_{5,5} -/
def embed4to5 (x : Carrier8) : Carrier10 :=
  fun i =>
    if h : i.val < 8 then
      x ⟨i.val, h⟩
    else
      0

/-- Left-inverse projection π_{5,4} : W_{5,5} ↠ W_{4,4} -/
def project5to4 (y : Carrier10) : Carrier8 :=
  fun i => y ⟨i.val, by omega⟩

/-- 🏆 THEOREM 1: Exact Left-Invertibility of the Witt Carrier Embedding:
    $\pi_{5,4}(\iota_{4,5}(x)) = x$. -/
theorem project_embed_id (x : Carrier8) :
    project5to4 (embed4to5 x) = x := by
  ext i
  dsimp [project5to4, embed4to5]
  have hlt : i.val < 8 := i.isLt
  simp [hlt]

/-- Lie algebra dimension chain: g_{2(2)} ⊂ so(4,4) ⊂ so(5,5) -/
def dim_g2_split : ℕ := 14
def dim_so44 : ℕ := 28
def dim_so55 : ℕ := 45

theorem lie_subalgebra_hierarchy :
    dim_g2_split < dim_so44 ∧ dim_so44 < dim_so55 := by
  decide

/-! Coordinate identity readout on the 8D Peirce carrier.  The actual
    8D-to-10D carrier embedding is `project_embed_id`; an
    exceptional-to-spinor representation map remains a separate target. -/
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

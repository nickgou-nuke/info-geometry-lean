import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.SplitOctonionDAGHodgeIntertwinerBridge
import InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge

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

end InfoGeometry.Canonical.ExceptionalCliffordCompatibilityBridge

import proofs.PenroseSpinIncidenceTessellation
import proofs.TKKJordanPairData

/-!
# Klein quadric / Erlangen 2.0 / Grothendieck bridge

Theorem-honest finite layer:

* prove the Plucker polynomial bookkeeping for the Klein quadric in `P^5`;
* reuse the already-proved five-grade TKK arithmetic;
* connect the `K₃` incidence tile to Klein/Erlangen/motivic sockets without
  asserting the analytic/geometric/Langlands conclusions as proved.
-/

namespace KleinErlangenGrothendieckBridge

open TKKJordanPairData.Legacy
open PenroseSpinIncidenceTessellation
open PenroseSpinTilingConfig

/-- Affine Plucker coordinates for `Gr(2,4) ⊂ P^5` in the order
`01,02,03,12,13,23`. -/
structure Plucker6 where
  p01 : ℤ
  p02 : ℤ
  p03 : ℤ
  p12 : ℤ
  p13 : ℤ
  p23 : ℤ
  deriving DecidableEq, Repr

/-- Klein-quadric Plucker polynomial.  Projectively this is
`p01 p23 - p02 p13 + p03 p12 = 0`. -/
def kleinPlucker (P : Plucker6) : ℤ :=
  P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12

/-- Predicate for the affine cone over the Klein quadric. -/
def OnKleinQuadric (P : Plucker6) : Prop := kleinPlucker P = 0

/-- Decomposable coordinate plane `span(e₀,e₁)` lies on the Klein quadric. -/
def line01 : Plucker6 :=
  { p01 := 1, p02 := 0, p03 := 0, p12 := 0, p13 := 0, p23 := 0 }

/-- Decomposable coordinate plane `span(e₂,e₃)` lies on the Klein quadric. -/
def line23 : Plucker6 :=
  { p01 := 0, p02 := 0, p03 := 0, p12 := 0, p13 := 0, p23 := 1 }

/-- A nontrivial decomposable example: `(e₀+e₂)∧(e₁+e₃)`. -/
def mixedLine : Plucker6 :=
  { p01 := 1, p02 := 0, p03 := 1, p12 := -1, p13 := 0, p23 := 1 }

@[simp] theorem klein_line01 : OnKleinQuadric line01 := rfl
@[simp] theorem klein_line23 : OnKleinQuadric line23 := rfl
@[simp] theorem klein_mixedLine : OnKleinQuadric mixedLine := rfl

/-- Scaling preserves the affine Klein-cone equation. -/
theorem kleinPlucker_smul (a : ℤ) (P : Plucker6) :
    kleinPlucker
      { p01 := a * P.p01, p02 := a * P.p02, p03 := a * P.p03,
        p12 := a * P.p12, p13 := a * P.p13, p23 := a * P.p23 } =
      a ^ 2 * kleinPlucker P := by
  unfold kleinPlucker
  ring

/-- Hence the Klein-quadric cone condition is projectively well-defined. -/
theorem onKleinQuadric_smul {a : ℤ} {P : Plucker6} (hP : OnKleinQuadric P) :
    OnKleinQuadric
      { p01 := a * P.p01, p02 := a * P.p02, p03 := a * P.p03,
        p12 := a * P.p12, p13 := a * P.p13, p23 := a * P.p23 } := by
  unfold OnKleinQuadric
  rw [kleinPlucker_smul, hP]
  ring

/-- Finite Erlangen datum: a transformation is accepted when it preserves the
Klein Plucker equation on the finite test alphabet.  This is a finite skeleton,
not the full conformal group. -/
structure FiniteErlangenTest where
  transform : Plucker6 → Plucker6
  preservesLine01 : OnKleinQuadric (transform line01)
  preservesLine23 : OnKleinQuadric (transform line23)
  preservesMixedLine : OnKleinQuadric (transform mixedLine)

/-- Identity transformation passes the finite Erlangen test. -/
def identityErlangenTest : FiniteErlangenTest where
  transform := id
  preservesLine01 := klein_line01
  preservesLine23 := klein_line23
  preservesMixedLine := klein_mixedLine

/-- The `K₃` incidence tile still supplies six local alpha/beta labels at the
Erlangen/Klein bridge. -/
theorem k3_generators_remain_six : Fintype.card SpinTileGenerator = 6 :=
  PenroseSpinTilingConfig.spinTileGenerator_card

/-- The TKK five-grade arithmetic still exposes the conformal pairing
`g₋₁ × g₁ → g₀`. -/
theorem tkk_conformal_pairing_grade : gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 :=
  TKKJordanPairData.Legacy.gradeAdd_m1_p1

/-- Capstone: finite Klein/Plucker, TKK-grade, and K3-incidence facts compile. -/
theorem klein_erlangen_grothendieck_synthesis :
    OnKleinQuadric line01 ∧
    OnKleinQuadric line23 ∧
    OnKleinQuadric mixedLine ∧
    Fintype.card SpinTileGenerator = 6 ∧
    gradeAdd TKKGrade.m1 TKKGrade.p1 = some TKKGrade.z0 := by
  exact ⟨klein_line01, klein_line23, klein_mixedLine, k3_generators_remain_six,
    tkk_conformal_pairing_grade⟩

end KleinErlangenGrothendieckBridge

import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-- Canonical basis vectors for factored coordinate recovery. -/
def vx0 : SplitOctF2 := basis8 2
def vx1 : SplitOctF2 := basis8 3
def vy2 : SplitOctF2 := basis8 7

/-- Group action of a word w = pc1^b0 * ... * pc6^b5 on a vector X. -/
def applyWord (b0 b1 b2 b3 b4 b5 : Bool) (X : SplitOctF2) : SplitOctF2 :=
  let X := if b5 then pc6Fun X else X
  let X := if b4 then pc5Fun X else X
  let X := if b3 then pc4Fun X else X
  let X := if b2 then pc3Fun X else X
  let X := if b1 then pc2Fun X else X
  let X := if b0 then pc1Fun X else X
  X

/-- Factored coordinate extraction for bit b0 from W(y2).x0 -/
def rec_b0 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  (applyWord b0 b1 b2 b3 b4 b5 vy2).x0

/-- Factored coordinate extraction for bit b1 from W(x0).x1 -/
def rec_b1 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  (applyWord b0 b1 b2 b3 b4 b5 vx0).x1

/-- Factored coordinate extraction for bit b2 from W(y2).x1 -/
def rec_b2 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  (applyWord b0 b1 b2 b3 b4 b5 vy2).x1

/-- Factored coordinate extraction for bit b4 from W(x0).y1 -/
def rec_b4 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  let b0' := rec_b0 b0 b1 b2 b3 b4 b5
  let b1' := rec_b1 b0 b1 b2 b3 b4 b5
  let b2' := rec_b2 b0 b1 b2 b3 b4 b5
  (applyWord b0 b1 b2 b3 b4 b5 vx0).y1 ^^ (b0' && b1') ^^ b1' ^^ b2'

/-- Factored coordinate extraction for bit b3 from W(x1).x2 -/
def rec_b3 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  let b0' := rec_b0 b0 b1 b2 b3 b4 b5
  let b1' := rec_b1 b0 b1 b2 b3 b4 b5
  let b2' := rec_b2 b0 b1 b2 b3 b4 b5
  let b4' := rec_b4 b0 b1 b2 b3 b4 b5
  (applyWord b0 b1 b2 b3 b4 b5 vx1).x2 ^^ (b0' && b1') ^^ (b0' && b2') ^^ (b0' && b4') ^^ b0' ^^ b1' ^^ b2' ^^ b4'

/-- Factored coordinate extraction for bit b5 from W(x0).x2 -/
def rec_b5 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  let b0' := rec_b0 b0 b1 b2 b3 b4 b5
  let b1' := rec_b1 b0 b1 b2 b3 b4 b5
  let b2' := rec_b2 b0 b1 b2 b3 b4 b5
  let b4' := rec_b4 b0 b1 b2 b3 b4 b5
  (applyWord b0 b1 b2 b3 b4 b5 vx0).x2 ^^ (b0' && b1' && b2') ^^ (b0' && b1' && b4') ^^ (b0' && b2') ^^ (b2' && b4')

/-- Lemma 1: Exact factored recovery of bit 0. -/
theorem recover_b0_eq (b0 b1 b2 b3 b4 b5 : Bool) :
    rec_b0 b0 b1 b2 b3 b4 b5 = b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

/-- Lemma 2: Exact factored recovery of bit 1. -/
theorem recover_b1_eq (b0 b1 b2 b3 b4 b5 : Bool) :
    rec_b1 b0 b1 b2 b3 b4 b5 = b1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

/-- Lemma 3: Exact factored recovery of bit 2. -/
theorem recover_b2_eq (b0 b1 b2 b3 b4 b5 : Bool) :
    rec_b2 b0 b1 b2 b3 b4 b5 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

/-- Lemma 4: Exact factored recovery of bit 4. -/
theorem recover_b4_eq (b0 b1 b2 b3 b4 b5 : Bool) :
    rec_b4 b0 b1 b2 b3 b4 b5 = b4 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

/-- Lemma 5: Exact factored recovery of bit 3. -/
theorem recover_b3_eq (b0 b1 b2 b3 b4 b5 : Bool) :
    rec_b3 b0 b1 b2 b3 b4 b5 = b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

/-- Lemma 6: Exact factored recovery of bit 5. -/
theorem recover_b5_eq (b0 b1 b2 b3 b4 b5 : Bool) :
    rec_b5 b0 b1 b2 b3 b4 b5 = b5 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

/-- 🏆 THEOREM: The 6-bit unipotent word action on the 8-basis is strictly injective. -/
theorem applyWord_injective (b0 b1 b2 b3 b4 b5 c0 c1 c2 c3 c4 c5 : Bool)
    (h : ∀ v, applyWord b0 b1 b2 b3 b4 b5 v = applyWord c0 c1 c2 c3 c4 c5 v) :
    (b0, b1, b2, b3, b4, b5) = (c0, c1, c2, c3, c4, c5) := by
  have h_vx0 := h vx0
  have h_vx1 := h vx1
  have h_vy2 := h vy2
  have h0 : b0 = c0 := by
    rw [← recover_b0_eq b0 b1 b2 b3 b4 b5, ← recover_b0_eq c0 c1 c2 c3 c4 c5]
    dsimp [rec_b0]
    rw [h_vy2]
  have h1 : b1 = c1 := by
    rw [← recover_b1_eq b0 b1 b2 b3 b4 b5, ← recover_b1_eq c0 c1 c2 c3 c4 c5]
    dsimp [rec_b1]
    rw [h_vx0]
  have h2 : b2 = c2 := by
    rw [← recover_b2_eq b0 b1 b2 b3 b4 b5, ← recover_b2_eq c0 c1 c2 c3 c4 c5]
    dsimp [rec_b2]
    rw [h_vy2]
  have h4 : b4 = c4 := by
    rw [← recover_b4_eq b0 b1 b2 b3 b4 b5, ← recover_b4_eq c0 c1 c2 c3 c4 c5]
    dsimp [rec_b4, rec_b0, rec_b1, rec_b2]
    rw [h_vx0, h_vy2]
  have h3 : b3 = c3 := by
    rw [← recover_b3_eq b0 b1 b2 b3 b4 b5, ← recover_b3_eq c0 c1 c2 c3 c4 c5]
    dsimp [rec_b3, rec_b4, rec_b0, rec_b1, rec_b2]
    rw [h_vx0, h_vx1, h_vy2]
  have h5 : b5 = c5 := by
    rw [← recover_b5_eq b0 b1 b2 b3 b4 b5, ← recover_b5_eq c0 c1 c2 c3 c4 c5]
    dsimp [rec_b5, rec_b4, rec_b0, rec_b1, rec_b2]
    rw [h_vx0, h_vy2]
  subst h0 h1 h2 h3 h4 h5
  rfl

end InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

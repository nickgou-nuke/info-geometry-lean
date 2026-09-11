/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

/-!
# The full coordinate root carrier and Weyl reflections

The positive roots are not closed under a simple reflection.  This owner
therefore uses the full signed coordinate carrier and only then defines the
finite Weyl action and its genuine inversion set.
-/

namespace InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

def phiMinus : Finset (ℤ × ℤ) :=
  phiPlus.image (fun v => (-v.1, -v.2))

def phi : Finset (ℤ × ℤ) := phiPlus ∪ phiMinus

abbrev G2CoordinateRoot := {x : ℤ × ℤ // x ∈ phi}

/-! The real Cartan charge readout of a signed coordinate root.  The subtype
  proof is deliberately irrelevant to the readout: only the canonical
  integer pair carries the two Cartan coordinates. -/
def g2CoordinateCharge (x : G2CoordinateRoot) : Fin 2 → ℝ := fun i =>
  if i = 0 then (x.1.1 : ℝ) else (x.1.2 : ℝ)

@[simp] theorem g2CoordinateCharge_zero (x : G2CoordinateRoot) :
    g2CoordinateCharge x 0 = (x.1.1 : ℝ) := by
  simp [g2CoordinateCharge]

@[simp] theorem g2CoordinateCharge_one (x : G2CoordinateRoot) :
    g2CoordinateCharge x 1 = (x.1.2 : ℝ) := by
  simp [g2CoordinateCharge]

def positiveRootInFullCarrier (α : G2PositiveRoot) : G2CoordinateRoot :=
  ⟨rootCoordinates α, by
    exact Finset.mem_union_left _ (rootCoordinateEquiv α).property⟩

def signedRootCoordinate (r : Bool × G2PositiveRoot) : G2CoordinateRoot :=
  if r.1 then
    ⟨((-rootCoordinates r.2).1, (-rootCoordinates r.2).2), by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨rootCoordinates r.2, (rootCoordinateEquiv r.2).property, rfl⟩⟩
  else
    positiveRootInFullCarrier r.2

theorem signedRootCoordinate_bijective :
    Function.Bijective signedRootCoordinate := by
  classical
  decide

noncomputable def signedRootCoordinateEquiv :
    Bool × G2PositiveRoot ≃ G2CoordinateRoot :=
  Equiv.ofBijective signedRootCoordinate signedRootCoordinate_bijective

@[simp] theorem signedRootCoordinateEquiv_apply
    (r : Bool × G2PositiveRoot) :
    signedRootCoordinateEquiv r = signedRootCoordinate r := rfl

theorem signedRootCoordinateEquiv_symm_apply_signed
    (r : Bool × G2PositiveRoot) :
    signedRootCoordinateEquiv.symm (signedRootCoordinate r) = r := by
  apply signedRootCoordinateEquiv.injective
  simp [signedRootCoordinateEquiv_apply]

theorem phiPlus_disjoint_phiMinus : Disjoint phiPlus phiMinus := by
  decide

def isPositive (α : G2CoordinateRoot) : Prop := α.1 ∈ phiPlus

def isNegative (α : G2CoordinateRoot) : Prop := α.1 ∈ phiMinus

theorem s1_mem_phi {v : ℤ × ℤ} (hv : v ∈ phi) : s1 v ∈ phi := by
  classical
  simp only [phi, Finset.mem_union, phiPlus, phiMinus, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with hv | ⟨u, hu, rfl⟩
  · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [s1]
  · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [s1]

theorem s2_mem_phi {v : ℤ × ℤ} (hv : v ∈ phi) : s2 v ∈ phi := by
  classical
  simp only [phi, Finset.mem_union, phiPlus, phiMinus, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at hv ⊢
  rcases hv with hv | ⟨u, hu, rfl⟩
  · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [s2]
  · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [s2]

def s1Root : G2CoordinateRoot ≃ G2CoordinateRoot where
  toFun x := ⟨s1 x.1, s1_mem_phi x.2⟩
  invFun x := ⟨s1 x.1, s1_mem_phi x.2⟩
  left_inv x := Subtype.ext (s1_involutive x.1)
  right_inv x := Subtype.ext (s1_involutive x.1)

def s2Root : G2CoordinateRoot ≃ G2CoordinateRoot where
  toFun α := ⟨s2 α.1, s2_mem_phi α.2⟩
  invFun α := ⟨s2 α.1, s2_mem_phi α.2⟩
  left_inv α := Subtype.ext (s2_involutive α.1)
  right_inv α := Subtype.ext (s2_involutive α.1)

theorem s1Root_involutive (α : G2CoordinateRoot) : s1Root (s1Root α) = α :=
  s1Root.left_inv α

theorem s2Root_involutive (α : G2CoordinateRoot) : s2Root (s2Root α) = α :=
  s2Root.left_inv α

theorem s1Root_sq : s1Root ^ 2 = 1 := by
  apply Equiv.ext
  intro α
  exact s1Root_involutive α

theorem s2Root_sq : s2Root ^ 2 = 1 := by
  apply Equiv.ext
  intro α
  exact s2Root_involutive α

theorem s1_rootNeg (v : ℤ × ℤ) :
    s1 (-v.1, -v.2) = (-((s1 v).1), -((s1 v).2)) := by
  rcases v with ⟨a, b⟩
  dsimp [s1]
  ring_nf

theorem s2_rootNeg (v : ℤ × ℤ) :
    s2 (-v.1, -v.2) = (-((s2 v).1), -((s2 v).2)) := by
  rcases v with ⟨a, b⟩
  dsimp [s2]
  ring_nf

def cRoot : G2CoordinateRoot ≃ G2CoordinateRoot := s1Root.trans s2Root

@[simp] theorem cRoot_apply (α : G2CoordinateRoot) :
    cRoot α = s2Root (s1Root α) := rfl

theorem cRoot_pow_six : cRoot ^ 6 = 1 := by
  decide

def coordinateWeylAction (w : WeylG2) : G2CoordinateRoot ≃ G2CoordinateRoot :=
  if w.2 then s1Root * cRoot ^ w.1.val else cRoot ^ w.1.val

@[simp] theorem coordinateWeylAction_one :
    coordinateWeylAction (0, false) = 1 := by
  simp [coordinateWeylAction]

@[simp] theorem coordinateWeylAction_cyclic_one :
    coordinateWeylAction (1, false) = cRoot := by
  change cRoot ^ (1 : ℕ) = cRoot
  simp

noncomputable def inversionRoots (w : WeylG2) : Finset G2PositiveRoot := by
  classical
  exact Finset.univ.filter (fun α =>
    isNegative ((coordinateWeylAction w).symm
      (positiveRootInFullCarrier α)))

theorem mem_inversionRoots_iff (w : WeylG2) (α : G2PositiveRoot) :
    α ∈ inversionRoots w ↔
      isNegative ((coordinateWeylAction w).symm
        (positiveRootInFullCarrier α)) := by
  classical
  simp [inversionRoots]

theorem inversionRoots_one : inversionRoots (0, false) = ∅ := by
  classical
  ext α
  cases α <;>
    simp [inversionRoots, coordinateWeylAction, positiveRootInFullCarrier,
      isNegative, phiMinus, phiPlus,
      InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge.rootCoordinates]

end InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

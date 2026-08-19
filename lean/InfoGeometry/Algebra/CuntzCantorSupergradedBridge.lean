import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Canonical.CantorCuntzBasis

/-!
# Cuntz--Cantor supergraded bridge

This module connects the finite wallpaper/SUSY matrix shadow to the binary
Cuntz-Cantor word recursion.

The theorem surface is intentionally finite:

* a one-bit Cuntz/Cantor branch word has odd `ZMod 2` length parity;
* a two-bit branch word has even parity;
* concatenating two one-bit odd steps gives an even word;
* the quotient Cuntz supercharge packet is exposed separately;
* the wallpaper matrix anticommutator is exposed separately.

It does not prove physical supersymmetry, a Hilbert-space Cuntz representation,
or a continuum spacetime theorem.

#### BUCKET 1: CLOSED FINITE THEOREMS

`oddStep_parity`, `evenTwoStep_parity`, `wordParityZ2_append`,
`odd_odd_concat_even`, and `cuntz_odd_odd_generates_even_translation_packet`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

Full Cuntz `O₂` representation theory, super-Poincare covariance, and physical
SUSY interpretations remain outside this finite word-parity bridge.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzCantorSupergradedBridge

open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Algebra.SupergradedSUSY
open InfoGeometry.Algebra.CuntzSuperalgebra

/-- Binary Cuntz/Cantor word parity, read in `ZMod 2`. -/
def wordParityZ2 (w : List Bool) : ZMod 2 :=
  (w.length : ZMod 2)

/-- A single Cuntz branch step. -/
def oddStep (b : Bool) : List Bool :=
  [b]

/-- A two-step Cuntz branch word. -/
def evenTwoStep (a b : Bool) : List Bool :=
  [a, b]

/-- A one-bit Cuntz branch word is odd. -/
@[simp] theorem wordParityZ2_nil :
    wordParityZ2 ([] : List Bool) = 0 := by
  rfl

@[simp] theorem wordParityZ2_append (u v : List Bool) :
    wordParityZ2 (u ++ v) = wordParityZ2 u + wordParityZ2 v := by
  simp [wordParityZ2]

theorem oddStep_parity (b : Bool) :
    wordParityZ2 (oddStep b) = 1 := by
  change (1 : ZMod 2) = 1
  rfl

@[simp] theorem oddStep_append_oddStep (a b : Bool) :
    oddStep a ++ oddStep b = evenTwoStep a b := by
  rfl

/-- Two odd one-bit Cuntz steps compose to an even two-bit word. -/
theorem odd_odd_concat_even (a b : Bool) :
    wordParityZ2 (oddStep a ++ oddStep b) = 0 := by
  calc
    wordParityZ2 (oddStep a ++ oddStep b) =
        wordParityZ2 (oddStep a) + wordParityZ2 (oddStep b) :=
      wordParityZ2_append _ _
    _ = (1 : ZMod 2) + 1 := by rw [oddStep_parity, oddStep_parity]
    _ = 0 := odd_add_odd_grade_even

/-- A two-bit Cuntz branch word is even. -/
theorem evenTwoStep_parity (a b : Bool) :
    wordParityZ2 (evenTwoStep a b) = 0 := by
  rw [← oddStep_append_oddStep a b]
  exact odd_odd_concat_even a b

/-! ## Cantor orbit readouts -/

/-- The branch operator selected by one binary Cantor digit. -/
def branchOperator {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (b : Bool) : Op :=
  if b then InfoGeometry.Topology.CuntzO2Carrier.S_right C
    else InfoGeometry.Topology.CuntzO2Carrier.S_left C

@[simp] theorem orbit_oddStep
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (seed : Op) (b : Bool) :
    InfoGeometry.Canonical.CantorCuntzBasis.orbit C seed (oddStep b) =
      branchOperator C b * seed := by
  simpa [oddStep, branchOperator] using
    (InfoGeometry.Canonical.CantorCuntzBasis.orbit_branch_recursion C seed b [])

@[simp] theorem orbit_evenTwoStep
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (seed : Op) (a b : Bool) :
    InfoGeometry.Canonical.CantorCuntzBasis.orbit C seed (evenTwoStep a b) =
      branchOperator C a * (branchOperator C b * seed) := by
  cases a <;> cases b <;>
    simp [evenTwoStep, branchOperator,
      InfoGeometry.Canonical.CantorCuntzBasis.orbit]

@[simp] theorem cuntzMajoranaSupercharge_odd
    (n : ℕ) (i : Fin n) :
    parity n (cuntzMajoranaSupercharge n i) =
      -cuntzMajoranaSupercharge n i := by
  exact parity_cuntzMajoranaSupercharge n i

@[simp] theorem cuntzSuperMomentum_even
    (n : ℕ) (i : Fin n) :
    parity n (cuntzSuperMomentum n i) =
      cuntzSuperMomentum n i := by
  exact parity_cuntzSuperMomentum n i

theorem cuntz_odd_odd_generates_even_momentum_packet
    (n : ℕ) (i : Fin n) :
    parity n (cuntzMajoranaSupercharge n i) =
        -cuntzMajoranaSupercharge n i ∧
      parity n (cuntzSuperMomentum n i) =
        cuntzSuperMomentum n i ∧
      algebraicAnticommutator
          (cuntzMajoranaSupercharge n i)
          (cuntzMajoranaSupercharge n i) =
        (2 : ℂ) • cuntzSuperMomentum n i := by
  exact ⟨cuntzMajoranaSupercharge_odd n i,
    cuntzSuperMomentum_even n i,
    cuntz_anticommutator_generates_momentum n i⟩

theorem cuntz_odd_odd_generates_even_translation_packet
    (n : ℕ) (i : Fin n) :
    parity n (cuntzSuperMomentum n i) = cuntzSuperMomentum n i ∧
      algebraicAnticommutator
          (cuntzMajoranaSupercharge n i)
          (cuntzMajoranaSupercharge n i) =
        (2 : ℂ) • cuntzSuperMomentum n i := by
  exact ⟨parity_cuntzSuperMomentum n i,
    cuntz_anticommutator_generates_momentum n i⟩

/-! ## Independent wallpaper matrix readout -/

/-- The wallpaper glide relation, separate from quotient momentum. -/
theorem wallpaper_glide_self_anticommutator_generates_translation :
    superAnticommutator InfoGeometry.Topology.KANWallpaper.G
        InfoGeometry.Topology.KANWallpaper.G =
      (2 : ℝ) • InfoGeometry.Topology.KANWallpaper.T_x := by
  exact susy_anticommutator_generates_two_smul_momentum

end InfoGeometry.Algebra.CuntzCantorSupergradedBridge

end noncomputable section

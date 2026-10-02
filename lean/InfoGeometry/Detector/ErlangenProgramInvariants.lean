import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.ErlangenProgramInvariants

class KleinGeometry (G X : Type*) where
  smul : G → X → X

def IsKleinInvariant {G X Y : Type*} [KleinGeometry G X] (f : X → Y) : Prop :=
  ∀ g x, f (KleinGeometry.smul (G := G) (X := X) g x) = f x

structure DetectorState where
  slope : ℝ
  volume : ℝ

noncomputable def dilationAction (s : ℝ) (state : DetectorState) : DetectorState where
  slope := (Real.sqrt s)⁻¹ * state.slope
  volume := s * state.volume

noncomputable def apollonianInvariant (state : DetectorState) : ℝ :=
  state.slope * Real.sqrt state.volume

theorem apollonianInvariant_dilation (s : ℝ) (state : DetectorState)
    (hs : 0 < s) : apollonianInvariant (dilationAction s state) =
      apollonianInvariant state := by
  dsimp [apollonianInvariant, dilationAction]
  rw [Real.sqrt_mul (le_of_lt hs)]
  have hsqrt : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  calc
    (Real.sqrt s)⁻¹ * state.slope * (Real.sqrt s * Real.sqrt state.volume) =
        ((Real.sqrt s)⁻¹ * Real.sqrt s) *
          (state.slope * Real.sqrt state.volume) := by ring
    _ = state.slope * Real.sqrt state.volume := by
      rw [inv_mul_cancel₀ hsqrt]
      ring

structure DFFTriad where
  H : ℝ
  D : ℝ
  K : ℝ

def casimir (triad : DFFTriad) : ℝ := triad.H * triad.K - triad.D ^ 2

noncomputable def nullTriad (x p : ℝ) : DFFTriad where
  H := (1 / 2) * p ^ 2
  D := (1 / 2) * x * p
  K := (1 / 2) * x ^ 2

theorem nullTriad_casimir (x p : ℝ) : casimir (nullTriad x p) = 0 := by
  simp [casimir, nullTriad]
  ring

def reflection (x : ℝ) : ℝ := 1 - x

def symmetricCapacity (x : ℝ) : ℝ := x * (1 - x)

theorem symmetricCapacity_reflection (x : ℝ) :
    symmetricCapacity (reflection x) = symmetricCapacity x := by
  simp [symmetricCapacity, reflection]
  ring

theorem reflection_fixed_iff (x : ℝ) : reflection x = x ↔ x = 1 / 2 := by
  simp only [reflection]
  constructor <;> intro h
  · linarith
  · rw [h]
    norm_num

noncomputable def carnotPrimitive (x : ℝ) : ℝ := x ^ 2 / 2 - x ^ 3 / 3

theorem carnotPrimitive_unit_interval :
    carnotPrimitive 1 - carnotPrimitive 0 = 1 / 6 := by
  norm_num [carnotPrimitive]

inductive Archetype
  | erlangenGeometry
  | dilationInvariant
  | nullCasimir
  | modularFixedPoint
  | masterSynthesis
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .erlangenGeometry => 170
  | .dilationInvariant => 171
  | .nullCasimir => 172
  | .modularFixedPoint => 173
  | .masterSynthesis => 174

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .erlangenGeometry .dilationInvariant ∧
    causallyPrecedes .dilationInvariant .nullCasimir ∧
    causallyPrecedes .nullCasimir .modularFixedPoint ∧
    causallyPrecedes .modularFixedPoint .masterSynthesis := by
  norm_num [causallyPrecedes, rank]

theorem master_invariants (s a V x p : ℝ) (hs : 0 < s) :
    apollonianInvariant (dilationAction s ⟨a, V⟩) =
      apollonianInvariant ⟨a, V⟩ ∧
    casimir (nullTriad x p) = 0 ∧
    reflection (1 / 2) = 1 / 2 ∧
    carnotPrimitive 1 - carnotPrimitive 0 = 1 / 6 := by
  exact ⟨apollonianInvariant_dilation s ⟨a, V⟩ hs,
    nullTriad_casimir x p,
    (reflection_fixed_iff (1 / 2)).mpr rfl,
    carnotPrimitive_unit_interval⟩

end DetectorGeometry.ErlangenProgramInvariants

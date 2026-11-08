import InfoGeometry.Analysis.TwoSheetPoleCancellation
import InfoGeometry.Canonical.FiniteSuperchargePairing
import InfoGeometry.Topology.TwistedCohomologyWeyl

/-!
# Reflected chiral poles and finite residue balance

The sheet label and its swap come from `TwistedCohomologyWeyl`.
Local coefficients are certified by punctured limits.  A finite set of
punctures closed under the reflected deck involution has zero total
coefficient when the scalar fields obey the stated seam law.

The integer sign-monodromy character supplies an exact algebraic meaning
for one-loop sign reversal.  It is not a construction of a compact Riemann
surface, a branched cover, or a physical evolution through a seam.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetResiduePairing

open InfoGeometry.Topology.Weyl
open InfoGeometry.Analysis.BipolarSimplePoleResidues
open scoped BigOperators

/-- Sheet exchange accompanied by reflection of the local complex coordinate. -/
def reflectedDeck (c : ℂ) (p : ChiralSheet × ℂ) : ChiralSheet × ℂ :=
  (p.1.swap, c - p.2)

@[simp] theorem reflectedDeck_involutive (c : ℂ) (p : ChiralSheet × ℂ) :
    reflectedDeck c (reflectedDeck c p) = p := by
  rcases p with ⟨sh, z⟩
  cases sh <;> simp [reflectedDeck]

/-- The lift has no fixed point, including over the fixed base coordinate. -/
theorem reflectedDeck_ne (c : ℂ) (p : ChiralSheet × ℂ) :
    reflectedDeck c p ≠ p := by
  intro h
  have hs := congrArg Prod.fst h
  rcases p with ⟨sh, z⟩
  cases sh <;> simp [reflectedDeck, ChiralSheet.swap] at hs

/-- Constructed reflected partner of an arbitrary scalar field. -/
def pairedField (c : ℂ) (f : ℂ → ℂ) : ChiralSheet → ℂ → ℂ
  | .plus => f
  | .minus => fun z => f (c - z)

def pairedCenter (c a : ℂ) : ChiralSheet → ℂ
  | .plus => a
  | .minus => c - a

def pairedCoefficient (r : ℂ) : ChiralSheet → ℂ
  | .plus => r
  | .minus => -r

/-- Both coefficients are derived from the same actual local limit. -/
theorem pairedField_hasCoefficient {f : ℂ → ℂ} {a r : ℂ}
    (h : HasSimplePoleCoefficientAt f a r) (c : ℂ) (sh : ChiralSheet) :
    HasSimplePoleCoefficientAt (pairedField c f sh)
      (pairedCenter c a sh) (pairedCoefficient r sh) := by
  cases sh
  · exact h
  · exact h.reflection c

theorem pairedField_seam (c : ℂ) (f : ℂ → ℂ) (sh : ChiralSheet) (z : ℂ) :
    pairedField c f sh.swap z = pairedField c f sh (c - z) := by
  cases sh <;> simp [pairedField, ChiralSheet.swap]

/-- The deck involution reverses the derived residue readout. -/
theorem pairedCoefficient_swap (r : ℂ) (sh : ChiralSheet) :
    pairedCoefficient r sh.swap = -pairedCoefficient r sh := by
  cases sh <;> simp [pairedCoefficient, ChiralSheet.swap]

/-- Exact finite orbit cancellation, using native `Finset.sum_involution`.
Closure under the involution and the field seam law are explicit hypotheses. -/
theorem finite_residue_balance (c : ℂ) (S : Finset (ChiralSheet × ℂ))
    (u : ChiralSheet → ℂ → ℂ) (residue : ChiralSheet × ℂ → ℂ)
    (hclosed : ∀ p ∈ S, reflectedDeck c p ∈ S)
    (hlocal : ∀ p ∈ S, HasSimplePoleCoefficientAt (u p.1) p.2 (residue p))
    (hseam : ∀ sh z, u sh.swap z = u sh (c - z)) :
    ∑ p ∈ S, residue p = 0 := by
  apply Finset.sum_involution (fun p _ => reflectedDeck c p)
  · intro p hp
    exact twin_pole_cancellation (hlocal p hp)
      (hlocal (reflectedDeck c p) (hclosed p hp)) (hseam p.1)
  · intro p _ _
    exact reflectedDeck_ne c p
  · exact hclosed
  · intro p _
    exact reflectedDeck_involutive c p

/-- A genuine representation of the integer loop group by sign units. -/
def signMonodromy : Multiplicative ℤ →* ℂˣ where
  toFun n := (-1 : ℂˣ) ^ Multiplicative.toAdd n
  map_one' := by simp
  map_mul' n m := by
    exact zpow_add (-1 : ℂˣ) (Multiplicative.toAdd n) (Multiplicative.toAdd m)

@[simp] theorem signMonodromy_one_loop :
    signMonodromy (Multiplicative.ofAdd (1 : ℤ)) = -1 := by
  simp [signMonodromy]

@[simp] theorem signMonodromy_two_loops :
    signMonodromy (Multiplicative.ofAdd (2 : ℤ)) = 1 := by
  apply Units.ext
  norm_num [signMonodromy]

/-- Sign holonomy preserves amplitude norm; it is not a dissipative law. -/
theorem one_loop_norm_preserved (z : ℂ) :
    ‖(signMonodromy (Multiplicative.ofAdd (1 : ℤ)) : ℂ) * z‖ = ‖z‖ := by
  simp

end InfoGeometry.Canonical.TwoSheetResiduePairing

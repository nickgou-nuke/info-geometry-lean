import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittPinAction
import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores

/-!
# Six-channel chiral colour readout in `Cl(5,5)`

This file packages the already existing first-three CAR pairs as one
operator-valued six-channel readout.  It is deliberately a readout layer:
it does not assert a multiplicative embedding of the non-associative Zorn
algebra into the associative Clifford algebra.  The colour labels below are
only a chosen convention for the first three Witt slots.
-/

namespace InfoGeometry.Canonical.Cl55ChiralSolderingReadout

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical

noncomputable section

def ChiralIndex := Bool × Fin 3

/-- The six chiral labels, with `true` denoting the plus sheet. -/
noncomputable def chiralReadout (s : ChiralIndex) : Cl55 :=
  if s.1 then chiralPlus55 s.2 else chiralMinus55 s.2

/- The colours are assigned to the first three Witt slots by convention;
   this is not a global identification of nonassociative carriers. -/
def colourFin3Equiv : SplitOctonionColour ≃ Fin 3 where
  toFun
    | .red => 0
    | .green => 1
    | .blue => 2
  invFun
    | 0 => .red
    | 1 => .green
    | 2 => .blue
  left_inv := by
    intro c
    cases c <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

noncomputable def colourChiralReadout (s : Bool) (c : SplitOctonionColour) : Cl55 :=
  chiralReadout (s, colourFin3Equiv c)

noncomputable def chiralVectorReadout (s : ChiralIndex) : V55 :=
  if s.1 then
    (1 / 2 : ℝ) • nbar_pair (Fin.castAdd 2 s.2)
  else
    (1 / 2 : ℝ) • n_pair (Fin.castAdd 2 s.2)

@[simp] theorem colourChiralReadout_red (s : Bool) :
    colourChiralReadout s .red = chiralReadout (s, 0) := by
  rfl

@[simp] theorem colourChiralReadout_green (s : Bool) :
    colourChiralReadout s .green = chiralReadout (s, 1) := by
  rfl

@[simp] theorem colourChiralReadout_blue (s : Bool) :
    colourChiralReadout s .blue = chiralReadout (s, 2) := by
  rfl

@[simp] theorem chiralReadout_plus (i : Fin 3) :
    chiralReadout (true, i) = chiralPlus55 i := by
  simp [chiralReadout]

@[simp] theorem chiralReadout_minus (i : Fin 3) :
    chiralReadout (false, i) = chiralMinus55 i := by
  simp [chiralReadout]

@[simp] theorem chiralReadout_sq (s : ChiralIndex) :
    chiralReadout s * chiralReadout s = 0 := by
  cases s with
  | mk b i =>
      cases b <;> simp [chiralReadout]

@[simp] theorem ι55_chiralVectorReadout (s : ChiralIndex) :
    ι55 (chiralVectorReadout s) = chiralReadout s := by
  cases s with
  | mk b i =>
      cases b <;>
        simp [chiralVectorReadout, chiralReadout, chiralPlus55,
          chiralMinus55, creation55, annihilation55]

theorem plus_anticommutator (i j : Fin 3) :
    chiralReadout (true, i) * chiralReadout (true, j) +
        chiralReadout (true, j) * chiralReadout (true, i) = 0 := by
  simpa [chiralReadout] using chiralPlus55_anticommutator i j

theorem minus_anticommutator (i j : Fin 3) :
    chiralReadout (false, i) * chiralReadout (false, j) +
        chiralReadout (false, j) * chiralReadout (false, i) = 0 := by
  simpa [chiralReadout] using chiralMinus55_anticommutator i j

theorem mixed_anticommutator (i j : Fin 3) :
    chiralReadout (false, i) * chiralReadout (true, j) +
        chiralReadout (true, j) * chiralReadout (false, i) =
      if i = j then 1 else 0 := by
  simpa [chiralReadout] using chiralMinus55_plus55_anticommutator i j

theorem chiralReadout_anticommutator (s t : ChiralIndex) :
    chiralReadout s * chiralReadout t + chiralReadout t * chiralReadout s =
      if s.1 = t.1 then 0 else if s.2 = t.2 then 1 else 0 := by
  cases s with
  | mk sb si =>
      cases t with
      | mk tb ti =>
          cases sb <;> cases tb
          · simpa using minus_anticommutator si ti
          · simpa [chiralReadout] using mixed_anticommutator si ti
          · simpa [chiralReadout] using chiralPlus55_minus55_anticommutator si ti
          · simpa using plus_anticommutator si ti

theorem plus_commutator_mem_grade_two (i j : Fin 3) :
    chiralReadout (true, i) * chiralReadout (true, j) -
        chiralReadout (true, j) * chiralReadout (true, i) ∈
      cl55GradeSubmodule 2 := by
  simpa [chiralReadout] using chiralPlus55_commutator_mem_grade_two i j

theorem minus_commutator_mem_grade_neg_two (i j : Fin 3) :
    chiralReadout (false, i) * chiralReadout (false, j) -
        chiralReadout (false, j) * chiralReadout (false, i) ∈
      cl55GradeSubmodule (-2) := by
  simpa [chiralReadout] using chiralMinus55_commutator_mem_grade_neg_two i j

theorem mixed_commutator_mem_grade_zero (i j : Fin 3) :
    chiralReadout (true, i) * chiralReadout (false, j) -
        chiralReadout (false, j) * chiralReadout (true, i) ∈
      cl55GradeSubmodule 0 := by
  simpa [chiralReadout] using chiralPlus55_minus55_commutator_mem_grade_zero i j

/- The Pin action is stated on the genuine Clifford vector readout.  The
   repository's native action transports vectors into `LinearMap.range ι55`;
   no unproved permutation formula for the six selected generators is added. -/
theorem pin_chiralReadout_mem_vector_range (g : Pin55) (s : ChiralIndex) :
    pinTwistedAdj g (chiralVectorReadout s) ∈ LinearMap.range (ι55) := by
  exact pinTwistedAdj_mem_ι_range g (chiralVectorReadout s)

theorem spin_chiralReadout_plus_grade (g : Spin55) (i : Fin 3) :
    spinCliffordRingEquiv g (chiralReadout (true, i)) ∈
      spinTransportedCl55GradeSubmodule g 1 := by
  simpa [chiralReadout] using chiralPlus55_spin_transport g i

theorem spin_chiralReadout_minus_grade (g : Spin55) (i : Fin 3) :
    spinCliffordRingEquiv g (chiralReadout (false, i)) ∈
      spinTransportedCl55GradeSubmodule g (-1) := by
  simpa [chiralReadout] using chiralMinus55_spin_transport g i

theorem spin_chiralReadout_grade (g : Spin55) (s : ChiralIndex) :
    spinCliffordRingEquiv g (chiralReadout s) ∈
      if s.1 then spinTransportedCl55GradeSubmodule g 1
      else spinTransportedCl55GradeSubmodule g (-1) := by
  cases s with
  | mk b i =>
      cases b
      · exact spin_chiralReadout_minus_grade g i
      · exact spin_chiralReadout_plus_grade g i

end

end InfoGeometry.Canonical.Cl55ChiralSolderingReadout

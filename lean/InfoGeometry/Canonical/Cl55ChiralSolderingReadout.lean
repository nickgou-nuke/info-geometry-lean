import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators
import InfoGeometry.Clifford.Cl55WittPinAction
import InfoGeometry.Canonical.SplitOctonionThreeColorSplitQuaternionCores

/-!
# Six-channel chiral soldering into `Cl(5,5)`

This file packages the already existing first-three CAR pairs as one
operator-valued six-channel readout.  It is deliberately a readout layer:
it does not assert a multiplicative embedding of the non-associative Zorn
algebra into the associative Clifford algebra.
-/

namespace InfoGeometry.Canonical.Cl55ChiralSolderingReadout

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical

noncomputable section

abbrev ChiralIndex := Bool × Fin 3

/-- The six chiral labels, with `true` denoting the plus sheet. -/
noncomputable def soldering (s : ChiralIndex) : Cl55 :=
  if s.1 then chiralPlus55 s.2 else chiralMinus55 s.2

/- The explicit identification of the three split-quaternionic colour planes
   `(i,l)`, `(j,l)`, `(k,l)` with the first three Witt pairs. -/
def colourToFin3 : SplitOctonionColour → Fin 3
  | .red => 0
  | .green => 1
  | .blue => 2

theorem colourToFin3_injective : Function.Injective colourToFin3 := by
  intro a b h
  cases a <;> cases b <;> simp [colourToFin3] at h ⊢

def solderingColour (s : Bool) (c : SplitOctonionColour) : Cl55 :=
  soldering (s, colourToFin3 c)

@[simp] theorem solderingColour_red (s : Bool) :
    solderingColour s .red = soldering (s, 0) := by
  rfl

@[simp] theorem solderingColour_green (s : Bool) :
    solderingColour s .green = soldering (s, 1) := by
  rfl

@[simp] theorem solderingColour_blue (s : Bool) :
    solderingColour s .blue = soldering (s, 2) := by
  rfl

@[simp] theorem soldering_plus (i : Fin 3) :
    soldering (true, i) = chiralPlus55 i := by
  simp [soldering]

@[simp] theorem soldering_minus (i : Fin 3) :
    soldering (false, i) = chiralMinus55 i := by
  simp [soldering]

@[simp] theorem soldering_sq (s : ChiralIndex) :
    soldering s * soldering s = 0 := by
  cases s with
  | mk b i =>
      cases b <;> simp [soldering]

theorem plus_anticommutator (i j : Fin 3) :
    soldering (true, i) * soldering (true, j) +
        soldering (true, j) * soldering (true, i) = 0 := by
  simpa [soldering] using chiralPlus55_anticommutator i j

theorem minus_anticommutator (i j : Fin 3) :
    soldering (false, i) * soldering (false, j) +
        soldering (false, j) * soldering (false, i) = 0 := by
  simpa [soldering] using chiralMinus55_anticommutator i j

theorem mixed_anticommutator (i j : Fin 3) :
    soldering (false, i) * soldering (true, j) +
        soldering (true, j) * soldering (false, i) =
      if i = j then 1 else 0 := by
  simpa [soldering] using chiralMinus55_plus55_anticommutator i j

theorem plus_commutator_mem_grade_two (i j : Fin 3) :
    soldering (true, i) * soldering (true, j) -
        soldering (true, j) * soldering (true, i) ∈
      cl55GradeSubmodule 2 := by
  simpa [soldering] using chiralPlus55_commutator_mem_grade_two i j

theorem minus_commutator_mem_grade_neg_two (i j : Fin 3) :
    soldering (false, i) * soldering (false, j) -
        soldering (false, j) * soldering (false, i) ∈
      cl55GradeSubmodule (-2) := by
  simpa [soldering] using chiralMinus55_commutator_mem_grade_neg_two i j

theorem mixed_commutator_mem_grade_zero (i j : Fin 3) :
    soldering (true, i) * soldering (false, j) -
        soldering (false, j) * soldering (true, i) ∈
      cl55GradeSubmodule 0 := by
  simpa [soldering] using chiralPlus55_minus55_commutator_mem_grade_zero i j

/- The Pin action is stated on the genuine Clifford vector readout.  The
   repository's native action transports vectors into `LinearMap.range ι55`;
   no unproved permutation formula for the six selected generators is added. -/
theorem pin_soldering_vector_readout (g : Pin55) (v : V55) :
    pinTwistedAdj g v ∈ LinearMap.range (ι55) := by
  exact pinTwistedAdj_mem_ι_range g v

theorem spin_soldering_plus_grade (g : Spin55) (i : Fin 3) :
    spinCliffordRingEquiv g (soldering (true, i)) ∈
      spinTransportedCl55GradeSubmodule g 1 := by
  simpa [soldering] using chiralPlus55_spin_transport g i

theorem spin_soldering_minus_grade (g : Spin55) (i : Fin 3) :
    spinCliffordRingEquiv g (soldering (false, i)) ∈
      spinTransportedCl55GradeSubmodule g (-1) := by
  simpa [soldering] using chiralMinus55_spin_transport g i

end

end InfoGeometry.Canonical.Cl55ChiralSolderingReadout

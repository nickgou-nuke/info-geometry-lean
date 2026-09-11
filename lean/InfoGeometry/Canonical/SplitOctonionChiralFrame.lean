import InfoGeometry.Canonical.SplitOctonionSixSectorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open SplitOctonionColour

noncomputable section

/-- The complete ordered chiral frame: one pole, the positive triplet,
the other pole, and the negative triplet. -/
def chiralFrame : Fin 8 → StandardRationalSplitOctonion
  | 0 => modularNPlus
  | 1 => modularSigmaPlus .red
  | 2 => modularSigmaPlus .green
  | 3 => modularSigmaPlus .blue
  | 4 => modularNMinus
  | 5 => modularSigmaMinus .red
  | 6 => modularSigmaMinus .green
  | 7 => modularSigmaMinus .blue

/-- The eight coordinates dual to the ordered chiral frame. -/
def chiralFrameCoordinate (z : StandardRationalSplitOctonion) : Fin 8 → ℚ
  | 0 => z .one + z .l
  | 1 => -z .i + z .il
  | 2 => -z .j + z .jl
  | 3 => -z .k + z .kl
  | 4 => z .one - z .l
  | 5 => z .i + z .il
  | 6 => z .j + z .jl
  | 7 => z .k + z .kl

def chiralFrameCoordinateLinear (i : Fin 8) :
    StandardRationalSplitOctonion →ₗ[ℚ] ℚ where
  toFun z := chiralFrameCoordinate z i
  map_add' x y := by
    fin_cases i <;> simp [chiralFrameCoordinate] <;> ring
  map_smul' a x := by
    fin_cases i <;> simp [chiralFrameCoordinate] <;> ring

@[simp] theorem chiralFrameCoordinateLinear_apply
    (i : Fin 8) (z : StandardRationalSplitOctonion) :
    chiralFrameCoordinateLinear i z = chiralFrameCoordinate z i :=
  rfl

@[simp] theorem chiralFrameCoordinate_frame (i j : Fin 8) :
    chiralFrameCoordinate (chiralFrame i) j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> native_decide

@[simp] theorem chiralFrameCoordinateLinear_frame (i j : Fin 8) :
    chiralFrameCoordinateLinear i (chiralFrame j) = if i = j then 1 else 0 := by
  simpa [chiralFrameCoordinateLinear_apply, eq_comm] using
    (chiralFrameCoordinate_frame j i)

theorem chiralFrame_injective : Function.Injective chiralFrame := by
  intro i j h
  have hc : chiralFrameCoordinate (chiralFrame i) =
      chiralFrameCoordinate (chiralFrame j) := congrArg chiralFrameCoordinate h
  by_contra hij
  have he := congrFun hc i
  rw [chiralFrameCoordinate_frame, chiralFrameCoordinate_frame] at he
  have hji : j = i := by simpa [hij] using he
  exact hij hji.symm

theorem chiralFrame_reconstruct (z : StandardRationalSplitOctonion) :
    (∑ i : Fin 8, chiralFrameCoordinate z i • chiralFrame i) = z := by
  funext b
  cases b <;>
    simp [chiralFrameCoordinate, chiralFrame, Fin.sum_univ_succ,
      modularNPlus, modularNMinus, modularSigmaPlus, modularSigmaMinus,
      modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit,
      fundamentalSymmetry, rationalBasis] <;>
    ring

theorem chiralFrame_linearIndependent :
    LinearIndependent ℚ chiralFrame := by
  rw [Fintype.linearIndependent_iff]
  intro g h i
  have hc := congrArg
    (fun z : StandardRationalSplitOctonion => chiralFrameCoordinate z i) h
  fin_cases i <;>
    simp [chiralFrameCoordinate, chiralFrame, Fin.sum_univ_succ,
      modularNPlus, modularNMinus, modularSigmaPlus, modularSigmaMinus,
      modularJ_eq_colourLUnit, phaseAxis, colourUnit, colourLUnit,
      fundamentalSymmetry, rationalBasis] at hc ⊢ <;>
    linarith

noncomputable def chiralFrameBasis :
    Module.Basis (Fin 8) ℚ StandardRationalSplitOctonion :=
  Module.Basis.mk chiralFrame_linearIndependent (by
    intro z hz
    rw [← chiralFrame_reconstruct z]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp] theorem chiralFrameBasis_apply (i : Fin 8) :
    chiralFrameBasis i = chiralFrame i := by
  exact Module.Basis.mk_apply _ _ _

@[simp] theorem chiralFrame_pole_plus :
    chiralFrame 0 = modularNPlus := rfl

@[simp] theorem chiralFrame_pole_minus :
    chiralFrame 4 = modularNMinus := rfl

@[simp] theorem chiralFrame_positive (c : SplitOctonionColour) :
    chiralFrame (match c with
      | .red => 1
      | .green => 2
      | .blue => 3) = modularSigmaPlus c := by
  cases c <;> rfl

@[simp] theorem chiralFrame_negative (c : SplitOctonionColour) :
    chiralFrame (match c with
      | .red => 5
      | .green => 6
      | .blue => 7) = modularSigmaMinus c := by
  cases c <;> rfl

theorem chiralFrame_two_poles_plus_six_channels :
    Set.range chiralFrame =
      {modularNPlus, modularNMinus} ∪
        Set.range (fun p : Fin 2 × SplitOctonionColour =>
          sixSectorBasis p.1 p.2) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · simp
    · exact Or.inr ⟨(0, .red), rfl⟩
    · exact Or.inr ⟨(0, .green), rfl⟩
    · exact Or.inr ⟨(0, .blue), rfl⟩
    · simp
    · exact Or.inr ⟨(1, .red), rfl⟩
    · exact Or.inr ⟨(1, .green), rfl⟩
    · exact Or.inr ⟨(1, .blue), rfl⟩
  · intro hz
    rcases hz with hz | hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨4, rfl⟩
    · rcases hz with ⟨⟨s, c⟩, rfl⟩
      fin_cases s
      · cases c <;> first | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
      · cases c <;> first | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩

/-- The explicit positions of the six off-diagonal channels in the full frame. -/
def chiralOffDiagonalIndex : Fin 2 × SplitOctonionColour → Fin 8
  | (0, .red) => 1
  | (0, .green) => 2
  | (0, .blue) => 3
  | (1, .red) => 5
  | (1, .green) => 6
  | (1, .blue) => 7

@[simp] theorem chiralFrame_chiralOffDiagonalIndex
    (p : Fin 2 × SplitOctonionColour) :
    chiralFrame (chiralOffDiagonalIndex p) = sixSectorBasis p.1 p.2 := by
  rcases p with ⟨s, c⟩
  fin_cases s <;> cases c <;> rfl

theorem chiralOffDiagonalIndex_injective :
    Function.Injective chiralOffDiagonalIndex := by
  intro p q h
  rcases p with ⟨s, c⟩
  rcases q with ⟨t, d⟩
  fin_cases s <;> fin_cases t <;> cases c <;> cases d <;>
    simp_all [chiralOffDiagonalIndex]

/- The same six channels with the native `Fin 3` colour index used by the
   six-state spectral owners. -/
def chiralOffDiagonalIndexFin3 : Fin 2 × Fin 3 → Fin 8
  | (0, 0) => 1
  | (0, 1) => 2
  | (0, 2) => 3
  | (1, 0) => 5
  | (1, 1) => 6
  | (1, 2) => 7

@[simp] theorem chiralFrame_chiralOffDiagonalIndexFin3
    (p : Fin 2 × Fin 3) :
    chiralFrame (chiralOffDiagonalIndexFin3 p) =
      sixSectorBasisFin3 p.1 p.2 := by
  rcases p with ⟨s, c⟩
  fin_cases s <;> fin_cases c <;> rfl

theorem chiralOffDiagonalIndexFin3_injective :
    Function.Injective chiralOffDiagonalIndexFin3 := by
  intro p q h
  rcases p with ⟨s, c⟩
  rcases q with ⟨t, d⟩
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;>
    simp_all [chiralOffDiagonalIndexFin3]

end
end InfoGeometry.Canonical

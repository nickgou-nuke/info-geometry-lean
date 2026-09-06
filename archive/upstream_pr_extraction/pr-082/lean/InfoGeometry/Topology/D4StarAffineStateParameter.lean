import InfoGeometry.Topology.D4StarAffineStateConvexity

namespace InfoGeometry.Topology.PauliJungD4Star

abbrev BooleanStateParameter := Set.Icc (0 : ℚ) 1

def stateToParameter (s : BooleanAffineState) : BooleanStateParameter :=
  ⟨s.centreWeight, s.centre_nonneg, by linarith [s.outer_nonneg, s.normalized]⟩

def parameterToState (p : BooleanStateParameter) : BooleanAffineState :=
  ⟨(p.1, 1 - p.1), by
    constructor
    · exact p.2.1
    · constructor
      · linarith [p.2.2]
      · ring⟩

theorem parameterToState_stateToParameter
    (s : BooleanAffineState) :
    parameterToState (stateToParameter s) = s := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change 1 - s.1.1 = s.1.2
    linarith [s.2.2]

theorem stateToParameter_parameterToState
    (p : BooleanStateParameter) :
    stateToParameter (parameterToState p) = p := by
  apply Subtype.ext
  rfl

noncomputable def booleanAffineStateEquivInterval :
    BooleanAffineState ≃ BooleanStateParameter :=
  { toFun := stateToParameter
    invFun := parameterToState
    left_inv := parameterToState_stateToParameter
    right_inv := stateToParameter_parameterToState }

theorem uniformState_parameter :
    stateToParameter uniformBooleanAffineState = ⟨1 / 2, by norm_num, by norm_num⟩ := by
  apply Subtype.ext
  rfl

end InfoGeometry.Topology.PauliJungD4Star

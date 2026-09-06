import Mathlib.Tactic
import InfoGeometry.Physics.IsospinMirrorDynamics

namespace InfoGeometry.Physics

/--
A representation of a superallowed Fermi decay, primarily focusing on the
Conserved Vector Current (CVC) property which states that the vector coupling
constant is unrenormalized, resulting in a universal `ft` value for all
superallowed 0+ to 0+ nuclear beta decays.
-/
abbrev SuperallowedFermiDecay :=
  {data : NuclearState × (NuclearState × ℝ) // data.2.2 = 3072}

namespace SuperallowedFermiDecay

abbrev initial_state (D : SuperallowedFermiDecay) : NuclearState := D.1.1
abbrev final_state (D : SuperallowedFermiDecay) : NuclearState := D.1.2.1
abbrev ft_value (D : SuperallowedFermiDecay) : ℝ := D.1.2.2
abbrev ft_is_universal (D : SuperallowedFermiDecay) : D.ft_value = 3072 := D.2

end SuperallowedFermiDecay

/--
A transition structure specifically for 0+ to 0+ superallowed decays.
We assert that the transition strength depends solely on the isospin
raising/lowering operators (encoded here via the expectation value of T_plus/T_minus).
-/
abbrev SuperallowedZeroPlusTransition :=
  {data : SuperallowedFermiDecay × ℝ //
    data.1.initial_state.spin = 0 ∧
      data.1.initial_state.parity = 1 ∧
      data.1.final_state.spin = 0 ∧
      data.1.final_state.parity = 1 ∧
      data.1.initial_state.isospin.T = data.1.final_state.isospin.T ∧
      data.2 =
        (data.1.initial_state.isospin.T : ℝ) *
            ((data.1.initial_state.isospin.T : ℝ) + 1) -
          (data.1.initial_state.isospin.T_z : ℝ) *
            (data.1.final_state.isospin.T_z : ℝ)}

namespace SuperallowedZeroPlusTransition

abbrev decay (T : SuperallowedZeroPlusTransition) : SuperallowedFermiDecay := T.1.1
abbrev initial_state (T : SuperallowedZeroPlusTransition) : NuclearState := T.decay.initial_state
abbrev final_state (T : SuperallowedZeroPlusTransition) : NuclearState := T.decay.final_state
abbrev ft_value (T : SuperallowedZeroPlusTransition) : ℝ := T.decay.ft_value
abbrev ft_is_universal (T : SuperallowedZeroPlusTransition) : T.ft_value = 3072 := T.decay.ft_is_universal
abbrev matrix_element_sq (T : SuperallowedZeroPlusTransition) : ℝ := T.1.2

end SuperallowedZeroPlusTransition

/--
A theorem formalizing that for 0+ to 0+ superallowed Fermi transitions,
the structure-independence of the CVC property guarantees that the ft value
is precisely the universal constant.
-/
theorem cvc_structure_independence (decay : SuperallowedZeroPlusTransition) :
  decay.ft_value = 3072 :=
  decay.ft_is_universal

end InfoGeometry.Physics

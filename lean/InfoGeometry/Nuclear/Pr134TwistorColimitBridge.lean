import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Nuclear.Praseodymium134
import InfoGeometry.Nuclear.TwistorMassGapSupergeometry
import InfoGeometry.Topology.AmplituhedronTensorTowerColimit
import InfoGeometry.Quantum.PauliSoldering

noncomputable section

namespace InfoGeometry.Nuclear.Pr134TwistorColimitBridge

open InfoGeometry.Nuclear.Praseodymium134
open InfoGeometry.Nuclear.TwistorMassGapSupergeometry
open InfoGeometry.Topology.AmplituhedronColimit
open InfoGeometry.Quantum.PauliSoldering
open Complex

/-- QMS Mandatory: Map the Twistor Incidence topological condition back down to the nuclear state.
    Instead of toy duplication, we natively call the exact Soldering form from the Quantum algebra. -/
def incidence_state (Z : Twistor4) (v : Vec3) : Prop :=
  is_incident Z (solder (0, v 0, v 1, v 2))

/-- Bridge the Pr134 state into the finite Amplituhedron algebraic stage n=3. -/
def pr134_amplituhedron_kinematics (S : EmergentSpacetime) : AmplituhedronAlgebra 3 :=
  !![S.j_p 0, S.j_p 1, S.j_p 2;
     S.j_n 0, S.j_n 1, S.j_n 2;
     S.omega 0, S.omega 1, S.omega 2;
     0, 0, 0]

/-- Project the finite Amplituhedron state iteratively into the Colimit Continuum tower. -/
def pr134_colimit_injection (S : EmergentSpacetime) (n : ℕ) : AmplituhedronAlgebra n :=
  Matrix.of (fun i j => if hj : j.val < 3 then pr134_amplituhedron_kinematics S i ⟨j.val, hj⟩ else 0)

end InfoGeometry.Nuclear.Pr134TwistorColimitBridge

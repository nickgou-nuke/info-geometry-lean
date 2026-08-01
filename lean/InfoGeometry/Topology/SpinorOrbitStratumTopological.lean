import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Rat
import InfoGeometry.Topology.SpinorOrbitStratum

namespace InfoGeometry.Topology.SpinorOrbitStratumTopological

open InfoGeometry.Physics.Pin55Formal
open InfoGeometry.Topology.SpinorOrbitStratum

abbrev Vec55 := Fin 10 → ℚ

/-!
  Topological readouts for the concrete rational `(5,5)` quadratic form.

  These statements concern the product topology on the finite coordinate
  carrier.  They do not assert a topology on a Pin/Spin group or an orbit
  quotient.
-/

theorem continuous_q55 : Continuous (q55 : Vec55 → ℚ) := by
  change Continuous (fun x : Fin 10 → ℚ => q55 x)
  fun_prop

def q55NullLocus : Set Vec55 :=
  {x | q55 x = 0}

def q55GenericLocus : Set Vec55 :=
  {x | q55 x ≠ 0}

def q55PositiveLocus : Set Vec55 :=
  {x | 0 < q55 x}

def q55NegativeLocus : Set Vec55 :=
  {x | q55 x < 0}

theorem q55NullLocus_isClosed : IsClosed q55NullLocus := by
  change IsClosed ((q55 : Vec55 → ℚ) ⁻¹' ({0} : Set ℚ))
  exact (isClosed_singleton : IsClosed ({0} : Set ℚ)).preimage continuous_q55

theorem q55GenericLocus_isOpen : IsOpen q55GenericLocus := by
  change IsOpen (((q55 : Vec55 → ℚ) ⁻¹' ({0} : Set ℚ))ᶜ)
  exact (q55NullLocus_isClosed).isOpen_compl

theorem q55PositiveLocus_isOpen : IsOpen q55PositiveLocus := by
  change IsOpen ((q55 : Vec55 → ℚ) ⁻¹' Set.Ioi 0)
  exact isOpen_Ioi.preimage continuous_q55

theorem q55NegativeLocus_isOpen : IsOpen q55NegativeLocus := by
  change IsOpen ((q55 : Vec55 → ℚ) ⁻¹' Set.Iio 0)
  exact isOpen_Iio.preimage continuous_q55

end InfoGeometry.Topology.SpinorOrbitStratumTopological

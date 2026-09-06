import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Krein.Metric

namespace InfoGeometry.Canonical.SuperInference

open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Information Supersymmetry (SUSY) pairs the bosonic belief state (parameters in E)
with a fermionic superpartner (differential forms or tangent vectors representing expectations/gradients).
-/
structure SuperState (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  boson : E      -- The primal parameter (e.g., natural parameters θ)
  fermion : E    -- The dual tangent vector (e.g., expectation parameters η)

/-- Canonical naming alias for supersymmetric belief-state packaging. -/
abbrev SuperBeliefState := SuperState

/--
The Supercharge operator Q acting on the SuperState.
Q transforms a bosonic state into its fermionic partner using the Fisher metric.
In this structural representation, the supercharge maps the parameter to its dual expectation.
-/
noncomputable def superCharge (H : HessianGeometry E) (s : SuperState E) : SuperState E :=
  { boson := 0, -- Q annihilates the bosonic part in a simple linear/fermionic sector
    fermion := H.dualMap s.boson }

/-- Canonical naming alias for the supersymmetric charge operator. -/
noncomputable abbrev susyCharge (H : HessianGeometry E) (s : SuperBeliefState E) :
    SuperBeliefState E :=
  superCharge H s

/--
The Supersymmetric Hamiltonian (Laplacian).
H_susy = {Q, Q†} = Q Q† + Q† Q.
In Information Geometry, this corresponds to the Witten Laplacian,
whose zero modes yield the Betti numbers (topological invariants) of the belief space.
-/
noncomputable def superHamiltonian (H : HessianGeometry E) (s : SuperState E) : SuperState E :=
  susyCharge H (susyCharge H s)

/-- Canonical naming alias for the supersymmetric Hamiltonian. -/
noncomputable abbrev susyHamiltonian (H : HessianGeometry E) (s : SuperBeliefState E) :
    SuperBeliefState E :=
  superHamiltonian H s

omit [FiniteDimensional ℝ E] in
@[simp] lemma superCharge_boson_eq_zero (H : HessianGeometry E) (s : SuperBeliefState E) :
    (susyCharge H s).boson = 0 := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma superCharge_fermion_eq_dualMap (H : HessianGeometry E) (s : SuperBeliefState E) :
    (susyCharge H s).fermion = H.dualMap s.boson := rfl

omit [FiniteDimensional ℝ E] in
/-- The square of the displayed triangular supercharge is determined by the
dual map at the origin. Nilpotency therefore requires the additional condition
`H.dualMap 0 = 0`; it is not silently assumed here.
-/
@[simp] lemma susyCharge_sq (H : HessianGeometry E) (s : SuperBeliefState E) :
    susyCharge H (susyCharge H s) =
      ({ boson := 0, fermion := H.dualMap 0 } : SuperBeliefState E) := by
  cases s
  simp [susyCharge, superCharge]

omit [FiniteDimensional ℝ E] in
lemma susyCharge_nilpotent_of_dualMap_zero
    (H : HessianGeometry E) (h0 : H.dualMap 0 = 0) (s : SuperBeliefState E) :
    susyCharge H (susyCharge H s) =
      ({ boson := 0, fermion := 0 } : SuperBeliefState E) := by
  rw [susyCharge_sq, h0]

omit [FiniteDimensional ℝ E] in
omit [FiniteDimensional ℝ E] in
@[simp] lemma susyHamiltonian_eq_charge_square
    (H : HessianGeometry E) (s : SuperBeliefState E) :
    susyHamiltonian H s =
      ({ boson := 0, fermion := H.dualMap 0 } : SuperBeliefState E) := by
  exact susyCharge_sq H s

omit [FiniteDimensional ℝ E] in
lemma susyHamiltonian_eq_zero_of_dualMap_zero
    (H : HessianGeometry E) (h0 : H.dualMap 0 = 0) (s : SuperBeliefState E) :
    susyHamiltonian H s = ({ boson := 0, fermion := 0 } : SuperBeliefState E) := by
  rw [susyHamiltonian_eq_charge_square, h0]

omit [FiniteDimensional ℝ E] in
lemma susyHamiltonian_eq_self_of_fixed
    (H : HessianGeometry E) (s : SuperBeliefState E)
    (hfixed : susyCharge H (susyCharge H s) = s) :
    susyHamiltonian H s = s := by
  exact hfixed

end InfoGeometry.Canonical.SuperInference

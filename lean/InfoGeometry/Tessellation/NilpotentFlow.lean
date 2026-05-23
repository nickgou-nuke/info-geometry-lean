import InfoGeometry.Tessellation.Corner
import Mathlib.Tactic

/-!
# Square-zero lightray flows

A square-zero lightray generates a concrete unipotent transport `1 + N` with
inverse `1 - N`.  This is the nilpotent-flow side of the tessellation picture;
it is separate from the diagonal determinant/exponential H¹ theorem.
-/

namespace InfoGeometry.Tessellation

/-- A square-zero element generates the unit `1 + N` with inverse `1 - N`. -/
def oneAddSquareZeroUnit {A : Type*} [Ring A] (N : A) (hN : N * N = 0) : Aˣ where
  val := 1 + N
  inv := 1 - N
  val_inv := by
    noncomm_ring [hN]
  inv_val := by
    noncomm_ring [hN]

@[simp]
theorem oneAddSquareZeroUnit_val
    {A : Type*} [Ring A] (N : A) (hN : N * N = 0) :
    (oneAddSquareZeroUnit N hN : A) = 1 + N :=
  rfl

/-- The inverse of the square-zero unipotent is `1 - N`. -/
theorem oneAddSquareZeroUnit_inv_val
    {A : Type*} [Ring A] (N : A) (hN : N * N = 0) :
    (((oneAddSquareZeroUnit N hN)⁻¹ : Aˣ) : A) = 1 - N :=
  rfl

/--
An incident lightray between orthogonal sectors generates a unipotent
transport unit.
-/
def IncidentLightray.flowUnit
    {A : Type*} [Ring A] {src tgt : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0) : Aˣ :=
  oneAddSquareZeroUnit L.N (L.square_zero_of_orthogonal h_orthogonal)

@[simp]
theorem IncidentLightray.flowUnit_val
    {A : Type*} [Ring A] {src tgt : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0) :
    (L.flowUnit h_orthogonal : A) = 1 + L.N :=
  rfl

/-- Incident lightray flow transports causal diamonds by unit conjugation. -/
def IncidentLightray.transportDiamond
    {A : Type*} [Ring A] {src tgt : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0)
    (D : Diamond A) : Diamond A :=
  unitConjDiamond (L.flowUnit h_orthogonal) D

/-- Incident lightray flow transports corner membership. -/
theorem IncidentLightray.transport_mem_corner
    {A : Type*} [Ring A] {src tgt D : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0)
    {x : A} (hx : IsInCorner D x) :
    IsInCorner (L.transportDiamond h_orthogonal D)
      (unitConjRing (L.flowUnit h_orthogonal) x) := by
  exact unitConjRing_mem_corner (L.flowUnit h_orthogonal) hx

end InfoGeometry.Tessellation

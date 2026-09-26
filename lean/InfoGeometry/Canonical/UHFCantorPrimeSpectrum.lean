import Mathlib.RingTheory.Spectrum.Prime.Topology
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

/-!
# The Cantor boundary in the native prime spectrum of its cylinder algebra

The owner modules already construct the complex cylinder-function algebra on
the binary boundary and prove that its inclusion into continuous functions is
dense.  This file connects that existing algebra to Mathlib's `PrimeSpectrum`
by evaluation at boundary points.

The result is a continuous injection into the prime spectrum.  It does not
claim surjectivity, a homeomorphism, or an identification of the full affine
scheme spectrum with the Cantor boundary.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFCantorPrimeSpectrum

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

/-- The already constructed subalgebra of complex-valued finite-cylinder
functions on the binary Cantor boundary. -/
abbrev BoundaryCylinderAlgebra := cylinderColimitSubalgebra

/-- Evaluation at a boundary point, restricted to the existing cylinder
algebra. -/
def evaluation (x : CantorBoundary) : BoundaryCylinderAlgebra →+* ℂ where
  toFun f := f.1 x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The prime of the cylinder algebra obtained by pulling back the unique
prime of `ℂ` along evaluation. -/
def point (x : CantorBoundary) : PrimeSpectrum BoundaryCylinderAlgebra :=
  PrimeSpectrum.comap (evaluation x) (⊥ : PrimeSpectrum ℂ)

@[simp] theorem mem_point_ideal_iff (x : CantorBoundary)
    (f : BoundaryCylinderAlgebra) :
    f ∈ (point x).asIdeal ↔ f.1 x = 0 := by
  simp [point, evaluation]

/-- Every prime-spectrum point in this map records evaluation at the original
boundary point. -/
theorem point_injective : Function.Injective point := by
  intro x y hxy
  by_contra hne
  obtain ⟨n, w, hx, hy⟩ := cylinderSet_separates hne
  let f : DiagAlg n := fun v => if v = w then 1 else 0
  let g : BoundaryCylinderAlgebra :=
    ⟨cylinder n f, cylinder_mem_colimit n f⟩
  have hx' : boundaryPrefix n x = w := by
    change boundaryPrefix n x = w at hx
    exact hx
  have hy' : boundaryPrefix n y ≠ w := by
    change boundaryPrefix n y = w at hy
    exact hy
  have hgx : g.1 x ≠ 0 := by
    change f (boundaryPrefix n x) ≠ 0
    simp [f, hx']
  have hgy : g.1 y = 0 := by
    change f (boundaryPrefix n y) = 0
    simp [f, hy']
  have hmemY : g ∈ (point y).asIdeal :=
    (mem_point_ideal_iff y g).2 hgy
  have hI : (point x).asIdeal = (point y).asIdeal :=
    congrArg PrimeSpectrum.asIdeal hxy
  have hmemX : g ∈ (point x).asIdeal := by
    rw [hI]
    exact hmemY
  exact hgx ((mem_point_ideal_iff x g).1 hmemX)

/-- The evaluation-to-spectrum map is continuous for the Zariski topology.
The proof uses the existing continuity theorem for every cylinder observable
and the native zero-locus description of closed subsets of a prime spectrum. -/
theorem continuous_point : Continuous point := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  rcases (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ with ⟨s, hs⟩
  rw [hs]
  have hpre : point ⁻¹' PrimeSpectrum.zeroLocus s =
      ⋂ f : s, {x : CantorBoundary | f.1.1 x = 0} := by
    ext x
    simp [PrimeSpectrum.mem_zeroLocus, mem_point_ideal_iff]
  rw [hpre]
  apply isClosed_iInter
  intro f
  exact isClosed_singleton.preimage
    (cylinder_colimit_mem_continuous f.1.2)

/-- The existing Cantor boundary maps continuously and injectively into the
native prime spectrum of its finite-cylinder algebra. -/
theorem continuous_injective_point : Continuous point ∧ Function.Injective point :=
  ⟨continuous_point, point_injective⟩

end InfoGeometry.Canonical.UHFCantorPrimeSpectrum

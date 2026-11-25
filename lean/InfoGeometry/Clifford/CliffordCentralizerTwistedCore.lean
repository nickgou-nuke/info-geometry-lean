/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.Clifford.Cl55WittVectorCommutant

/-!
# Clifford centralizer / twisted-centralizer core

This owner extracts only the set-level part of Filimoshina--Shirokov's
centralizer theory that is already meaningful on Mathlib's coordinate-free
`CliffordAlgebra Q`.  It reuses the ordinary commutant owner and the existing
involute/even-odd characterization; the explicit grade-wise classifications of
the paper remain open debt.

No reversion, grade-grading, basis expansion, or degenerate-radical argument is
asserted here.
-/

noncomputable section

namespace InfoGeometry.Clifford.CliffordCentralizerTwistedCore

open InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-- Paper-faithful twisted centralizer: the grade involution is applied to the
tested element, matching `X̃ V = V X` in the paper. -/
def gradedTwistedCentralizer (S : Set (CliffordAlgebra Q)) : Set (CliffordAlgebra Q) :=
  {x | ∀ v ∈ S, CliffordAlgebra.involute x * v = v * x}

theorem gradedTwistedCentralizer_zero_mem (S : Set (CliffordAlgebra Q)) :
    (0 : CliffordAlgebra Q) ∈ gradedTwistedCentralizer S := by
  intro v hv
  simp

theorem gradedTwistedCentralizer_add_mem {S : Set (CliffordAlgebra Q)}
    {x y : CliffordAlgebra Q} (hx : x ∈ gradedTwistedCentralizer S)
    (hy : y ∈ gradedTwistedCentralizer S) :
    x + y ∈ gradedTwistedCentralizer S := by
  intro v hv
  rw [map_add, add_mul, mul_add, hx v hv, hy v hv]

theorem algebraMap_mem_ordinaryCommutant_clifford
    (S : Set (CliffordAlgebra Q)) (r : R) :
    algebraMap R (CliffordAlgebra Q) r ∈ ordinaryCommutant S := by
  intro v hv
  exact Algebra.commutes r v

/-- The ordinary centralizer of the grade-zero scalar line is the whole
carrier. -/
theorem ordinaryCommutant_range_algebraMap_eq_univ :
    ordinaryCommutant (Set.range (algebraMap R (CliffordAlgebra Q))) = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _ v hv
    rcases hv with ⟨r, rfl⟩
    exact (Algebra.commutes r x).symm

/-- The twisted centralizer of the grade-zero scalar line is exactly the even
subspace; this is the coordinate-free form of the paper's `Ž⁰ = Cl⁽⁰⁾`. -/
theorem gradedTwistedCentralizer_range_algebraMap_eq_even [Invertible (2 : R)]
    (x : CliffordAlgebra Q) :
    x ∈ gradedTwistedCentralizer (Set.range (algebraMap R (CliffordAlgebra Q))) ↔
      x ∈ CliffordAlgebra.evenOdd Q 0 := by
  constructor
  · intro hx
    apply (involute_eq_self_iff_mem_even Q x).mp
    simpa using (hx (algebraMap R (CliffordAlgebra Q) 1) ⟨1, rfl⟩)
  · intro hx
    have hfix : CliffordAlgebra.involute x = x :=
      (involute_eq_self_iff_mem_even Q x).mpr hx
    intro v hv
    rcases hv with ⟨r, rfl⟩
    rw [hfix]
    exact (Algebra.commutes r x).symm

/-- The existing Cl(5,5) Witt vector commutant is the grade-one specialization
of the paper-faithful twisted centralizer. -/
theorem cl55_vector_commutant_eq_gradedTwistedCentralizer :
    InfoGeometry.Clifford.Clifford55.wittTwistedVectorCommutant =
      gradedTwistedCentralizer (Set.range InfoGeometry.Clifford.Clifford55.ι55) := by
  ext a
  constructor
  · intro ha v hv
    rcases hv with ⟨v, rfl⟩
    exact ha v
  · intro ha v
    exact ha (InfoGeometry.Clifford.Clifford55.ι55 v) ⟨v, rfl⟩

end InfoGeometry.Clifford.CliffordCentralizerTwistedCore

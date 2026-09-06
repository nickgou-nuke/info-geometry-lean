import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Rat
import InfoGeometry.Topology.SpinorOrbitStratum
import InfoGeometry.Topology.Pin55ReflectionGlide

namespace InfoGeometry.Topology.SpinorOrbitStratumTopological

open InfoGeometry.Physics.Pin55Formal
open InfoGeometry.Topology.Pin55ReflectionGlide
open InfoGeometry.Topology.SpinorOrbitStratum

abbrev Vec55 := Fin 10 → ℚ

/-!
  Topological readouts for the concrete rational `(5,5)` quadratic form.

  These statements concern the product topology on the finite coordinate
  carrier and provide the locus structure used by the `(5,5)` topology lane.
-/

theorem continuous_q55 : Continuous (q55 : Vec55 → ℚ) := by
  have h : Continuous (fun x : Vec55 =>
      x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 + x 4 * x 4 -
        (x 5 * x 5 + x 6 * x 6 + x 7 * x 7 + x 8 * x 8 + x 9 * x 9)) := by
    fun_prop
  simpa [q55, QuadraticMap.proj_apply] using h

def q55NullLocus : Set Vec55 :=
  {x | q55 x = 0}

def q55GenericLocus : Set Vec55 :=
  {x | q55 x ≠ 0}

def q55PositiveLocus : Set Vec55 :=
  {x | 0 < q55 x}

def q55NegativeLocus : Set Vec55 :=
  {x | q55 x < 0}

def q55NonzeroNullLocus : Set Vec55 :=
  q55NullLocus \ ({0} : Set Vec55)

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

theorem q55NonzeroNullLocus_decomposition :
    q55NonzeroNullLocus = q55NullLocus ∩ ({0} : Set Vec55)ᶜ := by
  ext x
  simp [q55NonzeroNullLocus]

theorem continuous_reflect0 : Continuous (reflect0 : Vec55 → Vec55) := by
  unfold reflect0
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · subst i
    simpa using (continuous_neg.comp (continuous_apply 0))
  · simpa [hi] using (continuous_apply i)

def reflect0Homeomorph : Vec55 ≃ₜ Vec55 where
  toFun := reflect0
  invFun := reflect0
  left_inv := reflect0_involutive
  right_inv := reflect0_involutive
  continuous_toFun := continuous_reflect0
  continuous_invFun := continuous_reflect0

@[simp] theorem reflect0Homeomorph_apply (x : Vec55) :
    reflect0Homeomorph x = reflect0 x := rfl

@[simp] theorem reflect0Homeomorph_symm_apply (x : Vec55) :
    reflect0Homeomorph.symm x = reflect0 x := rfl

theorem q55_reflect0_preserves (x : Vec55) :
    q55 (reflect0 x) = q55 x := by
  simp [q55, reflect0]

theorem q55NonzeroNullLocus_reflect0_preimage :
    reflect0 ⁻¹' q55NonzeroNullLocus = q55NonzeroNullLocus := by
  have hreflect_zero : reflect0 (0 : Vec55) = 0 := by
    ext i
    by_cases hi : i = 0 <;> simp [reflect0, hi]
  have hzero : ∀ x : Vec55, reflect0 x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro hx
      calc
        x = reflect0 (reflect0 x) := (reflect0_involutive x).symm
        _ = reflect0 0 := congrArg reflect0 hx
        _ = 0 := hreflect_zero
    · intro hx
      subst x
      exact hreflect_zero
  ext x
  change (q55 (reflect0 x) = 0 ∧ reflect0 x ≠ 0) ↔
    (q55 x = 0 ∧ x ≠ 0)
  rw [q55_reflect0_preserves x]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hx
    exact h.2 ((hzero x).mpr hx)
  · intro h
    refine ⟨h.1, ?_⟩
    intro hx
    exact h.2 ((hzero x).mp hx)

theorem reflect0_preimage_q55NullLocus :
    reflect0 ⁻¹' q55NullLocus = q55NullLocus := by
  ext x
  simp [q55NullLocus, q55_reflect0_preserves]

theorem reflect0_preimage_q55GenericLocus :
    reflect0 ⁻¹' q55GenericLocus = q55GenericLocus := by
  ext x
  simp [q55GenericLocus, q55_reflect0_preserves]

theorem reflect0_preimage_q55PositiveLocus :
    reflect0 ⁻¹' q55PositiveLocus = q55PositiveLocus := by
  ext x
  simp [q55PositiveLocus, q55_reflect0_preserves]

theorem reflect0_preimage_q55NegativeLocus :
    reflect0 ⁻¹' q55NegativeLocus = q55NegativeLocus := by
  ext x
  simp [q55NegativeLocus, q55_reflect0_preserves]

theorem reflect0Homeomorph_preimage_q55NullLocus :
    reflect0Homeomorph ⁻¹' q55NullLocus = q55NullLocus := by
  simpa [reflect0Homeomorph_apply] using reflect0_preimage_q55NullLocus

theorem reflect0Homeomorph_preimage_q55NonzeroNullLocus :
    reflect0Homeomorph ⁻¹' q55NonzeroNullLocus = q55NonzeroNullLocus := by
  simpa [reflect0Homeomorph_apply] using q55NonzeroNullLocus_reflect0_preimage

end InfoGeometry.Topology.SpinorOrbitStratumTopological

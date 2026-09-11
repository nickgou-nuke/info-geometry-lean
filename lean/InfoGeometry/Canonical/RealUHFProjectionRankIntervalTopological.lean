import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFProjectionRankSystem

/-!
# Topological carrier for coherent normalized projection-rank readouts

This owner packages only the bounded interval-valued readout supplied by the
finite real projection-rank tower.  It is not a state space and it does not
assert a K-theory or completed-UHF identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFProjectionRankIntervalTopological

open InfoGeometry.Canonical

abbrev DyadicUnitInterval := Set.Icc (0 : ℚ) 1

abbrev IntervalReadout := ℕ → DyadicUnitInterval

abbrev CompatibleIntervalReadout :=
  {f : IntervalReadout // ∀ n : ℕ, f (n + 1) = f n}

noncomputable instance : TopologicalSpace CompatibleIntervalReadout :=
  TopologicalSpace.induced
    (fun f : CompatibleIntervalReadout => f.1)
      (inferInstance : TopologicalSpace IntervalReadout)

noncomputable def normalizedIntervalReadout
    (S : RealUHFProjectionRankSystem) : CompatibleIntervalReadout :=
  ⟨fun n => S.normalizedReadoutInterval n, by
    intro n
    exact S.normalizedReadoutInterval_succ n⟩

@[simp] theorem normalizedIntervalReadout_apply
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    (normalizedIntervalReadout S).1 n = S.normalizedReadoutInterval n := rfl

theorem normalizedIntervalReadout_compatible
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    (normalizedIntervalReadout S).1 (n + 1) =
      (normalizedIntervalReadout S).1 n := by
  exact (normalizedIntervalReadout S).2 n

theorem continuous_intervalReadout_coordinate (n : ℕ) :
    Continuous (fun f : CompatibleIntervalReadout => f.1 n) := by
  exact (continuous_apply n).comp continuous_subtype_val

noncomputable def compatibleIntervalReadoutHomeomorph :
    CompatibleIntervalReadout ≃ₜ DyadicUnitInterval where
  toEquiv :=
    { toFun := fun f => f.1 0
      invFun := fun q => ⟨fun _ => q, by intro n; rfl⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext n
        induction n with
        | zero => rfl
        | succ n ih => exact ih.trans (f.2 n).symm
      right_inv := by
        intro q
        rfl }
  continuous_toFun := continuous_intervalReadout_coordinate 0
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro n
    simpa using
      (continuous_id : Continuous (fun q : DyadicUnitInterval => q))

def coordinateTopCatHom (n : ℕ) :
    TopCat.of CompatibleIntervalReadout ⟶ TopCat.of DyadicUnitInterval :=
  TopCat.ofHom
    { toFun := fun f => f.1 n
      continuous_toFun := continuous_intervalReadout_coordinate n }

@[simp] theorem coordinateTopCatHom_apply
    (n : ℕ) (f : CompatibleIntervalReadout) :
    coordinateTopCatHom n f = f.1 n := rfl

theorem normalizedIntervalReadout_coordinate
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    coordinateTopCatHom n (normalizedIntervalReadout S) =
      S.normalizedReadoutInterval n := rfl


end InfoGeometry.Canonical.RealUHFProjectionRankIntervalTopological

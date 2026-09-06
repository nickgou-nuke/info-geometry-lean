import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationTopology

/-!
# Split-Pin transport on the `Q55` null-configuration fundamental groupoid

Every native real split-Pin element already acts homeomorphically on the
unordered configuration space of distinct projective `Q55`-null points.  This
owner applies Mathlib's fundamental-groupoid functor to that concrete
homeomorphism and records the resulting equivalence between fundamental groups
at a point and at its image.

The basepoint is deliberately allowed to move.  These maps are induced by
global configuration-space symmetries; they are not exchange loops, braid
monodromy, or anyon data.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55RealSplitPinNullFundamentalGroup

open CategoryTheory
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfiguration
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- The fundamental-groupoid autoequivalence induced by one native real
split-Pin symmetry of unordered marked `Q55`-null configurations. -/
def realSplitPinNullFundamentalGroupoidEquivalence
    (g : realSplitPin55) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    FundamentalGroupoid (Unordered Q55 n) ≌
      FundamentalGroupoid (Unordered Q55 n) := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  let h : @Homeomorph (Unordered Q55 n) (Unordered Q55 n)
      (unorderedConfigurationTopology Q55 n)
      (unorderedConfigurationTopology Q55 n) :=
    realSplitPinUnorderedNullHomeomorph g n
  let he : @ContinuousMap.HomotopyEquiv (Unordered Q55 n) (Unordered Q55 n)
      (unorderedConfigurationTopology Q55 n)
      (unorderedConfigurationTopology Q55 n) :=
    h.toHomotopyEquiv
  exact @FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (Unordered Q55 n) (Unordered Q55 n)
    (unorderedConfigurationTopology Q55 n)
    (unorderedConfigurationTopology Q55 n) he

/-- The identity split-Pin element induces the identity functor on the
fundamental groupoid. -/
@[simp] theorem realSplitPinNullFundamentalGroupoidEquivalence_functor_one
    (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    (realSplitPinNullFundamentalGroupoidEquivalence 1 n).functor =
      𝟭 (FundamentalGroupoid (Unordered Q55 n)) := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  unfold realSplitPinNullFundamentalGroupoidEquivalence
  rw [realSplitPinUnorderedNullHomeomorph_one]
  exact FundamentalGroupoid.map_id

/-- The inverse functor is induced by the inverse of the same concrete
configuration homeomorphism. -/
theorem realSplitPinNullFundamentalGroupoidEquivalence_inverse
    (g : realSplitPin55) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    (realSplitPinNullFundamentalGroupoidEquivalence g n).inverse =
      FundamentalGroupoid.map
        ((realSplitPinUnorderedNullHomeomorph g n).symm :
          @ContinuousMap (Unordered Q55 n) (Unordered Q55 n)
            (unorderedConfigurationTopology Q55 n)
            (unorderedConfigurationTopology Q55 n)) := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  rfl

/-- Multiplication in the native split-Pin group transports to composition of
the induced fundamental-groupoid functors. -/
theorem realSplitPinNullFundamentalGroupoidEquivalence_functor_mul
    (g h : realSplitPin55) (n : ℕ) :
    let _ := unorderedConfigurationTopology Q55 n
    (realSplitPinNullFundamentalGroupoidEquivalence (g * h) n).functor =
      (realSplitPinNullFundamentalGroupoidEquivalence h n).functor.comp
        (realSplitPinNullFundamentalGroupoidEquivalence g n).functor := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  unfold realSplitPinNullFundamentalGroupoidEquivalence
  rw [realSplitPinUnorderedNullHomeomorph_mul]
  exact @FundamentalGroupoid.map_comp
    (Unordered Q55 n) (Unordered Q55 n)
    (unorderedConfigurationTopology Q55 n)
    (unorderedConfigurationTopology Q55 n)
    (Unordered Q55 n)
    (unorderedConfigurationTopology Q55 n)
    (realSplitPinUnorderedNullHomeomorph g n)
    (realSplitPinUnorderedNullHomeomorph h n)

/-- A split-Pin configuration homeomorphism induces a multiplicative
equivalence between the fundamental groups at a point and at its image. -/
def realSplitPinNullFundamentalGroupEquiv
    (g : realSplitPin55) (n : ℕ) (p : Unordered Q55 n) :
    @FundamentalGroup (Unordered Q55 n)
        (unorderedConfigurationTopology Q55 n) p ≃*
      @FundamentalGroup (Unordered Q55 n)
        (unorderedConfigurationTopology Q55 n)
        (realSplitPinUnorderedNullAction n g p) := by
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  let e := realSplitPinNullFundamentalGroupoidEquivalence g n
  change End (FundamentalGroupoid.mk p) ≃*
    End (e.functor.obj (FundamentalGroupoid.mk p))
  exact e.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk p)

/-- Pointwise, the moving-basepoint equivalence is exactly Mathlib's induced
fundamental-group map for the same concrete configuration homeomorphism. -/
theorem realSplitPinNullFundamentalGroupEquiv_apply
    (g : realSplitPin55) (n : ℕ) (p : Unordered Q55 n)
    (q : @FundamentalGroup (Unordered Q55 n)
      (unorderedConfigurationTopology Q55 n) p) :
    realSplitPinNullFundamentalGroupEquiv g n p q =
      @FundamentalGroup.map (Unordered Q55 n) (Unordered Q55 n)
        (unorderedConfigurationTopology Q55 n)
        (unorderedConfigurationTopology Q55 n)
        (realSplitPinUnorderedNullHomeomorph g n) p q := by
  rfl

end InfoGeometry.Twistor.Cl55RealSplitPinNullFundamentalGroup

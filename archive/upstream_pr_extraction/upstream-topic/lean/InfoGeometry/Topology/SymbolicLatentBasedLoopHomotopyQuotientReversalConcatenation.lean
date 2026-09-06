import Mathlib
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientIdentity
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientReversalBridge
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientReversalNaturality
import InfoGeometry.Topology.SymbolicLatentPathConcatenationReversal

namespace InfoGeometry.Topology

/-!
# Reversal and based-loop quotient concatenation

This is stated on canonical quotient representatives.  It follows from the
pointwise path reversal theorem and therefore does not add an unproved group
inverse law to the quotient.
-/

theorem basedLoopHomotopyQuotientReversal_concatenation_mk
    {X : Type} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
        (basedLoopHomotopyQuotientConcatenation
          (basedLoopHomotopyQuotient_mk γ₀)
          (basedLoopHomotopyQuotient_mk γ₁)) =
      basedLoopHomotopyQuotientConcatenation
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
          (basedLoopHomotopyQuotient_mk γ₁))
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
          (basedLoopHomotopyQuotient_mk γ₀)) := by
  rw [basedLoopHomotopyQuotientConcatenation_mk]
  rw [symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_mk]
  rw [symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_mk,
    symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_mk]
  change _ = basedLoopHomotopyQuotientConcatenation
      (basedLoopHomotopyQuotient_mk
        (reverseSymbolicLatentBasedLoopPath γ₁))
      (basedLoopHomotopyQuotient_mk
        (reverseSymbolicLatentBasedLoopPath γ₀))
  rw [basedLoopHomotopyQuotientConcatenation_mk]
  apply Subtype.ext
  exact reverseSymbolicLatentPath_canonicalSymbolicConcatenation_quotient
    (γ₀.2.2.trans γ₁.2.1.symm)

theorem basedLoopHomotopyQuotientReversal_concatenation
    {X : Type} [TopologicalSpace X] {x : X}
    (q₀ q₁ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
        (basedLoopHomotopyQuotientConcatenation q₀ q₁) =
      basedLoopHomotopyQuotientConcatenation
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q₁)
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q₀) := by
  let γ₀ := basedLoopHomotopyQuotientRepresentativeLoop q₀
  let γ₁ := basedLoopHomotopyQuotientRepresentativeLoop q₁
  have hq₀ : q₀ = basedLoopHomotopyQuotient_mk γ₀ := by
    apply Subtype.ext
    exact (basedLoopHomotopyQuotientRepresentative_quotient_eq q₀).symm
  have hq₁ : q₁ = basedLoopHomotopyQuotient_mk γ₁ := by
    apply Subtype.ext
    exact (basedLoopHomotopyQuotientRepresentative_quotient_eq q₁).symm
  have hconcat :
      basedLoopHomotopyQuotientConcatenation q₀ q₁ =
        basedLoopHomotopyQuotientConcatenation
          (basedLoopHomotopyQuotient_mk γ₀)
          (basedLoopHomotopyQuotient_mk γ₁) := by
    rw [hq₀, hq₁]
  have hrev :
      basedLoopHomotopyQuotientConcatenation
          (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q₁)
          (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q₀) =
        basedLoopHomotopyQuotientConcatenation
          (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
            (basedLoopHomotopyQuotient_mk γ₁))
          (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
            (basedLoopHomotopyQuotient_mk γ₀)) := by
    rw [hq₀, hq₁]
  exact (congrArg
      (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x)
      hconcat).trans
    ((basedLoopHomotopyQuotientReversal_concatenation_mk γ₀ γ₁).trans hrev.symm)

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_concatenation_mk
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
          (basedLoopHomotopyQuotientConcatenation
            (basedLoopHomotopyQuotient_mk γ₀)
            (basedLoopHomotopyQuotient_mk γ₁))) =
      basedLoopHomotopyQuotientConcatenation
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph y
          (basedLoopHomotopyQuotient_mk
            (mapSymbolicLatentBasedLoopPath f hxy γ₁)))
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph y
          (basedLoopHomotopyQuotient_mk
            (mapSymbolicLatentBasedLoopPath f hxy γ₀))) := by
  rw [basedLoopHomotopyQuotientReversal_concatenation_mk]
  rw [mapSymbolicLatentBasedLoopHomotopyQuotient_concatenation]
  congr

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_concatenation
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (q₀ q₁ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
          (basedLoopHomotopyQuotientConcatenation q₀ q₁)) =
      basedLoopHomotopyQuotientConcatenation
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph y
          (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q₁))
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph y
          (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q₀)) := by
  let γ₀ := basedLoopHomotopyQuotientRepresentativeLoop q₀
  let γ₁ := basedLoopHomotopyQuotientRepresentativeLoop q₁
  have hq₀ : q₀ = basedLoopHomotopyQuotient_mk γ₀ := by
    apply Subtype.ext
    exact (basedLoopHomotopyQuotientRepresentative_quotient_eq q₀).symm
  have hq₁ : q₁ = basedLoopHomotopyQuotient_mk γ₁ := by
    apply Subtype.ext
    exact (basedLoopHomotopyQuotientRepresentative_quotient_eq q₁).symm
  rw [hq₀, hq₁]
  simpa [mapSymbolicLatentBasedLoopHomotopyQuotient_mk] using
    (mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_concatenation_mk
      f hxy γ₀ γ₁)

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_concatenation_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (q₀ q₁ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient g hyz
        (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
          (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
            (basedLoopHomotopyQuotientConcatenation q₀ q₁))) =
      mapSymbolicLatentBasedLoopHomotopyQuotient (g.comp f)
        ((congrArg g hxy).trans hyz)
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
          (basedLoopHomotopyQuotientConcatenation q₀ q₁)) := by
  simpa using congrArg (fun h =>
    h (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
      (basedLoopHomotopyQuotientConcatenation q₀ q₁)))
    (mapSymbolicLatentBasedLoopHomotopyQuotient_comp
      (f := f) (g := g) (hxy := hxy) (hyz := hyz))

end InfoGeometry.Topology

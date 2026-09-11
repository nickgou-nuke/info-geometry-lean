import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientReversalBridge
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientFunctoriality

namespace InfoGeometry.Topology

/-!
# Naturality of based-loop reversal

Reversal is compatible with transport along a continuous map preserving the
chosen basepoint.  The statement is kept at the quotient level and does not
promote the based-loop quotient to a group.
-/

theorem mapSymbolicLatentBasedLoopPath_reverse_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopPath f hxy
        (reverseSymbolicLatentBasedLoopPath γ) =
      reverseSymbolicLatentBasedLoopPath
        (mapSymbolicLatentBasedLoopPath f hxy γ) := by
  apply Subtype.ext
  ext t
  rfl

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_natural_mk
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (γ : SymbolicLatentBasedLoopPath x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x
          (basedLoopHomotopyQuotient_mk γ)) =
      symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph y
        (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
          (basedLoopHomotopyQuotient_mk γ)) := by
  rw [symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_mk,
    mapSymbolicLatentBasedLoopHomotopyQuotient_mk,
    symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph_mk]
  apply Subtype.ext
  change mapSymbolicLatentPathHomotopyQuotient f
      (symbolicLatentPathHomotopyQuotientMap
        (reverseSymbolicLatentBasedLoopPath γ).1) =
    symbolicLatentPathHomotopyQuotientMap
      (reverseSymbolicLatentBasedLoopPath
        (mapSymbolicLatentBasedLoopPath f hxy γ)).1
  have hpath := mapSymbolicLatentBasedLoopPath_reverse_natural f hxy γ
  exact congrArg (fun p =>
    symbolicLatentPathHomotopyQuotientMap p.1) hpath

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (hxy : f x = y)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
        (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q) =
      symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph y
        (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q) := by
  let γ := basedLoopHomotopyQuotientRepresentativeLoop q
  have hq : q = basedLoopHomotopyQuotient_mk γ := by
    apply Subtype.ext
    exact (basedLoopHomotopyQuotientRepresentative_quotient_eq q).symm
  rw [hq]
  exact mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_natural_mk
    f hxy γ

theorem mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_natural_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    mapSymbolicLatentBasedLoopHomotopyQuotient g hyz
        (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy
          (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph x q)) =
      symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph z
        (mapSymbolicLatentBasedLoopHomotopyQuotient (g.comp f)
          ((congrArg g hxy).trans hyz) q) := by
  have hcomp :=
    congrArg (fun h =>
      h q) (mapSymbolicLatentBasedLoopHomotopyQuotient_comp f g hxy hyz)
  rw [mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_natural f hxy q]
  rw [mapSymbolicLatentBasedLoopHomotopyQuotient_reversal_natural g hyz
      (mapSymbolicLatentBasedLoopHomotopyQuotient f hxy q)]
  exact congrArg
    (symbolicLatentBasedLoopHomotopyQuotientReversalHomeomorph z) hcomp

end InfoGeometry.Topology

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientConcatenation
import InfoGeometry.Topology.SymbolicLatentPathConcatenationIdentity

namespace InfoGeometry.Topology

/-!
# Identity readouts for based-loop quotient concatenation

The laws here are stated on canonical quotient representatives.  They use the
explicit constant-concatenation homotopies and do not silently promote the
quotient to a group.
-/

def constantSymbolicLatentBasedLoopPath
    {X : Type*} [TopologicalSpace X] (x : X) :
    SymbolicLatentBasedLoopPath x :=
  ⟨constantSymbolicLatentPath x, by constructor <;> rfl⟩

theorem basedLoopHomotopyQuotientConcatenation_left_identity_mk
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    basedLoopHomotopyQuotientConcatenation
        (basedLoopHomotopyQuotient_mk
          (constantSymbolicLatentBasedLoopPath x))
        (basedLoopHomotopyQuotient_mk γ) =
      basedLoopHomotopyQuotient_mk γ := by
  rw [basedLoopHomotopyQuotientConcatenation_mk]
  apply Subtype.ext
  apply Quotient.sound
  exact canonicalSymbolicConcatenation_constant_left_homotopic
    γ.1 γ.2.1

theorem basedLoopHomotopyQuotientConcatenation_right_identity_mk
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    basedLoopHomotopyQuotientConcatenation
        (basedLoopHomotopyQuotient_mk γ)
        (basedLoopHomotopyQuotient_mk
          (constantSymbolicLatentBasedLoopPath x)) =
      basedLoopHomotopyQuotient_mk γ := by
  rw [basedLoopHomotopyQuotientConcatenation_mk]
  apply Subtype.ext
  apply Quotient.sound
  exact canonicalSymbolicConcatenation_constant_right_homotopic
    γ.1 γ.2.2

/-! The same identities for arbitrary quotient elements.  The proof uses the
chosen `Quotient.out` representatives only internally; the final equality is
in the quotient and hence is independent of that choice. -/

theorem basedLoopHomotopyQuotientConcatenation_left_identity
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    basedLoopHomotopyQuotientConcatenation
        (basedLoopHomotopyQuotient_mk
          (constantSymbolicLatentBasedLoopPath x)) q = q := by
  let e := constantSymbolicLatentBasedLoopPath x
  let γ := basedLoopHomotopyQuotientRepresentativeLoop q
  have hrep : SymbolicLatentPathHomotopic
      (basedLoopHomotopyQuotientRepresentativeLoop
        (basedLoopHomotopyQuotient_mk e)).1 e.1 :=
    Quotient.exact (by
      simpa using
        (basedLoopHomotopyQuotientRepresentative_quotient_eq
          (basedLoopHomotopyQuotient_mk e)))
  have hconcat : SymbolicLatentPathHomotopic
      (canonicalSymbolicLatentBasedLoopConcatenation
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk e)) γ).1
      (canonicalSymbolicLatentBasedLoopConcatenation e γ).1 :=
    concatenatedSymbolicPathHomotopic_of_homotopies
      ((basedLoopHomotopyQuotientRepresentativeLoop
        (basedLoopHomotopyQuotient_mk e)).2.2.trans γ.2.1.symm)
      (e.2.2.trans γ.2.1.symm)
      hrep.some (SymbolicLatentPathHomotopic.refl γ.1).some
  have htotal : SymbolicLatentPathHomotopic
      (canonicalSymbolicLatentBasedLoopConcatenation
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk e)) γ).1 γ.1 :=
    hconcat.trans (canonicalSymbolicConcatenation_constant_left_homotopic
      γ.1 γ.2.1)
  apply Subtype.ext
  change symbolicLatentPathHomotopyQuotientMap
      (canonicalSymbolicLatentBasedLoopConcatenation
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk e)) γ).1 = q.1
  exact (Quotient.sound htotal).trans
    (basedLoopHomotopyQuotientRepresentative_quotient_eq q)

theorem basedLoopHomotopyQuotientConcatenation_right_identity
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    basedLoopHomotopyQuotientConcatenation q
        (basedLoopHomotopyQuotient_mk
          (constantSymbolicLatentBasedLoopPath x)) = q := by
  let e := constantSymbolicLatentBasedLoopPath x
  let γ := basedLoopHomotopyQuotientRepresentativeLoop q
  have hrep : SymbolicLatentPathHomotopic
      (basedLoopHomotopyQuotientRepresentativeLoop
        (basedLoopHomotopyQuotient_mk e)).1 e.1 :=
    Quotient.exact (by
      simpa using
        (basedLoopHomotopyQuotientRepresentative_quotient_eq
          (basedLoopHomotopyQuotient_mk e)))
  have hconcat : SymbolicLatentPathHomotopic
      (canonicalSymbolicLatentBasedLoopConcatenation γ
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk e))).1
      (canonicalSymbolicLatentBasedLoopConcatenation γ e).1 :=
    concatenatedSymbolicPathHomotopic_of_homotopies
      (γ.2.2.trans
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk e)).2.1.symm)
      (γ.2.2.trans e.2.1.symm)
      (SymbolicLatentPathHomotopic.refl γ.1).some hrep.some
  have htotal : SymbolicLatentPathHomotopic
      (canonicalSymbolicLatentBasedLoopConcatenation γ
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk e))).1 γ.1 :=
    hconcat.trans (canonicalSymbolicConcatenation_constant_right_homotopic
      γ.1 γ.2.2)
  apply Subtype.ext
  change symbolicLatentPathHomotopyQuotientMap
      (canonicalSymbolicLatentBasedLoopConcatenation γ
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk e))).1 = q.1
  exact (Quotient.sound htotal).trans
    (basedLoopHomotopyQuotientRepresentative_quotient_eq q)

theorem basedLoopHomotopyQuotientConcatenation_left_identity_endpoints
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyEndpointMap
        (basedLoopHomotopyQuotientConcatenation
          (basedLoopHomotopyQuotient_mk
            (constantSymbolicLatentBasedLoopPath x)) q).1 =
      (x, x) := by
  rw [basedLoopHomotopyQuotientConcatenation_left_identity q]
  exact q.2

theorem basedLoopHomotopyQuotientConcatenation_right_identity_endpoints
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyEndpointMap
        (basedLoopHomotopyQuotientConcatenation q
          (basedLoopHomotopyQuotient_mk
            (constantSymbolicLatentBasedLoopPath x))).1 =
      (x, x) := by
  rw [basedLoopHomotopyQuotientConcatenation_right_identity q]
  exact q.2

end InfoGeometry.Topology

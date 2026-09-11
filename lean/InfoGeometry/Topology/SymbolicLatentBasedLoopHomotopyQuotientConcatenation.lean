import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopConcatenationQuotient
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotient

namespace InfoGeometry.Topology

/-!
# A representative-based concatenation on the based-loop quotient

The quotient is not given a group law by fiat.  Instead, a noncomputable
representative is extracted with `Quotient.out`; the endpoint-fiber proof is
then reconstructed and the resulting class is shown to agree with every
chosen representative by the previously proved homotopy congruence.
-/

noncomputable def basedLoopHomotopyQuotientRepresentative
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    SymbolicLatentPath X :=
  q.1.out

theorem basedLoopHomotopyQuotientRepresentative_quotient_eq
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyQuotientMap
        (basedLoopHomotopyQuotientRepresentative q) = q.1 :=
  Quotient.out_eq q.1

theorem basedLoopHomotopyQuotientRepresentative_endpoints
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    (basedLoopHomotopyQuotientRepresentative q).endpoints = (x, x) := by
  exact (congrArg symbolicLatentPathHomotopyEndpointMap
    (basedLoopHomotopyQuotientRepresentative_quotient_eq q)).trans q.2

noncomputable def basedLoopHomotopyQuotientRepresentativeLoop
    {X : Type} [TopologicalSpace X] {x : X}
    (q : SymbolicLatentBasedLoopHomotopyQuotient x) :
    SymbolicLatentBasedLoopPath x :=
  ⟨basedLoopHomotopyQuotientRepresentative q,
    ⟨congrArg Prod.fst (basedLoopHomotopyQuotientRepresentative_endpoints q),
      congrArg Prod.snd (basedLoopHomotopyQuotientRepresentative_endpoints q)⟩⟩

noncomputable def basedLoopHomotopyQuotientConcatenation
    {X : Type} [TopologicalSpace X] {x : X}
    (q₀ q₁ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    SymbolicLatentBasedLoopHomotopyQuotient x := by
  let γ₀ := basedLoopHomotopyQuotientRepresentativeLoop q₀
  let γ₁ := basedLoopHomotopyQuotientRepresentativeLoop q₁
  let c := canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁
  exact ⟨symbolicLatentPathHomotopyQuotientMap c.1, by
    rw [symbolicLatentPathHomotopyEndpointMap_mk]
    change (c.1.start, c.1.finish) = (x, x)
    exact Prod.ext c.2.1 c.2.2⟩

def basedLoopHomotopyQuotient_mk
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    SymbolicLatentBasedLoopHomotopyQuotient x :=
  ⟨symbolicLatentPathHomotopyQuotientMap (X := X) γ.1, by
    rw [symbolicLatentPathHomotopyEndpointMap_mk]
    change (γ.1.start, γ.1.finish) = (x, x)
    exact Prod.ext γ.2.1 γ.2.2⟩

theorem basedLoopHomotopyQuotientConcatenation_mk
    {X : Type} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    basedLoopHomotopyQuotientConcatenation
        (basedLoopHomotopyQuotient_mk γ₀)
        (basedLoopHomotopyQuotient_mk γ₁) =
      basedLoopHomotopyQuotient_mk
        (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁) := by
  apply Subtype.ext
  apply basedLoopConcatenation_quotient_congr
  · have hrel : SymbolicLatentPathHomotopic
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk γ₀)).1 γ₀.1 :=
      Quotient.exact (by
        simpa using
          (basedLoopHomotopyQuotientRepresentative_quotient_eq
            (basedLoopHomotopyQuotient_mk γ₀)))
    exact hrel.some
  · have hrel : SymbolicLatentPathHomotopic
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotient_mk γ₁)).1 γ₁.1 :=
      Quotient.exact (by
        simpa using
          (basedLoopHomotopyQuotientRepresentative_quotient_eq
            (basedLoopHomotopyQuotient_mk γ₁)))
    exact hrel.some

theorem basedLoopHomotopyQuotientConcatenation_endpoints
    {X : Type} [TopologicalSpace X] {x : X}
    (q₀ q₁ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    symbolicLatentPathHomotopyEndpointMap
        (basedLoopHomotopyQuotientConcatenation q₀ q₁).1 = (x, x) :=
  (basedLoopHomotopyQuotientConcatenation q₀ q₁).2

end InfoGeometry.Topology

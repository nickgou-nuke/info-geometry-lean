import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.TomitaTransportReadback

Finite term-stream transport/readback for a closed lambda-term graph.

This is a small syntax-level owner surface. It does not assert any operator-
algebraic Tomita-Takesaki structure; it only records the transport/readback
inversion for the finite token machine described in the module statement.
-/

namespace InfoGeometry.Canonical.TomitaTransportReadback

/-- Flat stream tokens for the linearized term representation. -/
inductive StreamToken : Type
  | app : StreamToken
  | lam : Nat → StreamToken
  | var : Nat → StreamToken

/-- Closed-term graph syntax. -/
inductive TermGraph : Type
  | var : Nat → TermGraph
  | app : TermGraph → TermGraph → TermGraph
  | lam : Nat → TermGraph → TermGraph

open StreamToken
open TermGraph

/-- Transport a term graph to a flat token stream. -/
def transport : TermGraph → List StreamToken
  | TermGraph.var n => [StreamToken.var n]
  | TermGraph.app t1 t2 => transport t1 ++ transport t2 ++ [StreamToken.app]
  | TermGraph.lam n t => transport t ++ [StreamToken.lam n]

/-- Read back a term graph from a token stream and stack. -/
def readback_aux : List StreamToken → List TermGraph → Option TermGraph
  | [], [t] => some t
  | StreamToken.var n :: tokens, stack =>
      readback_aux tokens (TermGraph.var n :: stack)
  | StreamToken.app :: tokens, t2 :: t1 :: stack =>
      readback_aux tokens (TermGraph.app t1 t2 :: stack)
  | StreamToken.lam n :: tokens, t :: stack =>
      readback_aux tokens (TermGraph.lam n t :: stack)
  | _, _ => none

/-- Read back a term graph from a token stream. -/
def readback (tokens : List StreamToken) : Option TermGraph :=
  readback_aux tokens []

/--
Transport readback commutes with stack extension: transporting a term into a
stack is the same as pushing the term onto the stack and continuing.
-/
theorem readback_aux_append (t : TermGraph) (tokens : List StreamToken)
    (stack : List TermGraph) :
    readback_aux (transport t ++ tokens) stack = readback_aux tokens (t :: stack) := by
  induction t generalizing tokens stack with
  | var n =>
      simp [transport, readback_aux]
  | app t1 t2 ih1 ih2 =>
      simp [transport, List.append_assoc]
      rw [ih1]
      rw [ih2]
      rfl
  | lam n t ih =>
      simp [transport, List.append_assoc]
      rw [ih]
      rfl

/-- The transport/readback inversion theorem. -/
theorem tomita_transport_readback_inverse (t : TermGraph) :
    readback (transport t) = some t := by
  simpa [readback] using (readback_aux_append (t := t) (tokens := []) (stack := []))

end InfoGeometry.Canonical.TomitaTransportReadback

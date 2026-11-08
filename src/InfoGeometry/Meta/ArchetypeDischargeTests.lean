import InfoGeometry.Meta.ArchetypeDischarge

open InfoGeometry.MetaCompiler

-- ============================================================================
-- 1. Simple Candidate Discharged via `rfl`
-- ============================================================================

def addZeroCandidate : TypedArchetype Nat .candidate where
  name     := `addZeroCandidate
  phase    := 1
  claim    := fun n => n + 0 = n
  evidence := trivial

#register_archetype addZeroCandidate

-- Auto-promote using the default solver portfolio:
#auto_promote addZeroCandidate

-- Verified: `addZeroCandidate.proved` now exists in the kernel and extension.
#check addZeroCandidate.proved

-- ============================================================================
-- 2. Linear Arithmetic Candidate Discharged via `omega`
-- ============================================================================

def triangleCandidate : TypedArchetype (Nat × Nat) .candidate where
  name     := `triangleCandidate
  phase    := 2
  claim    := fun (a, b) => a + b ≥ a
  evidence := trivial

#register_archetype triangleCandidate

#auto_promote triangleCandidate as triangleProved

#check triangleProved

-- ============================================================================
-- 3. Parameterized Candidate Archetype (Pi-binders)
-- ============================================================================

def offsetCandidate (offset : Nat) : TypedArchetype Nat .candidate where
  name     := `offsetCandidate
  phase    := 1
  claim    := fun n => n + offset ≥ offset
  evidence := trivial

#register_archetype offsetCandidate

-- The telescope reducer abstracts `offset` into a Pi-type
#auto_promote offsetCandidate

#check offsetCandidate.proved

-- ============================================================================
-- 4. Guided Promotion with Custom Tactic Script
-- ============================================================================

def inductionCandidate : TypedArchetype Nat .candidate where
  name     := `inductionCandidate
  phase    := 3
  claim    := fun n => 0 + n = n
  evidence := trivial

#register_archetype inductionCandidate

-- Complex goal solved using an explicit tactic block:
#promote_archetype inductionCandidate as inductionProved by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

-- ============================================================================
-- 5. Batch Auto-Promotion
-- ============================================================================

#auto_promote_all
#search_typed_archetypes

-- ============================================================================
-- 6. In-Proof Tactic Extraction
-- ============================================================================

example (m : Nat) : m + 0 = m := by
  discharge_archetype addZeroCandidate.proved m

example (x y : Nat) : x + y ≥ x := by
  have_archetype triangleProved with (x, y) as h
  exact h


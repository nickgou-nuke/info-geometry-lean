import InfoGeometry.Geometry.DressingFieldDependency

namespace InfoGeometry.Geometry.DressingField.Tests

variable {Gauge : Type*} [Group Gauge]

def firstFrame : (Gauge × Gauge) →[Gauge] Gauge where
  toFun := Prod.fst
  map_smul' _ _ := rfl

def secondFrame : (Gauge × Gauge) →[Gauge] Gauge where
  toFun := Prod.snd
  map_smul' _ _ := rfl

example (first second : Gauge) :
    dressed firstFrame secondFrame (first, second) = first⁻¹ * second := rfl

example (gauge first second : Gauge) :
    dressed firstFrame secondFrame (gauge * first, gauge * second) =
      dressed firstFrame secondFrame (first, second) :=
  dressed_invariant firstFrame secondFrame gauge (first, second)

example (first second : Gauge) :
    normalize firstFrame (first, second) = (1, first⁻¹ * second) := by
  change (first⁻¹ * first, first⁻¹ * second) = (1, first⁻¹ * second)
  simp

example :
    dressed firstFrame secondFrame
      (Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2) 0 = 1 := by
  decide

example :
    ¬ Nonempty (Unit →[Equiv.Perm (Fin 2)] Equiv.Perm (Fin 2)) := by
  exact no_global_frame_of_stabilizer (Equiv.swap (0 : Fin 2) 1) ()
    (by decide) (by rfl)

example :
    relationalField (Equiv.swap (0 : Fin 3) 1) (fun index => index.val) 0 = 1 := by
  decide

example (coordinate : Equiv.Perm (Fin 3)) (field : Fin 3 → ℕ) :
    relationalField ((Equiv.swap (0 : Fin 3) 1).symm.trans coordinate)
        (field ∘ (Equiv.swap (0 : Fin 3) 1).symm) =
      relationalField coordinate field :=
  relationalField_relabel coordinate field (Equiv.swap (0 : Fin 3) 1)

#print axioms dressed_invariant
#print axioms onOrbit
#print axioms onOrbit_mk
#print axioms onOrbit_unique
#print axioms transition_invariant
#print axioms transition_self
#print axioms transition_cocycle
#print axioms dressed_change_frame
#print axioms stabilizer_trivial
#print axioms no_global_frame_of_stabilizer
#print axioms normalize_eq_iff_orbit
#print axioms normalize_invariant
#print axioms frame_normalize
#print axioms normalize_idempotent
#print axioms relationalField_relabel
#print axioms relationalField_change_reference
#print axioms ProofDependency.causal_branches
#print axioms ProofDependency.descent_and_obstruction_incomparable
#print axioms ProofDependency.no_dependency_cycle

end InfoGeometry.Geometry.DressingField.Tests

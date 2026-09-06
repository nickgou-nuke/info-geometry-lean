import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

/-!
# Fixed Lean-PC generators for the native flag-stabilizer readback

The six words below are written in the repository's fixed `PCExponent`
coordinate order.  This owner records only the native subgroup facts that
can be proved without importing an external PCGS basis or a CAS certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators

open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

def pcBits (b₀ b₁ b₂ b₃ b₄ b₅ : Bool) : PCWordExp := fun i =>
  if i = 0 then b₀ else
  if i = 1 then b₁ else
  if i = 2 then b₂ else
  if i = 3 then b₃ else
  if i = 4 then b₄ else b₅

def stabilizerPCGenerators :
    Set InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut :=
  Set.insert (pcWord (pcBits false false false false false true))
    (Set.insert (pcWord (pcBits false false false true false true))
      (Set.insert (pcWord (pcBits false false true false true false))
        (Set.insert (pcWord (pcBits false true true false false true))
          (Set.insert (pcWord (pcBits true false false false false false))
            (Set.singleton
              (pcWord (pcBits true false true true false true)))))))

theorem stabilizerPCGenerators_subset_unipotentSubgroup :
    stabilizerPCGenerators ⊆ unipotentSubgroup.carrier := by
  intro g hg
  have hg' :
      g = pcWord (pcBits false false false false false true) ∨
      g = pcWord (pcBits false false false true false true) ∨
      g = pcWord (pcBits false false true false true false) ∨
      g = pcWord (pcBits false true true false false true) ∨
      g = pcWord (pcBits true false false false false false) ∨
      g = pcWord (pcBits true false true true false true) := by
    simpa [stabilizerPCGenerators] using hg
  rcases hg' with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨_, rfl⟩

theorem stabilizerPCGenerators_closure_le_unipotentSubgroup :
    Subgroup.closure stabilizerPCGenerators ≤ unipotentSubgroup := by
  exact (Subgroup.closure_le _).2 stabilizerPCGenerators_subset_unipotentSubgroup

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators

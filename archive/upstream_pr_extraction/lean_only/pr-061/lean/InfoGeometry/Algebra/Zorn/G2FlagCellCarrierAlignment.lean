import InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate

/-!
# Carrier alignment for the finite G2 flag-cell witness table

The witness tables in `G2FlagCellWitnessCertificate` are retained as data until
they are checked against the current Lean `flagRepresentative` carrier.  This
owner performs exactly that finite check and then transports it through the
native matrix-faithfulness theorem.

No Bruhat-cell disjointness, global coverage, or total Bruhat index is asserted
here.  Those are downstream consequences requiring the complementary reverse
cell-identification / uniqueness step.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagCellCarrierAlignment

open InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- Closed finite certificate: every exported left/right PC witness attached to
an index in `orbitCells k` reproduces the current Lean flag representative at
the faithful matrix readout. -/
set_option maxRecDepth 100000 in
theorem flagRepresentative_factorization_matrix :
    ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      autMatrix (flagRepresentative i) =
        autMatrix
          (pcWord (leftWitness k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
            pcWord (rightWitness k i)) := by
  native_decide

/-- Carrier-level alignment of the exported witness table with the native Lean
`flagRepresentative` automorphisms. -/
theorem flagRepresentative_factorization
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      pcWord (leftWitness k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        pcWord (rightWitness k i) := by
  apply autMatrix_injective
  exact flagRepresentative_factorization_matrix k i hi

/-- Every finite certificate representative lies in the concrete Bruhat cell
indexed by its recorded Weyl parameter. -/
theorem flagRepresentative_mem_concreteBruhatCell
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i ∈
      concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
  refine ⟨pcWord (leftWitness k i), pcWord (rightWitness k i),
    pcWord_mem_sylow _, pcWord_mem_sylow _, ?_⟩
  exact flagRepresentative_factorization k i hi

end InfoGeometry.Algebra.Zorn.G2FlagCellCarrierAlignment

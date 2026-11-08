import InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

/-!
# Kernel-checked 189-point Bruhat orbit-membership certificate

The data `leftWitness` and `rightWitness` are the orientation-corrected
PC-coordinate witnesses exported from GAP.  This file does not trust the CAS
equalities.  For each certified `(cell,index)` row it checks the supplied
witness on the faithful `autMatrix` carrier and then transports that equality
to the native quotient.

There is no search over `Fin 12 × Fin 189`, no enumeration of
`SplitOctF2Aut`, and no cardinality argument.
-/

namespace InfoGeometry.Algebra.Zorn.G2Fin189OrbitMembershipCertificate

open InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate
open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

private theorem row_orbit_witness
    (k : Fin 12) (i : Fin 189)
    (hmat :
      autMatrix ((flagRepresentative i)⁻¹ *
        (pcWord (leftWitness k i) *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2)) =
        autMatrix (pcWord (pcInverse (rightWitness k i)))) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i =
          b •
            (QuotientGroup.mk
              (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
                CarrierQuotient) := by
  refine ⟨pcWord (leftWitness k i), ?_, ?_⟩
  · exact ⟨leftWitness k i, rfl⟩
  · apply quotientRepresentative_eq_left_smul_of_pc_matrix
    exact ⟨pcInverse (rightWitness k i), hmat⟩

set_option maxRecDepth 100000 in
theorem hcell_0 (i : Fin 189) (hi : i ∈ orbitCells 0) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 0).1 (orbitWeyl 0).2) : CarrierQuotient) := by
  have hi' : i = 0 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_1 (i : Fin 189) (hi : i ∈ orbitCells 1) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  have hi' : i = 24 ∨ i = 45 ∨ i = 178 ∨ i = 73 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_2 (i : Fin 189) (hi : i ∈ orbitCells 2) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 2).1 (orbitWeyl 2).2) : CarrierQuotient) := by
  have hi' : i = 3 ∨ i = 57 ∨ i = 185 ∨ i = 83 ∨ i = 96 ∨ i = 173 ∨
      i = 12 ∨ i = 122 ∨ i = 170 ∨ i = 175 ∨ i = 55 ∨ i = 167 ∨
      i = 49 ∨ i = 106 ∨ i = 79 ∨ i = 163 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem hcell_3 (i : Fin 189) (hi : i ∈ orbitCells 3) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 3).1 (orbitWeyl 3).2) : CarrierQuotient) := by
  have hi' : i = 9 ∨ i = 52 ∨ i = 75 ∨ i = 31 ∨ i = 111 ∨ i = 68 ∨
      i = 70 ∨ i = 126 ∨ i = 35 ∨ i = 150 ∨ i = 64 ∨ i = 93 ∨
      i = 89 ∨ i = 157 ∨ i = 114 ∨ i = 71 ∨ i = 66 ∨ i = 40 ∨
      i = 104 ∨ i = 156 ∨ i = 125 ∨ i = 155 ∨ i = 153 ∨ i = 187 ∨
      i = 118 ∨ i = 11 ∨ i = 110 ∨ i = 77 ∨ i = 86 ∨ i = 65 ∨
      i = 144 ∨ i = 33 ∨ i = 142 ∨ i = 27 ∨ i = 128 ∨ i = 138 ∨
      i = 21 ∨ i = 39 ∨ i = 143 ∨ i = 42 ∨ i = 38 ∨ i = 44 ∨
      i = 22 ∨ i = 119 ∨ i = 61 ∨ i = 30 ∨ i = 108 ∨ i = 188 ∨
      i = 94 ∨ i = 123 ∨ i = 62 ∨ i = 136 ∨ i = 139 ∨ i = 112 ∨
      i = 85 ∨ i = 115 ∨ i = 28 ∨ i = 87 ∨ i = 51 ∨ i = 145 ∨
      i = 137 ∨ i = 36 ∨ i = 152 ∨ i = 103 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_4 (i : Fin 189) (hi : i ∈ orbitCells 4) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 4).1 (orbitWeyl 4).2) : CarrierQuotient) := by
  have hi' : i = 6 ∨ i = 101 ∨ i = 20 ∨ i = 18 ∨ i = 130 ∨ i = 8 ∨
      i = 180 ∨ i = 91 ∨ i = 182 ∨ i = 147 ∨ i = 100 ∨ i = 133 ∨
      i = 92 ∨ i = 134 ∨ i = 131 ∨ i = 148 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_5 (i : Fin 189) (hi : i ∈ orbitCells 5) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 5).1 (orbitWeyl 5).2) : CarrierQuotient) := by
  have hi' : i = 15 ∨ i = 160 ∨ i = 17 ∨ i = 159 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_6 (i : Fin 189) (hi : i ∈ orbitCells 6) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 6).1 (orbitWeyl 6).2) : CarrierQuotient) := by
  have hi' : i = 1 ∨ i = 2 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_7 (i : Fin 189) (hi : i ∈ orbitCells 7) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 7).1 (orbitWeyl 7).2) : CarrierQuotient) := by
  have hi' : i = 16 ∨ i = 161 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_8 (i : Fin 189) (hi : i ∈ orbitCells 8) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 8).1 (orbitWeyl 8).2) : CarrierQuotient) := by
  have hi' : i = 7 ∨ i = 99 ∨ i = 19 ∨ i = 129 ∨ i = 181 ∨ i = 90 ∨
      i = 149 ∨ i = 132 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_9 (i : Fin 189) (hi : i ∈ orbitCells 9) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 9).1 (orbitWeyl 9).2) : CarrierQuotient) := by
  have hi' : i = 10 ∨ i = 53 ∨ i = 76 ∨ i = 32 ∨ i = 113 ∨ i = 67 ∨
      i = 69 ∨ i = 127 ∨ i = 34 ∨ i = 151 ∨ i = 63 ∨ i = 95 ∨
      i = 88 ∨ i = 158 ∨ i = 116 ∨ i = 41 ∨ i = 102 ∨ i = 124 ∨
      i = 154 ∨ i = 186 ∨ i = 117 ∨ i = 109 ∨ i = 84 ∨ i = 146 ∨
      i = 141 ∨ i = 29 ∨ i = 140 ∨ i = 23 ∨ i = 43 ∨ i = 37 ∨
      i = 60 ∨ i = 135 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_10 (i : Fin 189) (hi : i ∈ orbitCells 10) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 10).1 (orbitWeyl 10).2) : CarrierQuotient) := by
  have hi' : i = 4 ∨ i = 5 ∨ i = 58 ∨ i = 184 ∨ i = 82 ∨ i = 97 ∨
      i = 59 ∨ i = 183 ∨ i = 81 ∨ i = 98 ∨ i = 171 ∨ i = 14 ∨
      i = 121 ∨ i = 13 ∨ i = 169 ∨ i = 174 ∨ i = 168 ∨ i = 54 ∨
      i = 165 ∨ i = 48 ∨ i = 172 ∨ i = 120 ∨ i = 176 ∨ i = 56 ∨
      i = 166 ∨ i = 50 ∨ i = 107 ∨ i = 78 ∨ i = 105 ∨ i = 164 ∨
      i = 162 ∨ i = 80 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem hcell_11 (i : Fin 189) (hi : i ∈ orbitCells 11) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 11).1 (orbitWeyl 11).2) : CarrierQuotient) := by
  have hi' : i = 25 ∨ i = 47 ∨ i = 177 ∨ i = 26 ∨ i = 72 ∨ i = 46 ∨
      i = 179 ∨ i = 74 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply row_orbit_witness
    decide

set_option maxRecDepth 100000 in
theorem fin189_orbit_membership
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : CarrierQuotient) := by
  fin_cases k
  · exact hcell_0 i hi
  · exact hcell_1 i hi
  · exact hcell_2 i hi
  · exact hcell_3 i hi
  · exact hcell_4 i hi
  · exact hcell_5 i hi
  · exact hcell_6 i hi
  · exact hcell_7 i hi
  · exact hcell_8 i hi
  · exact hcell_9 i hi
  · exact hcell_10 i hi
  · exact hcell_11 i hi

end InfoGeometry.Algebra.Zorn.G2Fin189OrbitMembershipCertificate

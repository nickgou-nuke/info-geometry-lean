theory KawamuraInfiniteWedge
  imports Main
begin

section ‹Kawamura's Infinite Wedge and Recursive Fermion System›

text ‹
  Following Katsunori Kawamura, we construct the branching functions 
  on the space of Maya diagrams which give rise to the infinite wedge 
  representation of the CAR algebra and its extension to the Cuntz algebra O2.
›

type_synonym maya_index = int

definition vacuum :: "maya_index set" where
  "vacuum = {j. j ≤ 0}"

definition dual_vacuum :: "maya_index set" where
  "dual_vacuum = {j. j ≥ 1}"

definition is_maya :: "maya_index set ⇒ bool" where
  "is_maya S ⟷ finite ((S - vacuum) ∪ (vacuum - S))"

definition is_dual_maya :: "maya_index set ⇒ bool" where
  "is_dual_maya S ⟷ finite ((S - dual_vacuum) ∪ (dual_vacuum - S))"

subsection ‹Branching Functions›

definition s_plus :: "maya_index set ⇒ maya_index set" where
  "s_plus S = S ∩ {j. j ≥ 1}"

definition s_minus :: "maya_index set ⇒ maya_index set" where
  "s_minus S = S ∩ {j. j ≤ 0}"

definition shift_plus :: "maya_index set ⇒ maya_index set" where
  "shift_plus S = {j + 1 | j. j ∈ S}"

definition negate_index :: "maya_index set ⇒ maya_index set" where
  "negate_index S = {1 - j | j. j ∈ S}"

definition g1 :: "maya_index set ⇒ maya_index set" where
  "g1 S = negate_index (shift_plus (s_plus S) ∪ (s_minus S) ∪ {1})"

definition g2 :: "maya_index set ⇒ maya_index set" where
  "g2 S = negate_index (shift_plus (s_plus S) ∪ (s_minus S))"

subsection ‹Thermodynamic Limit Colimit Properties›

text ‹
  The branching functions g1 and g2 map Maya diagrams to Dual Maya diagrams,
  implementing the Z2 symmetry breaking of the Cuntz algebra over the Fermi sea.
›

lemma g2_maps_maya_to_dual:
  assumes "is_maya S"
  shows "is_dual_maya (g2 S)"
  sorry

lemma g1_maps_maya_to_dual:
  assumes "is_maya S"
  shows "is_dual_maya (g1 S)"
  sorry

end

import sympy as sp

lean_code = """import Mathlib
import proofs.SplitOctonionTrialitySO44Equivalence

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityEquiv
open SplitOctonionTrialityCore

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

"""

for u in range(8):
    for v in range(8):
        lean_code += f"lemma triality_vertex_{u}_{v} (A : SO44) :\n"
        lean_code += f"  (Subtype.val A) (basis {u} * basis {v}) - trialityPartnerB A (basis {u}) * basis {v} - basis {u} * trialityPartnerC A (basis {v}) = 0 := by\n"
        
        # dsimp triality formulas
        lean_code += f"  dsimp [trialityPartnerB, trialityPartnerC]\n"
        lean_code += f"  simp only [LinearMap.sub_apply, LinearMap.comp_apply, octMulRight_apply, octMulLeft_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.add_apply]\n"
        
        # substitute A_val_expansion everywhere
        lean_code += f"  simp only [A_val_expansion A]\n"
        
        # dsimp everything else
        lean_code += f"  dsimp [splitBilinear, splitNorm, basis, smul_def, add_def, sub_def, neg_def, mul_def]\n"
        
        # Now apply the skewness constraints
        for i in range(8):
            for j in range(i+1, 8):
                lean_code += f"  have h_skew_{i}_{j} : matrixElem A {j} {i} = - matrixElem A {i} {j} := eq_neg_of_add_eq_zero_left (matrixElem_skew A {i} {j})\n"
                lean_code += f"  rw [h_skew_{i}_{j}]\n"
            # for i=j it is 0
            lean_code += f"  have h_skew_{i}_{i} : matrixElem A {i} {i} = 0 := by\n"
            lean_code += f"    have h := matrixElem_skew A {i} {i}\n"
            lean_code += f"    linarith\n"
            lean_code += f"  rw [h_skew_{i}_{i}]\n"
        
        lean_code += f"  ring_nf\n\n"

lean_code += """
noncomputable def trialityVertexBilinear (A : SO44) : SplitOct →ₗ[ℝ] SplitOct →ₗ[ℝ] SplitOct where
  toFun x := {
    toFun := fun y => (Subtype.val A) (x * y) - trialityPartnerB A x * y - x * trialityPartnerC A y
    map_add' := by 
      intro y1 y2
      simp only [mul_add, LinearMap.map_add]
      abel
    map_smul' := by 
      intro c y
      simp only [mul_smul_comm, smul_mul_assoc, LinearMap.map_smul, RingHom.id_apply]
      abel
  }
  map_add' := by 
    intro x1 x2
    apply LinearMap.ext; intro y
    simp only [add_mul, LinearMap.map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    abel
  map_smul' := by 
    intro c x
    apply LinearMap.ext; intro y
    simp only [smul_mul_assoc, smul_add, smul_sub, mul_smul_comm, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    abel

lemma triality_vertex_eq (A : SO44) (x y : SplitOct) :
  (Subtype.val A) (x * y) = trialityPartnerB A x * y + x * trialityPartnerC A y := by
  have H : trialityVertexBilinear A x y = 0 := by
    rw [oct_expansion x, oct_expansion y]
    simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    -- The goal is now a sum of terms involving trialityVertexBilinear A (basis u) (basis v)
    -- We can replace them all with 0 using our 64 lemmas.
    have h00 := triality_vertex_0_0 A
    have h01 := triality_vertex_0_1 A
    have h02 := triality_vertex_0_2 A
    have h03 := triality_vertex_0_3 A
    have h04 := triality_vertex_0_4 A
    have h05 := triality_vertex_0_5 A
    have h06 := triality_vertex_0_6 A
    have h07 := triality_vertex_0_7 A
    have h10 := triality_vertex_1_0 A
    have h11 := triality_vertex_1_1 A
    have h12 := triality_vertex_1_2 A
    have h13 := triality_vertex_1_3 A
    have h14 := triality_vertex_1_4 A
    have h15 := triality_vertex_1_5 A
    have h16 := triality_vertex_1_6 A
    have h17 := triality_vertex_1_7 A
    have h20 := triality_vertex_2_0 A
    have h21 := triality_vertex_2_1 A
    have h22 := triality_vertex_2_2 A
    have h23 := triality_vertex_2_3 A
    have h24 := triality_vertex_2_4 A
    have h25 := triality_vertex_2_5 A
    have h26 := triality_vertex_2_6 A
    have h27 := triality_vertex_2_7 A
    have h30 := triality_vertex_3_0 A
    have h31 := triality_vertex_3_1 A
    have h32 := triality_vertex_3_2 A
    have h33 := triality_vertex_3_3 A
    have h34 := triality_vertex_3_4 A
    have h35 := triality_vertex_3_5 A
    have h36 := triality_vertex_3_6 A
    have h37 := triality_vertex_3_7 A
    have h40 := triality_vertex_4_0 A
    have h41 := triality_vertex_4_1 A
    have h42 := triality_vertex_4_2 A
    have h43 := triality_vertex_4_3 A
    have h44 := triality_vertex_4_4 A
    have h45 := triality_vertex_4_5 A
    have h46 := triality_vertex_4_6 A
    have h47 := triality_vertex_4_7 A
    have h50 := triality_vertex_5_0 A
    have h51 := triality_vertex_5_1 A
    have h52 := triality_vertex_5_2 A
    have h53 := triality_vertex_5_3 A
    have h54 := triality_vertex_5_4 A
    have h55 := triality_vertex_5_5 A
    have h56 := triality_vertex_5_6 A
    have h57 := triality_vertex_5_7 A
    have h60 := triality_vertex_6_0 A
    have h61 := triality_vertex_6_1 A
    have h62 := triality_vertex_6_2 A
    have h63 := triality_vertex_6_3 A
    have h64 := triality_vertex_6_4 A
    have h65 := triality_vertex_6_5 A
    have h66 := triality_vertex_6_6 A
    have h67 := triality_vertex_6_7 A
    have h70 := triality_vertex_7_0 A
    have h71 := triality_vertex_7_1 A
    have h72 := triality_vertex_7_2 A
    have h73 := triality_vertex_7_3 A
    have h74 := triality_vertex_7_4 A
    have h75 := triality_vertex_7_5 A
    have h76 := triality_vertex_7_6 A
    have h77 := triality_vertex_7_7 A
    -- wait, we must unfold trialityVertexBilinear to apply h00
    change ∀ x y, trialityVertexBilinear A x y = A.val (x * y) - trialityPartnerB A x * y - x * trialityPartnerC A y at h00 h01
    -- Actually, h00 is ALREADY exactly the RHS!
    -- So we can just rewrite!
    -- But trialityVertexBilinear is NOT in h00. We just change the goal.
    -- The goal has trialityVertexBilinear A (basis u) (basis v).
    -- We can just unfold it!
    simp only [trialityVertexBilinear, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [h00, h01, h02, h03, h04, h05, h06, h07]
    simp only [h10, h11, h12, h13, h14, h15, h16, h17]
    simp only [h20, h21, h22, h23, h24, h25, h26, h27]
    simp only [h30, h31, h32, h33, h34, h35, h36, h37]
    simp only [h40, h41, h42, h43, h44, h45, h46, h47]
    simp only [h50, h51, h52, h53, h54, h55, h56, h57]
    simp only [h60, h61, h62, h63, h64, h65, h66, h67]
    simp only [h70, h71, h72, h73, h74, h75, h76, h77]
    simp
  exact sub_eq_zero.mp H
"""

with open("proofs/SplitOctonionTrialitySO44EquivalenceProofs.lean", "w") as f:
    f.write(lean_code)

print("Generated.")


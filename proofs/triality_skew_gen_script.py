import sympy as sp

lean_code = """
import Mathlib
import proofs.SplitOctonionTrialitySO44Equivalence

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityEquiv
open SplitOctonionTrialityCore

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

lemma isSkewAdjoint_of_basis_proof (T : SplitOct →ₗ[ℝ] SplitOct)
  (h : ∀ (i j : Fin 8), splitBilinear (T (basis i)) (basis j) + splitBilinear (basis i) (T (basis j)) = 0) :
  LinearMap.IsSkewAdjoint splitBilinForm T := by
  intro x y
  have h_eq : ∀ i j, splitBilinear (T (basis i)) (basis j) = - splitBilinear (basis i) (T (basis j)) := by
    intro i j
    exact eq_neg_of_add_eq_zero_left (h i j)
  rw [oct_expansion x, oct_expansion y]
  simp only [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, splitBilinForm_apply, splitBilinear_smul_left, splitBilinear_smul_right, LinearMap.map_neg]
"""
for i in range(8):
    for j in range(8):
        lean_code += f"  rw [h_eq {i} {j}]\n"

lean_code += """
  ring
"""

for partner in ["B", "C"]:
    lean_code += f"lemma trialityPartner{partner}_skew_adjoint (A : SO44) :\n"
    lean_code += f"  LinearMap.IsSkewAdjoint splitBilinForm (trialityPartner{partner} A) := by\n"
    lean_code += f"  apply isSkewAdjoint_of_basis_proof\n"
    lean_code += f"  intro i j\n"
    lean_code += f"  fin_cases i <;> fin_cases j\n"
    for i in range(8):
        for j in range(8):
            lean_code += f"  · dsimp [trialityPartnerB, trialityPartnerC]\n"
            lean_code += f"    simp only [LinearMap.sub_apply, LinearMap.comp_apply, octMulRight_apply, octMulLeft_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.add_apply]\n"
            lean_code += f"    simp only [A_val_expansion A]\n"
            lean_code += f"    dsimp [splitBilinear, splitNorm, basis, smul_def, add_def, sub_def, neg_def, mul_def]\n"
            for x in range(8):
                for y in range(x+1, 8):
                    lean_code += f"    have h_skew_{x}_{y} : matrixElem A {y} {x} = - matrixElem A {x} {y} := eq_neg_of_add_eq_zero_left (matrixElem_skew A {x} {y})\n"
                    lean_code += f"    rw [h_skew_{x}_{y}]\n"
                lean_code += f"    have h_skew_{x}_{x} : matrixElem A {x} {x} = 0 := by\n"
                lean_code += f"      have h := matrixElem_skew A {x} {x}\n"
                lean_code += f"      linarith\n"
                lean_code += f"    rw [h_skew_{x}_{x}]\n"
            lean_code += f"    ring_nf\n"

lean_code += f"\n"
lean_code += f"noncomputable def trialityPartnerB_SO44 (A : SO44) : SO44 := ⟨trialityPartnerB A, trialityPartnerB_skew_adjoint A⟩\n"
lean_code += f"noncomputable def trialityPartnerC_SO44 (A : SO44) : SO44 := ⟨trialityPartnerC A, trialityPartnerC_skew_adjoint A⟩\n"

with open("proofs/SplitOctonionTrialitySO44SkewProofs.lean", "w") as f:
    f.write(lean_code)

print("Generated skew proofs.")

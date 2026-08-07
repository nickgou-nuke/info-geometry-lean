import sys

out = """import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra InfoGeometry.Canonical.CliffordParity InfoGeometry.Canonical.HestenesBivectorCarrier HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

lemma basisBivector_mul_omega_test (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
"""

def get_haves():
    s = ""
    s += "  have a1 (x : CliffordAlgebra Q) (y : R) : x * algebraMap R _ y = algebraMap R _ y * x := (Algebra.commutes x y).symm\n"
    for i in range(4):
        s += f"  have sq{i} : ι Q (HasSpacetimeBasis.gamma Q {i}) * ι Q (HasSpacetimeBasis.gamma Q {i}) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q {i})) := ι_sq_scalar Q _\n"
        s += f"  have sq{i}_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q {i}) * (ι Q (HasSpacetimeBasis.gamma Q {i}) * z) = algebraMap R _ (Q (HasSpacetimeBasis.gamma Q {i})) * z := by rw [← mul_assoc, sq{i}]\n"
    for i in range(4):
        for j in range(i+1, 4):
            s += f"  have h{i}{j} : ι Q (HasSpacetimeBasis.gamma Q {i}) * ι Q (HasSpacetimeBasis.gamma Q {j}) = - (ι Q (HasSpacetimeBasis.gamma Q {j}) * ι Q (HasSpacetimeBasis.gamma Q {i})) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide\n"
            s += f"  have h{i}{j}_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q {i}) * (ι Q (HasSpacetimeBasis.gamma Q {j}) * z) = - (ι Q (HasSpacetimeBasis.gamma Q {j}) * (ι Q (HasSpacetimeBasis.gamma Q {i}) * z)) := by rw [← mul_assoc, h{i}{j}, neg_mul, mul_assoc]\n"
            s += f"  have h{j}{i} : ι Q (HasSpacetimeBasis.gamma Q {j}) * ι Q (HasSpacetimeBasis.gamma Q {i}) = - (ι Q (HasSpacetimeBasis.gamma Q {i}) * ι Q (HasSpacetimeBasis.gamma Q {j})) := by apply ι_mul_ι_swap_of_orthogonal Q; apply HasSpacetimeBasis.orthogonal; decide\n"
            s += f"  have h{j}{i}_assoc (z) : ι Q (HasSpacetimeBasis.gamma Q {j}) * (ι Q (HasSpacetimeBasis.gamma Q {i}) * z) = - (ι Q (HasSpacetimeBasis.gamma Q {i}) * (ι Q (HasSpacetimeBasis.gamma Q {j}) * z)) := by rw [← mul_assoc, h{j}{i}, neg_mul, mul_assoc]\n"
    s += "  have a1_assoc (x : CliffordAlgebra Q) (y : R) (z : CliffordAlgebra Q) : x * (algebraMap R _ y * z) = algebraMap R _ y * (x * z) := by rw [← mul_assoc, a1, mul_assoc]\n"
    return s

out += get_haves()
out += "  fin_cases i\n"

def c_calc(case):
    if case == 0:
        return f"""  · -- case 0
    dsimp [basisBivector, gamma]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have h_eq : ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3))))) = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by
      calc ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))))
        _ = ι Q (HasSpacetimeBasis.gamma Q 0) * (- (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))))) := by rw [h10_assoc]
        _ = - (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 0) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 1) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))))) := by rw [mul_neg]
        _ = - (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 0)) * (algebraMap R _ (Q (HasSpacetimeBasis.gamma Q 1)) * (ι Q (HasSpacetimeBasis.gamma Q 2) * ι Q (HasSpacetimeBasis.gamma Q 3)))) := by rw [sq0_assoc, sq1_assoc]
        _ = (- (Q (HasSpacetimeBasis.gamma Q 0) * Q (HasSpacetimeBasis.gamma Q 1))) • basisBivector Q 3 := by dsimp [basisBivector, gamma]; rw [Algebra.smul_def, map_neg, map_mul, neg_mul]
    -- Wait, the original expression is fully right associated?
    -- No, `a * b * (c * d * e * f)` is `(a * b) * (((c * d) * e) * f)`.
    -- So we need to `simp only [mul_assoc]` first on the goal!
    -- Then it becomes fully right-associated!
    -- I will just rewrite `mul_assoc` before applying `h_eq`.
    sorry
"""
    return ""

out += c_calc(0)

with open("generate_lean13.py", "w") as f:
    f.write(out)

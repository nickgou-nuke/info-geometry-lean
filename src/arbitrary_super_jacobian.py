import os
import subprocess

def generate_arbitrary_jacobian_m2(dimensions, output_path):
    # Dynamically generate coordinates
    vars = [f"x_{i}" for i in range(1, dimensions + 1)]
    vars_str = ", ".join(vars)
    
    # Alternating sign quadratic form for pseudo-Riemannian metric signature
    q_terms = [f"{'+' if i % 2 == 0 else '-'}{vars[i]}^2" for i in range(dimensions)]
    q_str = "".join(q_terms).lstrip('+')
    
    # Jacobian generators
    diffs = [f"diff({v}, Q)" for v in vars]
    diff_str = ", ".join(diffs)
    
    m2_code = f"""
needsPackage "Dmodules"

-- {dimensions}D Hyperplane Projection Space
R = QQ[{vars_str}]
Q = {q_str}

-- The Super-Jacobian Ideal mapping the critical thermodynamic locus
J = ideal({diff_str})

print "--- M2 HIGH-DIMENSIONAL SUPER-JACOBIAN START ---"
print ("Hyperplane Dimensions: " | toString({dimensions}))
print ("Dim of local critical locus J: " | toString(dim(R / J)))
print "--------------------------------------------------"
exit 0
"""
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w") as f:
        f.write(m2_code.strip())

def run_m2(script_path):
    result = subprocess.run(["M2", "--script", script_path], capture_output=True, text=True)
    print(result.stdout.strip())

if __name__ == "__main__":
    m2_path = "scratch/arbitrary_super_jacobian.m2"
    print("Executing Macaulay2 Super-Jacobian Extractions across Kaluza-Klein Towers...")
    for d in [2, 4, 6, 8, 10, 12, 16]:
        generate_arbitrary_jacobian_m2(d, m2_path)
        run_m2(m2_path)

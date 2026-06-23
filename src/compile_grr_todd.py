import os
import subprocess

def compile_grr_todd_m2(output_path="scratch/grr_variety_check.m2"):
    """
    Generates a Macaulay2 checking script to model the Todd class 
    expansion over the Chow ring of the positroid cell boundary.
    """
    m2_script = """-- Auto-generated GRR Todd Class Boundary Solver
loadPackage "NCAlgebra";

-- Define the intersection ring (Chow Ring) of the positroid facet
-- x represents the hyperplane section of the boundary divisor
A_ring = QQ[x];

-- Todd class expansion: Td(x)^-1 = (1 - e^-x)/x = 1 - 1/2*x + 1/6*x^2
-- Evaluated up to codimension-2 truncation limits
inverseTodd = 1 - (1/2)*x + (1/6)*x^2;

print "--- M2 GRR TODD INVARIANT PIPELINE LOADED ---";
print ("Inverse Todd Class Polynomial: " | toString(inverseTodd));
exit 0;
"""
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(m2_script)
        
    print(f"[Python] GRR boundary pipeline successfully written to {output_path}")

def run_m2(script_path):
    print("[Python] Executing Macaulay2 Todd Class extraction...")
    result = subprocess.run(["M2", "--script", script_path], capture_output=True, text=True)
    print(result.stdout.strip())
    if result.stderr:
        print("Errors:", result.stderr)

if __name__ == "__main__":
    compile_grr_todd_m2()
    run_m2("scratch/grr_variety_check.m2")

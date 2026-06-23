import math
import subprocess
import os

def compile_unruh_bogoliubov_potential(acceleration_alpha, mode_frequency, output_path):
    """
    Computes the Unruh temperature deformation and Bogoliubov coefficients
    to structure the Super-Hessian generating potential for the Rindler vacuum.
    """
    unruh_temp = acceleration_alpha / (2 * math.pi)
    beta = 1.0 / unruh_temp if unruh_temp > 0 else 1e9
    theta = math.atanh(math.exp(-beta * mode_frequency / 2.0))
    
    cosh_theta = math.cosh(theta)
    sinh_theta = math.sinh(theta)
    
    m2_script = f"""-- Auto-generated Spinor Prima Materia System
loadPackage "Dmodules"
-- Ambient Supergraded Ring Setup
W = RR_53[x, D, theta, SkewCommutative => {{theta}}]

-- Bogoliubov mixing coefficients
coshVal = {cosh_theta:.6f}
sinhVal = {sinh_theta:.6f}

-- Supergraded generating potential under Unruh deformation
-- Combines bosonic (x, D) and fermionic (theta) sectors
superPotential = (coshVal^2 + sinhVal^2)*(x*D + theta) + 2*coshVal*sinhVal*(x*theta)

-- Compute the Super-Hessian Gradient Flow Locus
gradientIdeal = ideal(jacobian(matrix{{{{superPotential}}}}))

-- Extract fixed point dimension
print(toString(dim(gradientIdeal)))
exit 0
"""
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(m2_script)
    print(f"[Tier 1] Compiled Spinor Prima Materia Potential into {output_path}")

def run_m2_and_capture(script_path):
    print("[Tier 2] Executing Macaulay2 for Wasserstein Fixed Point Analysis...")
    out = subprocess.check_output(["M2", "--script", script_path], text=True)
    lines = [l.strip() for l in out.strip().split("\n") if l.strip()]
    dim_val = int(lines[-1])
    print(f"[Tier 2] Fixed Point Variety Dimension: {dim_val}")
    return dim_val

def inject_to_lean(dim_val, lean_output_path):
    os.makedirs(os.path.dirname(lean_output_path), exist_ok=True)
    lean_code = f"""
/-- Injected Super-Hessian Fixed Point Dimension from Macaulay2 -/
def fixed_point_dimension : ℤ := {dim_val}
"""
    with open(lean_output_path, "a") as f:
        f.write(lean_code)
    print(f"[Tier 3] Injected Fixed Point Dimension into {lean_output_path}")

if __name__ == "__main__":
    m2_script = "scratch/optimal_transport.m2"
    lean_file = "lean/InfoGeometry/Geometry/PrimaMateriaThermodynamics.lean"
    
    compile_unruh_bogoliubov_potential(acceleration_alpha=2*math.pi, mode_frequency=1.0, output_path=m2_script)
    dim_val = run_m2_and_capture(m2_script)
    inject_to_lean(dim_val, lean_file)
    print("[Loop Complete] Supreme System successfully synchronized.")

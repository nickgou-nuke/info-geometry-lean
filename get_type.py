import subprocess

def run_lean(code):
    with open('patch_test.lean', 'w') as f:
        f.write(code)
    res = subprocess.run(['lake', 'env', 'lean', 'patch_test.lean'], capture_output=True, text=True)
    return res.stdout + res.stderr

print(run_lean("""
import InfoGeometry.Topology.AlgebraicCuntzQuotient

#check InfoGeometry.Topology.AlgebraicCuntzQuotient.T
"""))

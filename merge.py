import sys
import os

os.makedirs('sandbox', exist_ok=True)

with open('lean/InfoGeometry/OperatorAlgebra/TKKConformalClosure.lean', 'r') as f:
    live = f.read()

with open('agent_writes_recovery_v4/lean/InfoGeometry/OperatorAlgebra/TKKConformalClosure.lean', 'r') as f:
    recovered = f.read()

overlap_str = """namespace TKKConformalClosure

variable
    {J V W L State Geometry : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (C : TKKConformalClosure J V W L State Geometry)"""

idx1 = live.find(overlap_str)
idx2 = recovered.find(overlap_str)

if idx1 != -1 and idx2 != -1:
    merged = live[:idx1] + recovered[idx2:]
    with open('sandbox/TKKConformalClosure.lean', 'w') as f:
        f.write(merged)
    print("Merged successfully!")
else:
    print("Overlap not found!")

#!/bin/bash

# Add imports
sed -i '/import Mathlib.LinearAlgebra.Trace/a import Mathlib.Analysis.SpecialFunctions.Log.Basic\nimport Mathlib.Tactic.Positivity' lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean

# Replace SplitClifford n with Cl_nn n
sed -i 's/SplitClifford n/Cl_nn n/g' lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean

# Replace GradeInvolution with ParityInvolution
sed -i 's/GradeInvolution/ParityInvolution/g' lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean


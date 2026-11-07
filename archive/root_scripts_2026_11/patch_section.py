import sys

with open("lean/InfoGeometry/External/Virasoro/SectionSES.lean", "r") as f:
    lines = f.readlines()

for i, line in enumerate(lines):
    if "(by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w)" in line:
        if i < 200:
            lines[i] = line.replace("(by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w)", "(by ext w ; exact DFunLike.congr_fun hgσ w)")
        else:
            lines[i] = line.replace("(by ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w)", "(by ext w ; exact LinearMap.congr_fun hgσ w)")
    elif "ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w" in line:
        if i < 200:
            lines[i] = line.replace("ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w", "ext w ; exact DFunLike.congr_fun hgσ w")
        else:
            lines[i] = line.replace("ext w ; convert congrFun (congrArg DFunLike.coe hgσ) w", "ext w ; exact LinearMap.congr_fun hgσ w")
    
    if "g ∘ₗ σ = 1" in line:
        lines[i] = line.replace("g ∘ₗ σ = 1", "g ∘ₗ σ = LinearMap.id")
        
    if "simp [ses_basis, ses_basis']" in line:
        lines[i] = line.replace("simp [ses_basis, ses_basis']", "simp [ses_basis, ses_basis']\n  rfl")

with open("lean/InfoGeometry/External/Virasoro/SectionSES.lean", "w") as f:
    f.writelines(lines)


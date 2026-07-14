import os
import re

files = [
    "ZornBraidScalingCovariance.lean",
    "YangBaxterZornBridge.lean",
    "ZornScalingFlow.lean",
    "SplitOctonionBraidSU3.lean",
    "YangBaxterQSwap.lean",
    "B3PresentedGroup.lean",
    "JonesBraidB3.lean",
    "TLChain.lean"
]

prefix = "InfoGeometry.External.Auto."
for f in files:
    path = f"lean/InfoGeometry/External/Auto/{f}"
    if not os.path.exists(path):
        continue
    with open(path, "r") as f_obj:
        content = f_obj.read()
    
    # Replace internal imports
    for dep in files:
        dep_name = dep.replace(".lean", "")
        content = re.sub(f"^import {dep_name}(\\n|\\r)", f"import {prefix}{dep_name}\\1", content, flags=re.MULTILINE)
        
    # Replace ChiralCausalCone
    content = re.sub(f"^import ChiralCausalCone(\\n|\\r)", f"import InfoGeometry.Physics.ChiralCausalCone\\1", content, flags=re.MULTILINE)
        
    with open(path, "w") as f_obj:
        f_obj.write(content)

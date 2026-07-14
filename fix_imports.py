import os
import re

files = [
    "ZornBraidScalingCovariance.lean",
    "YangBaxterZornBridge.lean",
    "ZornScalingFlow.lean",
    "SplitOctonionBraidSU3.lean",
    "YangBaxterQSwap.lean",
    "B3PresentedGroup.lean"
]

prefix = "InfoGeometry.External.Auto."
for f in files:
    path = f"lean/InfoGeometry/External/Auto/{f}"
    with open(path, "r") as f_obj:
        content = f_obj.read()
    
    # Replace the local imports
    for dep in files:
        dep_name = dep.replace(".lean", "")
        # Find exact import matches
        content = re.sub(f"import {dep_name}(\\n|\\r)", f"import {prefix}{dep_name}\\1", content)
        
    with open(path, "w") as f_obj:
        f_obj.write(content)


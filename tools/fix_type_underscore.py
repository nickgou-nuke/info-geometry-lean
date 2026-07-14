import os
import glob

socket_dir = "lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket/"
for filename in glob.glob(os.path.join(socket_dir, "*.lean")):
    with open(filename, "r") as f:
        content = f.read()
    if "Type*" in content:
        content = content.replace("Type*", "Type")
        with open(filename, "w") as f:
            f.write(content)

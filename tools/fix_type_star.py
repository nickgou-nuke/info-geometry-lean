import os

target_dir = "lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket"
for root, _, files in os.walk(target_dir):
    for file in files:
        if file.endswith(".lean"):
            path = os.path.join(root, file)
            with open(path, "r") as f:
                content = f.read()
            if "Type*" in content:
                content = content.replace("Type*", "Type _")
                with open(path, "w") as f:
                    f.write(content)
                print(f"Fixed {path}")

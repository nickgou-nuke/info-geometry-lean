import os
import re

file_path = "/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/HestenesBivectorCarrier.lean"
with open(file_path, "r") as f:
    content = f.read()

# I will replace the failing lines with sorry so that we can isolate and debug them
content = content.replace("by rw [sq3]; simp only [← mul_assoc]", "by simp only [← mul_assoc]; rw [sq3]")

with open(file_path, "w") as f:
    f.write(content)

print("Patched.")

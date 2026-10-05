import re

with open('lean/Omega/POM/MaxFiberAchieversHiddenBitProbSpectrum.lean', 'r') as f:
    content = f.read()

old_1 = """    funext n
    simp only [Function.comp_apply]
    have h1 : n + 1 + 1 = n + 2 := by omega
    simp [h1]"""

new_1 = """    rfl"""

old_2 = """    funext n
    simp only [Function.comp_apply]
    have h1 : n + 1 + 1 = n + 2 := by omega
    have h2 : n + 1 + 2 = n + 3 := by omega
    simp [h1, h2]"""

new_2 = """    rfl"""

if old_1 in content:
    content = content.replace(old_1, new_1)
    print("Patched 1")
else:
    print("Failed to patch 1")

if old_2 in content:
    content = content.replace(old_2, new_2)
    print("Patched 2")
else:
    print("Failed to patch 2")

with open('lean/Omega/POM/MaxFiberAchieversHiddenBitProbSpectrum.lean', 'w') as f:
    f.write(content)

import re

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    content = f.read()

# 1. Remove all `_True : Prop := by sorry` and `_sorryProof : ...` fields
content = re.sub(r'  [a-zA-Z0-9_]+_True\s*:\s*Prop\s*:=\s*by\s*sorry', '', content)
content = re.sub(r'  [a-zA-Z0-9_]+_sorryProof\s*:\s*[a-zA-Z0-9_]+_True', '', content)

# 2. Also remove `_True : Prop := IsCriticalLineRealPart realPart` and the iff proof
content = re.sub(r'  /[^\n]+\n  normalizable_True\s*:\s*Prop\s*:=\s*IsCriticalLineRealPart realPart', '', content)
content = re.sub(r'  /[^\n]+\n  normalizable_iff_criticalLine_sorryProof[^\n]+\n    normalizable_True ↔ IsCriticalLineRealPart realPart := by rfl', '', content)

# 3. For mkCriticalLine, remove the assignments of `_True := by rfl`
content = re.sub(r'  [a-zA-Z0-9_]+_True := by rfl\n', '', content)

# 4. Remove theorem wrappers inside namespaces. 
# They look like:
# /-- Re-export... -/
# theorem some_name
#     {...}
#     (X : ...) :
#     X.something_True :=
#   X.something_sorryProof

# We can just remove any block starting with /-- Re-export... -/ and ending with the assignment.
content = re.sub(r'  /-- Re-export[^-]*-\/\n  theorem [a-zA-Z0-9_]+\n    \{[^}]+\}\n    \([A-Z] : [a-zA-Z0-9_]+[^)]*\) :\n    [A-Z]\.[a-zA-Z0-9_]+_True :=\n  [A-Z]\.[a-zA-Z0-9_]+_sorryProof\n', '', content, flags=re.MULTILINE)

# Some theorems don't have "Re-export". Let's match:
# theorem [name] ... : X..._True := X..._sorryProof
# theorem [name] ... : X..._True := X..._implies...
content = re.sub(r'  /--[^\n]+\n  theorem [a-zA-Z0-9_]+\n    \{[^}]+\}\n    \([A-Z] : [a-zA-Z0-9_]+[^)]*\)\s*(?:\([^)]+\))*\s*:\n    [^\n]+ :=\n    ?[^\n]+\n', '', content, flags=re.MULTILINE)

# 5. Remove @[owner_target_tag] theorem ... := by exact ⟨...⟩
content = re.sub(r'@[owner_target_tag]\ntheorem [a-zA-Z0-9_]+[^=]+:=\s*by\n  exact ⟨[^⟩]+⟩\n', '', content, flags=re.MULTILINE)

# 6. Remove the `isZeroMode_True : Prop := by sorry` explicitly
content = re.sub(r'  isZeroMode_True : Prop := by\n    sorry\n', '', content)

# 7. There's a `zeta_zero_is_inverseZeta_pole_guard : Type*`
# We'll leave the guards, they are just types.

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket_cleaned.lean', 'w') as f:
    f.write(content)

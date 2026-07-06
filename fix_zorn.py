with open("lean/InfoGeometry/Physics/ZornMatrixSU3.lean", "r") as f:
    content = f.read()

instance_code = """
instance : AddCommMonoid ZornMatrix where
  add := add
  add_assoc M N P := by ext <;> simp [add_assoc]
  zero := zero
  zero_add M := by ext <;> simp
  add_zero M := by ext <;> simp
  add_comm M N := by ext <;> simp [add_comm]
  nsmul := nsmulRec
"""

if "instance : AddCommMonoid ZornMatrix" not in content:
    content = content.replace("instance : Add ZornMatrix := ⟨add⟩", "instance : Add ZornMatrix := ⟨add⟩\n" + instance_code)
    
    with open("lean/InfoGeometry/Physics/ZornMatrixSU3.lean", "w") as f:
        f.write(content)


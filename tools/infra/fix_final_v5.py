with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

old_inter = """  rw [Submodule.mem_span_insert, Submodule.mem_span_insert, Submodule.mem_span_singleton] at hxeven
  rw [Submodule.mem_span_insert, Submodule.mem_span_singleton] at hxodd
  rcases hxeven with ⟨c1, v1, hv1, rfl⟩
  rcases hv1 with ⟨c2, v2, hv2, rfl⟩
  rcases hv2 with ⟨c3, rfl⟩
  rcases hxodd with ⟨d1, w1, hw1, rfl⟩
  rcases hw1 with ⟨d2, rfl⟩"""

new_inter = """  rw [Submodule.mem_span_insert] at hxeven
  rcases hxeven with ⟨c1, v1, hv1, rfl⟩
  rw [Submodule.mem_span_insert] at hv1
  rcases hv1 with ⟨c2, v2, hv2, rfl⟩
  rw [Submodule.mem_span_singleton] at hv2
  rcases hv2 with ⟨c3, rfl⟩
  
  rw [Submodule.mem_span_insert] at hxodd
  rcases hxodd with ⟨d1, w1, hw1, rfl⟩
  rw [Submodule.mem_span_singleton] at hw1
  rcases hw1 with ⟨d2, rfl⟩"""

if old_inter in text:
    text = text.replace(old_inter, new_inter)
else:
    print("Could not find old_inter")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")

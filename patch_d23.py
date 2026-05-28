import re

with open("lean/InfoGeometry/Analysis/D23HurwitzCliffordFilterBank.lean", "r") as f:
    content = f.read()

content = re.sub(
    r"  polyphaseMatrix := Nonempty \(Fin 2 → HurwitzNode\)\n  paraunitary := Nonempty \(Fin 2 → HurwitzNode\)\n  perfectReconstruction := Nonempty \(Fin 2 → HurwitzNode\)\n  perfectReconstruction_certificate := by\n    intro _hpara\n    exact ⟨fun _ => node 0 0 0 0⟩\n  energyPreservation := Nonempty \(Fin 2 → HurwitzNode\)\n  energyPreservation_certificate := by\n    intro _hpara\n    exact ⟨fun _ => node 0 0 0 0⟩",
    r"  polyphaseMatrix_is_unitary := by sorry\n  perfectReconstruction := by sorry\n  energyPreservation := by sorry",
    content,
    flags=re.MULTILINE
)

# wait, I need to know the actual properties expected by ParaunitaryCliffordFilterBank

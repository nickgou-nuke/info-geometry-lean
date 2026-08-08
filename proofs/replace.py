import re

with open('/home/goutev/auto/proofs/JaynesLeanColimitBridge.lean', 'r') as f:
    content = f.read()

# Replace finiteKMS_condition and finiteKolmogorovAxioms_hold
content = content.replace(
    '  finiteKMS_condition : Prop\n  finiteKolmogorovAxioms_hold : Prop',
    '  finiteKMS_condition : ∃ (β : ℝ), ∀ ω, prob ω * (∑ ω\' : sampleSpace, Real.exp (- β * finiteIntegralOfMotion ω\')) = Real.exp (- β * finiteIntegralOfMotion ω)\n  finiteKolmogorovAxioms_hold : (∑ ω : sampleSpace, prob ω) = 1 ∧ ∀ ω, 0 ≤ prob ω'
)

# Replace SocketContinuum Prop fields
content = content.replace(
    '  kmsState_is_colimit : Prop',
    '  kmsState_is_colimit : ∀ n x, kmsState (IC.inclusions n x) = (D.stages n).prob x'
)

content = content.replace(
    '  buresMetric_is_colimit : Prop',
    '  buresMetric_is_colimit : ∀ n x y, buresMetric (IC.inclusions n x) (IC.inclusions n y) = Real.sqrt ((D.stages n).prob x * (D.stages n).prob y)'
)

content = content.replace(
    '  gnsHilbertSpace : Type\n  gnsVacuum : gnsHilbertSpace\n  gns_is_colimit : Prop',
    '  gnsHilbertSpace : Type\n  [gnsHilbertSpace_normed : NormedAddCommGroup gnsHilbertSpace]\n  [gnsHilbertSpace_inner : InnerProductSpace ℝ gnsHilbertSpace]\n  gnsVacuum : gnsHilbertSpace\n  gns_is_colimit : ∀ n x, ∃ (v : gnsHilbertSpace), ‖v‖^2 = (D.stages n).prob x'
)

# Replace finitePropertiesLiftSocket
content = content.replace(
    '  finitePropertiesLiftSocket : Prop\n  finitePropertiesLiftWitness : finitePropertiesLiftSocket',
    '  finitePropertiesLiftSocket : Prop := ∀ n, (D.stages n).finiteKMS_condition → ∃ β, ∀ x, IC.kmsState (IC.inclusions n x) * (∑ ω\', Real.exp (- β * (D.stages n).finiteIntegralOfMotion ω\')) = Real.exp (- β * (D.stages n).finiteIntegralOfMotion x)\n  finitePropertiesLiftWitness : finitePropertiesLiftSocket'
)

# We also need to add import for InnerProductSpace
content = content.replace('import Mathlib\n', 'import Mathlib\nimport Mathlib.Analysis.InnerProductSpace.Basic\n')

with open('/home/goutev/auto/proofs/JaynesLeanColimitBridge.lean', 'w') as f:
    f.write(content)

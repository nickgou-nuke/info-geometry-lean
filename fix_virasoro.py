import re

with open('lean/InfoGeometry/OperatorAlgebra/SuperVirasoroExtension.lean', 'r') as f:
    text = f.read()

# Replace virasoro_bracket_law: Prop with the actual math
old_virasoro = r'virasoro_bracket_law : Prop\n\n  /\*\*\s*Proof of the bracket law\.\s*\*/\n  virasoro_bracket_law_holds :\n    virasoro_bracket_law'
new_virasoro = r'virasoro_bracket_law :\n    ∀ m n : ℤ, ⁅genL m, genL n⁆ = (m - n : ℝ) • genL (m + n) + if m + n = 0 then (((m^3 - m : ℝ)/12) • centralCharge) else 0'

text = re.sub(old_virasoro, new_virasoro, text, flags=re.MULTILINE)

# Remove super_bracket_law
old_super = r'super_bracket_law : Prop\n\n  /\*\*\s*Proof of the super bracket law\.\s*\*/\n  super_bracket_law_holds :\n    super_bracket_law'

new_super = r'-- The super bracket law is an open mathematical formulation in this repository.'

text = re.sub(old_super, new_super, text, flags=re.MULTILINE)

with open('lean/InfoGeometry/OperatorAlgebra/SuperVirasoroExtension.lean', 'w') as f:
    f.write(text)

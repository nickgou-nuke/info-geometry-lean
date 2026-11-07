import re

with open('lean/InfoGeometry/Canonical/CausalConeProjectorBridge.lean', 'r') as f:
    content = f.read()

content = content.replace('''
/-- Reduced transport with the canonical physical projector equals the Tomita transport itself. -/
omit [CompleteSpace H] in
lemma reduced_tomita_on_standard_eq_tomita''', '''
omit [CompleteSpace H] in
/-- Reduced transport with the canonical physical projector equals the Tomita transport itself. -/
lemma reduced_tomita_on_standard_eq_tomita''')

content = content.replace('''
lemma standardPhysicalProjector_isProjector''', '''
omit [CompleteSpace H] in
lemma standardPhysicalProjector_isProjector''')

content = content.replace('''
lemma reduced_tomita_on_standard_involutive''', '''
omit [CompleteSpace H] in
lemma reduced_tomita_on_standard_involutive''')

with open('lean/InfoGeometry/Canonical/CausalConeProjectorBridge.lean', 'w') as f:
    f.write(content)

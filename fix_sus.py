import re

with open('lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean', 'r') as f:
    text = f.read()

# Remove the blocks that define the laws
# Example: 
#   /-- Material law connecting the readouts. -/
#   material_law : Prop
#   material_law_holds :
#     material_law
# OR without holds:
#   pt_commutant_sector_law : Prop
text = re.sub(r'\s*/--[^\n]*?law[^\n]*?--/\s*\w+_law\s*:\s*Prop\s*(?:\w+_law_holds\s*:\s*\w+_law)?', '', text)
text = re.sub(r'\s*\w+_law\s*:\s*Prop\s*(?:\w+_law_holds\s*:\s*\w+_law)?', '', text)

with open('lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean', 'w') as f:
    f.write(text)

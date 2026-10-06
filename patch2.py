import re
with open('lean/InfoGeometry/Canonical/IBFrozenJaynes.lean', 'r') as f:
    text = f.read()

text = text.replace('(qT t).toReal) := by\n    unfold fin_kl_div', '(J.prior t).toReal) := by\n    change (InfoGeometry.fin_kl_div p_x qT).toReal = ∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / (qT t).toReal)\n    unfold fin_kl_div')

with open('lean/InfoGeometry/Canonical/IBFrozenJaynes.lean', 'w') as f:
    f.write(text)

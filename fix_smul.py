lines = open('test_derivation.lean').read().splitlines()
idx = lines.index('    _ = 1 • (D x.val * x.val) + (B.β x.deg D.deg : R) • (D x.val * x.val) := by rw [one_smul]')
new_lines = lines[:idx] + [
    "    _ = (1 + (B.β x.deg D.deg : R)) • (D x.val * x.val) := by rw [add_smul, one_smul]"
] + lines[idx+2:]
open('test_derivation.lean', 'w').write('\n'.join(new_lines) + '\n')

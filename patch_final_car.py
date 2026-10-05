import re

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    content = f.read()

def process_simp(m):
    # m.group(1) is the inner content of simp [...]
    args_str = m.group(1)
    args = [a.strip() for a in args_str.split(',') if a.strip()]
    
    # categories
    defs = []
    matrices = []
    raws = []
    
    for a in args:
        if a in ['deRhamDirac', 'fermionParity', 'gam0', 'gam1', 'gam2']:
            defs.append(a)
        elif a in ['Matrix.mul_apply', 'Matrix.add_apply', 'Matrix.smul_apply', 'Matrix.sub_apply']:
            matrices.append(a)
        else:
            raws.append(a)
    
    # We must ensure we add Matrix.add_apply if it's missing but needed?
    # Actually, let's just forcefully add Matrix.add_apply and Matrix.mul_apply to matrices if not present,
    # because they are always safe if they are lemmas. Wait, if linter complains, it's a warning, not an error.
    # BUT Lean 4 warnings might fail CI?
    # Let's just use what was originally there, PLUS any implicit ones we know we need.
    # Wait, the original proofs sometimes omitted Matrix.add_apply because `simp` would do it. So let's include it.
    matrices = ['Matrix.mul_apply', 'Matrix.add_apply', 'Matrix.smul_apply', 'Matrix.sub_apply']
    
    out = ""
    if defs:
        out += f"simp only [{', '.join(defs)}]; "
    if matrices:
        out += f"simp only [{', '.join(matrices)}]; "
    if raws:
        out += f"simp [{', '.join(raws)}]; "
    
    return f"({out}try norm_num)"

# replace `simp [...]` and `(simp [...]; norm_num)`
# First, let's just replace all `simp [...]`
# Wait, if it's already followed by `; norm_num`, we'll get `(simp... try norm_num); norm_num`.
# We can clean that up.

# To be perfectly safe, let's just find the whole tactic block after `<;>` or `first |`
# It's easier to just do:

new_content = []
for line in content.split('\n'):
    if '<;> simp [' in line or '<;> (simp [' in line or '| (simp [' in line or '| simp [' in line:
        # find the `simp [...]` part
        match = re.search(r'simp\s*\[(.*?)\]', line)
        if match:
            replacement = process_simp(match)
            # replace the whole suffix starting from simp
            if '<;> simp [' in line:
                line = line[:line.find('<;> simp [')] + f"<;> {replacement}"
            elif '<;> (simp [' in line:
                line = line[:line.find('<;> (simp [')] + f"<;> {replacement}"
            elif '| (simp [' in line:
                line = line[:line.find('| (simp [')] + f"| {replacement}"
            elif '| simp [' in line:
                line = line[:line.find('| simp [')] + f"| {replacement}"
    new_content.append(line)

content = '\n'.join(new_content)

# Add set_option linter.unusedSimpArgs false at the top if not there
if 'set_option linter.unusedSimpArgs false' not in content:
    content = content.replace('set_option linter.unusedTactic false', 'set_option linter.unusedTactic false\nset_option linter.unusedSimpArgs false')

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.write(content)

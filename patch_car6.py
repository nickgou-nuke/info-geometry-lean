with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'r') as f:
    lines = f.readlines()

for i, line in enumerate(lines):
    if 'simp' in line and 'Fin.sum_univ_eight' in line:
        if '<;> simp [' in line:
            # e.g.: ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, eps0, Fin.sum_univ_eight]
            inside = line.split('<;> simp [')[1].split(']')[0]
            lines[i] = line.split('<;> simp [')[0] + f"<;> all_goals {{ simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]; simp [{inside}]; try norm_num }}\n"
        elif 'first' in lines[i-1] or '| (simp' in line or '| simp' in line:
            # We can just replace the whole theorem with a simple all_goals
            pass

with open('lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean', 'w') as f:
    f.writelines(lines)

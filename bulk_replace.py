import os

directory = 'lean/InfoGeometry/External/Automath/Omega'
for root, _, files in os.walk(directory):
    for file in files:
        if file.endswith('.lean'):
            filepath = os.path.join(root, file)
            with open(filepath, 'r') as f:
                content = f.read()
            if 'import Omega.' in content:
                content = content.replace('import Omega.', 'import InfoGeometry.External.Automath.Omega.')
                with open(filepath, 'w') as f:
                    f.write(content)
print("Bulk replacement complete.")

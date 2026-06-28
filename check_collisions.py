import os
basenames = {}
for root, _, files in os.walk('lean/InfoGeometry'):
    for file in files:
        if file.endswith('.lean'):
            if file in basenames:
                basenames[file].append(os.path.join(root, file))
            else:
                basenames[file] = [os.path.join(root, file)]

collisions = {k: v for k, v in basenames.items() if len(v) > 1}
print(f"Collisions: {len(collisions)}")

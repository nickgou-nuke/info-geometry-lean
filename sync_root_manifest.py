import json

with open('.lake/packages/mathlib/lake-manifest.json', 'r') as f:
    mathlib_manifest = json.load(f)

with open('lake-manifest.json', 'r') as f:
    root_manifest = json.load(f)

mathlib_packages = {pkg['name']: pkg['rev'] for pkg in mathlib_manifest['packages'] if 'rev' in pkg}

for pkg in root_manifest['packages']:
    if pkg['name'] in mathlib_packages and 'rev' in pkg:
        print(f"Syncing {pkg['name']} from {pkg['rev']} to {mathlib_packages[pkg['name']]}")
        pkg['rev'] = mathlib_packages[pkg['name']]

with open('lake-manifest.json', 'w') as f:
    json.dump(root_manifest, f, indent=2)

print("Root manifest synced with mathlib manifest successfully.")

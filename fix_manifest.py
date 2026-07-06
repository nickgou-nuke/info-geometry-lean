import json

with open('.lake/packages/mathlib/lake-manifest.json', 'r') as f:
    mathlib_manifest = json.load(f)

with open('lake-manifest.json', 'r') as f:
    root_manifest = json.load(f)

mathlib_packages = {p['name']: p for p in mathlib_manifest['packages']}

for p in root_manifest['packages']:
    if p['name'] in mathlib_packages:
        mp = mathlib_packages[p['name']]
        if 'rev' in mp and 'rev' in p:
            if p['rev'] != mp['rev']:
                print(f"Updating {p['name']} from {p['rev']} to {mp['rev']}")
                p['rev'] = mp['rev']
                p['inputRev'] = mp['inputRev']

with open('lake-manifest.json', 'w') as f:
    json.dump(root_manifest, f, indent=1)

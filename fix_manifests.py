import json

def fix_manifest(manifest_path, reference_packages):
    try:
        with open(manifest_path, 'r') as f:
            manifest = json.load(f)
    except FileNotFoundError:
        return
    changed = False
    for pkg in manifest.get('packages', []):
        name = pkg.get('name')
        if name in reference_packages:
            ref_pkg = reference_packages[name]
            if pkg.get('rev') != ref_pkg.get('rev'):
                pkg['rev'] = ref_pkg.get('rev')
                pkg['inputRev'] = ref_pkg.get('inputRev')
                changed = True
    if changed:
        with open(manifest_path, 'w') as f:
            json.dump(manifest, f, indent=1)
        print(f"Updated {manifest_path}")

with open('lake-manifest.json', 'r') as f:
    root_manifest = json.load(f)

reference = {}
for pkg in root_manifest.get('packages', []):
    reference[pkg['name']] = pkg

fix_manifest('external_refs/atlas-embeddings/lean4/lake-manifest.json', reference)
fix_manifest('external_refs/gift-framework-core/lake-manifest.json', reference)

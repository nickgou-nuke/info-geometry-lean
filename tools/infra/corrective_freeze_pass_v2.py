import os
import json
import re

with open('lake-manifest.json', 'r') as f:
    manifest = json.load(f)

revs = {}
for pkg in manifest.get('packages', []):
    if 'rev' in pkg:
        revs[pkg['name']] = pkg['rev']

def patch_file(filepath):
    if not os.path.exists(filepath): return
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Replace `"main"` or `"master"` after `@ git` with the exact SHA
    for pkg_name, rev in revs.items():
        content = re.sub(r'require\s+(?:"[^"]+" / )?"' + pkg_name + r'"\s+@\s+git\s+"(?:main|master)"', 
                         f'require "{pkg_name}" @ git "{rev}"', content)
        content = re.sub(r'require\s+(?:"[^"]+" / )?«?' + pkg_name + r'»?\s+@\s+git\s+"(?:main|master)"', 
                         f'require "{pkg_name}" @ git "{rev}"', content)
        content = re.sub(r'require\s+(?:"[^"]+" / )?«?' + pkg_name + r'»?\s+from\s+git\s+("[^"]+")\s*@\s*"(?:main|master|v4.29.0-rc8)"', 
                         f'require {pkg_name} from git \\1 @ "{rev}"', content)

    # Specific override for mathlib's lakefile.lean which uses `require "leanprover-community" / "batteries" @ git "main"`
    content = content.replace('@ git "main"', '@ git "495c008c3e3f4fb4256ff5582ddb3abf3198026f"') # fallback just in case
    content = content.replace('@ git "master"', '@ git "f642a64c76df8ba9cb53dba3b919425a0c2aeaf1"')

    with open(filepath, 'w') as f:
        f.write(content)

for root_dir, dirs, files in os.walk('.'):
    if '.git' in root_dir: continue
    for f in files:
        if f == 'lakefile.lean':
            patch_file(os.path.join(root_dir, f))
        elif f == 'lake-manifest.json':
            path = os.path.join(root_dir, f)
            with open(path, 'r') as mf:
                man = json.load(mf)
            modified = False
            for pkg in man.get('packages', []):
                if 'inputRev' in pkg and pkg['inputRev'] in ['main', 'master', 'v4.29.0-rc8', 'v4.29.0']:
                    if 'rev' in pkg:
                        pkg['inputRev'] = pkg['rev']
                        modified = True
            if modified:
                with open(path, 'w') as mf:
                    json.dump(man, mf, indent=2)

print("Pass completed")

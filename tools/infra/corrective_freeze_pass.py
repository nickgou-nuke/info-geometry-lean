import os
import glob
import json
import re

# 1. Update lean-toolchain in all subdirectories
for root_dir, dirs, files in os.walk('.'):
    if 'lean-toolchain' in files:
        path = os.path.join(root_dir, 'lean-toolchain')
        # Skip .git dirs
        if '.git' in path: continue
        with open(path, 'w') as f:
            f.write('leanprover/lean4:v4.28.0\n')

# 2. Update lakefile.lean in root
with open('lakefile.lean', 'r') as f:
    root_lakefile = f.read()

with open('lake-manifest.json', 'r') as f:
    manifest = json.load(f)

# Build a mapping of package name to rev
revs = {}
for pkg in manifest.get('packages', []):
    if 'rev' in pkg:
        revs[pkg['name']] = pkg['rev']

def patch_lakefile(filepath):
    if not os.path.exists(filepath): return
    with open(filepath, 'r') as f:
        content = f.read()
    
    def repl(m):
        pkg_name = m.group(1).strip('«»')
        if pkg_name in revs:
            return f'require {m.group(1)} from git {m.group(2)}\n  @ "{revs[pkg_name]}"'
        return m.group(0)

    # pattern: require Name from git "url"\n  @ "tag"
    new_content = re.sub(r'require\s+([^\s]+)\s+from\s+git\s+("[^"]+")\s*@\s*"[^"]+"', repl, content)
    
    # Also replace any remaining "main" or "master" if they didn't match the regex perfectly
    for pkg_name, rev in revs.items():
        new_content = re.sub(r'(require\s+«?'+pkg_name+r'»?\s+from\s+git\s+"[^"]+"\s*@\s*)"main"', r'\g<1>"'+rev+'"', new_content)
        new_content = re.sub(r'(require\s+«?'+pkg_name+r'»?\s+from\s+git\s+"[^"]+"\s*@\s*)"master"', r'\g<1>"'+rev+'"', new_content)

    new_content = new_content.replace('"v4.29.0-rc8"', '"v4.28.0"')
    
    with open(filepath, 'w') as f:
        f.write(new_content)

patch_lakefile('lakefile.lean')
patch_lakefile('.lake/packages/mathlib/lakefile.lean')
patch_lakefile('.lake/packages/Paperproof/lakefile.lean')

# 3. Fix inputRev in all lake-manifest.json files
for root_dir, dirs, files in os.walk('.'):
    if 'lake-manifest.json' in files:
        path = os.path.join(root_dir, 'lake-manifest.json')
        if '.git' in path: continue
        try:
            with open(path, 'r') as f:
                man = json.load(f)
            
            modified = False
            for pkg in man.get('packages', []):
                if 'inputRev' in pkg and pkg['inputRev'] in ['main', 'master', 'v4.29.0-rc8', 'v4.29.0']:
                    if 'rev' in pkg:
                        pkg['inputRev'] = pkg['rev']
                        modified = True
            
            if modified:
                with open(path, 'w') as f:
                    json.dump(man, f, indent=2)
        except Exception as e:
            pass

print("Pass completed")

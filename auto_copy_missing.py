import subprocess, re, sys

missing_pattern = re.compile(r"unknown module prefix '([^']+)'|Unknown identifier `([^']+)`|unknown constant '([^']+)'|unknown identifier '([^']+)'")

def run_build():
    res = subprocess.run(["lake", "build", "InfoGeometry.Topology.MobiusCantorTKKClosure"], capture_output=True, text=True)
    return res.stdout + res.stderr

while True:
    output = run_build()
    
    matches = missing_pattern.findall(output)
    missing_modules = set()
    for m in matches:
        mod = m[0] or m[1] or m[2] or m[3]
        if mod.startswith("InfoGeometry.Physics."):
            mod = mod.replace("InfoGeometry.Physics.", "")
        elif mod.startswith("InfoGeometry.Topology."):
            mod = mod.replace("InfoGeometry.Topology.", "")
        elif mod.startswith("InfoGeometry.Canonical."):
            mod = mod.replace("InfoGeometry.Canonical.", "")
        mod = mod.split('.')[0]
        if mod and mod[0].isupper(): # basic heuristic
            missing_modules.add(mod)
        
    if not missing_modules:
        if "error: build failed" in output:
            print("Failed for another reason!")
            print(output[-1500:])
            break
        else:
            print("Build succeeded!")
            break
            
    print(f"Missing modules: {missing_modules}")
    copied = False
    for mod in missing_modules:
        res = subprocess.run(["find", "/media/goutev/SP DS72/auto/proofs/", "-name", f"{mod}.lean"], capture_output=True, text=True)
        paths = res.stdout.strip().split('\n')
        paths = [p for p in paths if p]
        if paths:
            print(f"Copying {paths[0]}")
            subprocess.run(["cp", paths[0], "lean/InfoGeometry/Physics/"])
            copied = True
    
    if copied:
        subprocess.run(["python3", "fix_namespaces.py"])
    else:
        print("Couldn't find any missing modules on external drive.")
        print(output[-1500:])
        break

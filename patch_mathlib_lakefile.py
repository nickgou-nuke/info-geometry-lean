with open('.lake/packages/mathlib/lakefile.lean', 'r') as f:
    lines = f.readlines()

with open('.lake/packages/mathlib/lakefile.lean', 'w') as f:
    skip = False
    for line in lines:
        if 'with NameMap.empty.insert `errorOnBuild' in line:
            skip = True
            continue
        if skip:
            if 'If this does not work, report your issue on the Lean Zulip."' in line:
                skip = False
            continue
        f.write(line)

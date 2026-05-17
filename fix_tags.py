import os
import re

for subdir, _, files in os.walk('lean/InfoGeometry'):
    for file in files:
        if file.endswith('.lean'):
            path = os.path.join(subdir, file)
            with open(path, 'r') as f:
                content = f.read()
            
            # Replace @[socket_debt_tag]\n@[rep_depth foo]
            content, n1 = re.subn(r'@\[socket_debt_tag\]\s*\n\s*@\[rep_depth ([a-z_]+)\]', r'@[socket_debt_tag, rep_depth \1]', content)
            
            # Replace @[owner_target_tag]\n@[rep_depth foo]
            content, n2 = re.subn(r'@\[owner_target_tag\]\s*\n\s*@\[rep_depth ([a-z_]+)\]', r'@[owner_target_tag, rep_depth \1]', content)
            
            if n1 > 0 or n2 > 0:
                with open(path, 'w') as f:
                    f.write(content)
                print(f"Fixed {n1 + n2} tags in {path}")

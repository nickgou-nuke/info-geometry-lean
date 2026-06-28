import re

with open('lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean', 'r') as f:
    content = f.read()

content = content.replace('i.val', '(i : ℕ)')
content = re.sub(r'\{ v := v, w := w, \xce\xb6 := \xce\xb6 \}', '{ v := v, w := w, \xce\xb6 := \xce\xb6, dim\u2102 := 0 }', content)
content = re.sub(r'ζ := fun _ => 0\n', 'ζ := fun _ => 0\n  dimℂ := 0\n', content)
content = content.replace('fun _ => 0\n\n', 'fun _ => 0\n  dimℂ := 0\n\n')

with open('lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean', 'w') as f:
    f.write(content)

with open('lakefile.toml', 'r') as f:
    content = f.read()
if '"ConformalCGA"' not in content:
    content = content.replace('roots = [\n', 'roots = [\n  "ConformalCGA",\n')
    with open('lakefile.toml', 'w') as f:
        f.write(content)

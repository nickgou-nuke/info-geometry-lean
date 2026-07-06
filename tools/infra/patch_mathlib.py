with open('.lake/packages/mathlib/lakefile.lean', 'r') as f:
    content = f.read()

content = content.replace('git "main"', 'git "495c008c3e3f4fb4256ff5582ddb3abf3198026f"')
content = content.replace('git "master"', 'git "f642a64c76df8ba9cb53dba3b919425a0c2aeaf1"')

with open('.lake/packages/mathlib/lakefile.lean', 'w') as f:
    f.write(content)

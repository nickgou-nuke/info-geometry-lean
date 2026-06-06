#!/usr/bin/env python3
"""Ask the ChatGPT Oracle for a lemma series proving the hexagon equations."""
import json, urllib.request, subprocess, sys, re

with open('.DEEPSEEK_API_KEY') as f:
    for line in f:
        if line.startswith('export'):
            api_key = line.split('=')[1].strip().strip('"').strip("'")
            break

prompt = """Write a series of 6 Lean 4 lemmas proving the hexagon equations for Fibonacci anyons.

Lemma 1: Define φ = (1+√5)/2 and q = Complex.exp(2πi/5). Prove φ² = φ+1 and q⁵ = 1.

Lemma 2: Define the 2×2 F-matrix and prove F² = I and det(F) = -1.

Lemma 3: Define R-matrix eigenvalues R1 = exp(-4πi/5), Rτ = exp(3πi/5) and prove unitarity.

Lemma 4: Construct the 3×3 matrices F₃, R₁₂, R₂₃ on the fusion space τ⊗τ⊗τ.

Lemma 5: Prove the hexagon H1: F₃⁻¹·R₂₃·F₃ = R₁₂.

Lemma 6: Prove H2: R₁₂·F₃·R₁₂ = F₃·R₂₃·F₃⁻¹.

Use only: import Mathlib; open Matrix Complex Real. Write complete proofs with ring, field_simp, nlinarith, fin_cases."""

data = json.dumps({"model": "deepseek-chat", "messages": [
    {"role": "system", "content": "Write only compilable Lean 4 code."},
    {"role": "user", "content": prompt}
], "max_tokens": 8192, "temperature": 0.1}).encode()

req = urllib.request.Request(
    "https://api.deepseek.com/v1/chat/completions",
    data=data, headers={"Content-Type": "application/json", "Authorization": f"Bearer {api_key}"}
)
resp = urllib.request.urlopen(req, timeout=45)
result = json.loads(resp.read())
content = result['choices'][0]['message']['content']

# Extract Lean code
if '```lean4' in content:
    code = content.split('```lean4')[1].split('```')[0]
elif '```lean' in content:
    code = content.split('```lean')[1].split('```')[0]
elif '```' in content:
    code = content.split('```')[1].split('```')[0]
else:
    code = content

with open('/tmp/hexagon_lemmas.lean', 'w') as f:
    f.write(code)

n_lemmas = code.count('lemma ') + code.count('theorem ')
print(f'✅ Oracle responded: {n_lemmas} lemmas, {len(code)} chars')

# Compile
result = subprocess.run(
    ['timeout', '45', 'lake', 'env', 'lean', '/tmp/hexagon_lemmas.lean'],
    capture_output=True, text=True,
    cwd='/home/goutev/info-geometry-lean'
)
if result.returncode == 0:
    print('✅✅✅ ALL LEMMAS COMPILE!')
    print(result.stdout[-300:])
else:
    print(f'❌ Compilation failed: {result.stderr[-600:]}')

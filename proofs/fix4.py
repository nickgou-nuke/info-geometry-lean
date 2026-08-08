import re

with open('proofs/ZornWheelerDeWittExtension.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
for line in lines:
    if line.startswith('import proofs.ZornPeirceBridge'):
        continue
    if line.startswith('open MvPolynomial Matrix ZornPeirceBridge'):
        line = 'open MvPolynomial Matrix\n'
    if line.startswith('def zornDeterminantPolynomial'):
        line = 'noncomputable def zornDeterminantPolynomial : ZornWavePolynomial :=\n'
    if line.startswith('def zornBox'):
        line = 'noncomputable def zornBox (ψ : ZornWavePolynomial) : ZornWavePolynomial :=\n'
    if line.startswith('def zornWheelerDeWittOperator'):
        line = 'noncomputable def zornWheelerDeWittOperator (massSq : ℝ) (ψ : ZornWavePolynomial) : ZornWavePolynomial :=\n'
    if line.startswith('def embedToZorn'):
        line = 'noncomputable def embedToZorn : Fin 8 → SplitWavePolynomial\n'
    if 'have hk : zornRestriction' in line and 'simp [' in line and 'ring' not in line:
        line = line.replace('zornRestriction_C]', 'zornRestriction_C] <;> ring')
    
    # For pullback_pderiv_*
    # If it is case add, and we are NOT in pullback_pderiv_4 or 7, add ; ring
    # Wait, how to know which lemma we are in?
    
    new_lines.append(line)

text = "".join(new_lines)

# Fix case add for 0, 1, 2, 3, 5, 6
def fix_add_case(match):
    lemma_name = match.group(1)
    body = match.group(2)
    if lemma_name in ['4', '7']:
        return f"lemma pullback_pderiv_{lemma_name}{body}"
    else:
        return f"lemma pullback_pderiv_{lemma_name}{body}".replace('hp, hq]\n', 'hp, hq]; ring\n')

text = re.sub(r'lemma pullback_pderiv_(\d)(.*?)(?=\nlemma|\nnoncomputable|\ntheorem|\Z)', fix_add_case, text, flags=re.DOTALL)

with open('proofs/ZornWheelerDeWittExtension.lean', 'w') as f:
    f.write(text)

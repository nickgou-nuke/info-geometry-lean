import re

with open('proofs/ZornWheelerDeWittExtension.lean', 'r') as f:
    text = f.read()

# Fix the "No goals to be solved" by removing `; ring` from the `case add` lines
text = re.sub(r'case add p q hp hq => simp \[(.*?)\]; ring', r'case add p q hp hq => simp [\1]', text)

# Fix the `fin_cases k <;> simp [...]` in all pullback_pderiv_* to have `<;> try { rw [← map_neg]; congr 1; norm_num }`
text = re.sub(r'(fin_cases k <;> simp \[.*?\])(?! <;>)', r'\1 <;> try { rw [← map_neg]; congr 1; norm_num }', text)

with open('proofs/ZornWheelerDeWittExtension.lean', 'w') as f:
    f.write(text)

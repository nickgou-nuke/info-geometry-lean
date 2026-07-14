import re

with open("sandbox/MobiusHelpers.lean", "r") as f:
    helpers = f.read()

# Extract comp
comp_match = re.search(r"def comp \([^\n]+\n(?:[ \t]+.*?\n)+", helpers, re.MULTILINE)
comp_code = comp_match.group(0) if comp_match else ""

# Extract eval_inv
eval_inv_match = re.search(r"lemma eval_inv \([^\n]+\n(?:[ \t]+.*?\n)+", helpers, re.MULTILINE)
eval_inv_code = eval_inv_match.group(0) if eval_inv_match else ""

# Extract eval_comp
eval_comp_match = re.search(r"lemma eval_comp \([^\n]+\n(?:[ \t]+.*?\n)+", helpers, re.MULTILINE)
eval_comp_code = eval_comp_match.group(0) if eval_comp_match else ""

with open("sandbox/MobiusFinalProof.lean", "r") as f:
    final_proof_file = f.read()

final_proof_match = re.search(r"theorem strictly_three_transitive[\s\S]+?(?=\n\n|\Z)", final_proof_file)
final_proof_code = final_proof_match.group(0) if final_proof_match else ""

with open("sandbox/MobiusGeometry.lean", "r") as f:
    geom = f.read()

geom = re.sub(
    r"/-- The action of the Möbius group on the Riemann sphere is strictly 3-transitive\.\n    Any three distinct points determine a unique Möbius transformation\n    mapping them to any other three distinct points\. -/\ntheorem strictly_three_transitive[\s\S]+?sorry\n",
    "",
    geom
)

# Insert after `def inv ... exact h }`
inv_pattern = r"def inv \(M : MobiusTransform\) : MobiusTransform :=\n(?:[ \t]+.*?\n)+?[ \t]+exact h \}\n"
insertion = f"\n{eval_inv_code}\n{comp_code}\n{eval_comp_code}\n/-- The action of the Möbius group on the Riemann sphere is strictly 3-transitive.\n    Any three distinct points determine a unique Möbius transformation\n    mapping them to any other three distinct points. -/\n{final_proof_code}\n"

geom = re.sub(inv_pattern, lambda m: m.group(0) + insertion, geom)

with open("sandbox/MobiusGeometry.lean", "w") as f:
    f.write(geom)

print("Insertion complete")

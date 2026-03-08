import os
import re
import json


class LegacyIntakeParser:
    """Parser to extract mathematical claims and assumptions from legacy notes."""

    def __init__(self):
        self.claim_pattern = re.compile(
            r'\\begin{theorem}\[(.*?)\](.*?)\\end{theorem}', re.DOTALL
        )
        self.assumption_pattern = re.compile(r'\\item (.*)')

    def parse_tex(self, file_path):
        """Extract claims from LaTeX files."""
        with open(file_path, 'r') as f:
            content = f.read()

        claims = []
        for match in self.claim_pattern.finditer(content):
            title = match.group(1).strip()
            body = match.group(2).strip()
            line_no = content.count('\n', 0, match.start()) + 1

            # Simple assumption extraction from surrounding itemize
            assumptions = self.assumption_pattern.findall(body)

            claims.append({
                'title': title,
                'body': body,
                'assumptions': assumptions,
                'source': f"{file_path}:{line_no}",
            })
        return claims

    def generate_lean_claim(self, claim, claim_id):
        """Format a parsed claim into a Lean definition snippet."""
        target_statement = claim['body'].replace('\n', ' ').strip()
        if len(target_statement) > 160:
            target_statement = target_statement[:157] + "..."
        lean_snippet = f"""
/--
## {claim_id}: {claim['title']}
Source: `{claim['source']}`
Body: {claim['body'][:100]}...
Assumptions: {claim['assumptions']}
-/
def claim_{claim_id.split('_')[-1]}_meta : LegacyClaim := {{
  id := "{claim_id}",
  source := "{claim['source']}",
  domain := "AutoExtracted",
  assumptions := {json.dumps(claim['assumptions'])},
  targetStatement := {json.dumps(target_statement)},
  status := ClaimStatus.Claim
}}
"""
        return lean_snippet


if __name__ == "__main__":
    parser = LegacyIntakeParser()
    # Example execution on a known file
    target = (
        "/home/goutev/LEAN4/EINSTEIN/Einstein_Universe_Blueprint/"
        "volumes/volume1/sections/13_synthesis.tex"
    )
    if os.path.exists(target):
        claims = parser.parse_tex(target)
        for i, c in enumerate(claims):
            print(parser.generate_lean_claim(c, f"AUTO_{i+1:03}"))

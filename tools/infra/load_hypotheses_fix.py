def load_hypotheses_from_oracle_result(result_file: Path) -> list[Hypothesis]:
    """Parse the oracle result (HYPOTHESIS N — format) into Hypothesis objects."""
    if not result_file.exists():
        return []
    content = result_file.read_text()
    hypotheses = []
    
    # Strategy: Match HYPOTHESIS N — format
    import re
    blocks = re.split(r'HYPOTHESIS \d+ —', content)[1:]
    if blocks:
        for i, block in enumerate(blocks):
            lines = block.strip().split('\n')
            if not lines:
                continue
            statement = lines[0].strip()
            rationale = ""
            for line in lines[1:]:
                if line.strip().startswith("RATIONALE"):
                    rationale = line.split("—", 1)[-1].strip()
                    break
            if not rationale and len(lines) > 1:
                rationale = '\n'.join(lines[1:5]).strip()
            
            h = Hypothesis(
                id=f"auto_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{i}",
                statement=lines[0].strip(),
                rationale=rationale,
                mathematical_objects=["spectrum", "C*-algebra", "functional-calculus", "fibonacci", "K-theory", "presheaf", "sheaf", "causal-site", "alexandrov-topology"],
                source_apex="InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz",
            )
            hypotheses.append(h)
    
    return hypotheses
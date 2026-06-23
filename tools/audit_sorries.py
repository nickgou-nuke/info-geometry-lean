import os
import re

lean_dir = "lean/InfoGeometry"
results = []

for root, _, files in os.walk(lean_dir):
    for file in files:
        if file.endswith(".lean"):
            filepath = os.path.join(root, file)
            with open(filepath, 'r') as f:
                content = f.read()
                
            matches = re.finditer(r'\b(sorry|admit|axiom)\b', content)
            count = sum(1 for _ in matches)
            if count > 0:
                # Classify based on heuristics
                classification = "Unclassified"
                
                if "Eval/" in filepath or "Lint/" in filepath or "Meta/" in filepath or "Test" in file:
                    classification = "Stale Scaffolding / Test Artifacts"
                elif "External/" in filepath or "Auto/" in filepath or "axiom" in content:
                    classification = "Intentional Assumption Modules"
                elif "sandbox" in filepath.lower() or "legacy" in filepath.lower():
                    classification = "Stale Scaffolding"
                elif count == 1:
                    classification = "Likely Removable Wrapper / Single Debt"
                else:
                    classification = "Real Theorem Debt"
                    
                results.append({
                    "file": filepath,
                    "count": count,
                    "classification": classification
                })

results.sort(key=lambda x: x["count"], reverse=True)

with open("sorry_audit_report.md", "w") as out:
    out.write("# Sorry/Admit/Axiom Audit Report\n\n")
    out.write("Total files with debt: " + str(len(results)) + "\n\n")
    
    categories = {}
    for r in results:
        cat = r["classification"]
        if cat not in categories:
            categories[cat] = []
        categories[cat].append(r)
        
    for cat, items in categories.items():
        total_sorries = sum(x["count"] for x in items)
        out.write(f"## {cat} (Total Hits: {total_sorries})\n")
        for item in items:
            out.write(f"- `{item['file']}`: {item['count']} hits\n")
        out.write("\n")
        
print("Report generated: sorry_audit_report.md")

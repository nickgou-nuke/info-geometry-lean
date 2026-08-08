import requests
import json
import re

url = "http://127.0.0.1:8529/_db/info_geometry/_api/cursor"
auth = ('root', '')

# Search case-insensitively across lean_decls
query = """
FOR d IN lean_decls
  FILTER LOWER(d.name) LIKE "%nolen%" 
      OR LOWER(d.name) LIKE "%schiffer%" 
      OR LOWER(d.name) LIKE "%isospin%" 
      OR LOWER(d.name) LIKE "%f72%"
  RETURN {
    name: d.name,
    module: d.module,
    dependencies: d.dependencies,
    references: d.references,
    type: d.type,
    value: d.value,
    limits: d.limits
  }
"""

try:
    response = requests.post(url, auth=auth, json={"query": query})
    response.raise_for_status()
    data = response.json()
    results = data.get('result', [])
    
    report_content = "# Lean 4 Extracted Limits\n\n"
    
    # Filter specific targets requested by the user
    target_keywords = ['nolen', 'schiffer', 'isospin', 'f72']
    
    if not results:
        report_content += "No matching theorems or modules found in ArangoDB.\n"
    else:
        for item in results:
            name_lower = str(item.get('name', '')).lower()
            if any(k in name_lower for k in target_keywords):
                report_content += f"## {item.get('name', 'Unknown')}\n"
                report_content += f"- **Module:** {item.get('module', 'N/A')}\n"
                deps = item.get('dependencies') or item.get('references') or 'None listed'
                report_content += f"- **Dependencies:** {deps}\n"
                
                # Derived limits (heuristic extraction from type, value or limits fields)
                limits = item.get('limits')
                if not limits:
                    val = str(item.get('value', ''))
                    typ = str(item.get('type', ''))
                    limits = f"Extracted from type/value: {typ} / {val[:100]}"
                report_content += f"- **Derived Limits:** {limits}\n"
                report_content += "\n"
                
    with open("Lean4_Extracted_Limits.md", "w") as f:
        f.write(report_content)
        
    print("Graph extraction complete. Saved to Lean4_Extracted_Limits.md")
    print(f"Found {len(results)} relevant items.")
except Exception as e:
    print(f"Error querying ArangoDB: {e}")

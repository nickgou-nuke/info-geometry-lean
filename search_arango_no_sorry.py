from arango import ArangoClient
import re

client = ArangoClient(hosts='http://localhost:8540')
db = client.db('hive_memory', username='root', password='hive_brain')

query = """
FOR doc IN Thoughts
  FILTER doc.content LIKE "%non_parabolic_normal_form%"
  RETURN doc.content
"""

cursor = db.aql.execute(query)
results = list(cursor)

found_proof = False
for i, content in enumerate(results):
    # Find all occurrences of non_parabolic_normal_form
    matches = re.finditer(r"theorem non_parabolic_normal_form.*?(?=theorem|def|lemma|/-|/--|\Z)", content, re.DOTALL)
    for m in matches:
        snippet = m.group(0)
        if "sorry" not in snippet:
            print(f"--- Found proof in result {i} ---")
            print(snippet)
            found_proof = True

if not found_proof:
    print("No non-sorry proofs found in ArangoDB.")

from arango import ArangoClient

# Initialize the ArangoDB client.
client = ArangoClient(hosts='http://localhost:8540')

# Connect to "hive_memory" database as root user.
db = client.db('hive_memory', username='root', password='hive_brain')

# Execute an AQL query to search for the theorem proof.
query = """
FOR doc IN Thoughts
  FILTER doc.content LIKE "%non_parabolic_normal_form%" OR doc.thought LIKE "%non_parabolic_normal_form%"
  RETURN doc
"""

cursor = db.aql.execute(query)
results = list(cursor)
print(f"Found {len(results)} results.")

for i, res in enumerate(results):
    print(f"--- Result {i+1} ---")
    content = res.get('content', '')
    thought = res.get('thought', '')
    
    if len(content) > 1000:
        print(f"Content snippet: {content[:500]} ... {content[-500:]}")
    else:
        print(f"Content: {content}")
        
    print(f"Thought: {thought[:200]}...")

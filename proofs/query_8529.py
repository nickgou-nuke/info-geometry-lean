import requests
import json

try:
    query = {"query": "FOR m IN memories FILTER LOWER(m.content) LIKE '%methodology%' OR LOWER(m.title) LIKE '%methodology%' RETURN m"}
    resp = requests.post("http://localhost:8529/_db/brain_graph/_api/cursor", json=query)
    data = resp.json()
    if not data.get('error'):
        for doc in data.get('result', []):
            print("TITLE:", doc.get('title'))
            print("CONTENT:", doc.get('content'))
            print("-" * 80)
    else:
        print("Error in query:", data)
except Exception as e:
    print(f"Exception: {e}")

import requests
import json

url = "http://127.0.0.1:8529/_db/info_geometry/_api/cursor"
auth = ('root', '')

query = """
FOR m IN lean_modules
  FILTER m.name LIKE "%Nolen%" 
      OR m.name LIKE "%Isospin%" 
      OR m.name LIKE "%F72%"
  RETURN m
"""

response = requests.post(url, auth=auth, json={"query": query})
print(json.dumps(response.json(), indent=2))

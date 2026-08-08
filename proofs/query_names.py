import requests
import json

url = "http://127.0.0.1:8529/_db/info_geometry/_api/cursor"
auth = ('root', '')

query = """
FOR d IN lean_decls
  FILTER LOWER(d.name) LIKE "%nolen%" 
      OR LOWER(d.name) LIKE "%schiffer%" 
      OR LOWER(d.name) LIKE "%isospin%" 
      OR LOWER(d.name) LIKE "%f72%"
  RETURN d.name
"""
response = requests.post(url, auth=auth, json={"query": query})
print("Decls:")
for item in response.json().get('result', []):
    if "nolen" in item.lower() or "schiffer" in item.lower() or "f72" in item.lower():
        print("  " + item)

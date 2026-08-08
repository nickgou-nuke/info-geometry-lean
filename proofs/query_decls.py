import requests
import json

url = "http://127.0.0.1:8529/_db/info_geometry/_api/cursor"
auth = ('root', '')

query = """
FOR d IN lean_decls
  FILTER d.name LIKE "%NolenSchifferAnomaly%" 
      OR d.name LIKE "%HeavyIsospinMixingSystematics%" 
      OR d.name LIKE "%F72ShellSystematicsBE2%"
  RETURN d
"""

response = requests.post(url, auth=auth, json={"query": query})
print(json.dumps(response.json(), indent=2))

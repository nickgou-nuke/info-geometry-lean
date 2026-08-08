import requests
import json

url = "http://127.0.0.1:8529/_db/info_geometry/_api/collection"
auth = ('root', '')

response = requests.get(url, auth=auth)
print(response.json())

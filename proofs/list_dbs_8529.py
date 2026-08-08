import requests

try:
    resp = requests.get("http://localhost:8529/_api/database")
    print(resp.json())
except Exception as e:
    print(f"Error: {e}")

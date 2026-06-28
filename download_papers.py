import urllib.request
import urllib.parse
import xml.etree.ElementTree as ET
import os

queries = [
    'all:"mirror nuclei" AND all:"Tonev"',
    'all:"31P" AND all:"31S" AND all:"mirror"',
    'all:"35Ar" AND all:"35Cl" AND all:"mirror"',
    'all:"39Ca" AND all:"39K" AND all:"mirror"',
    'all:"47Cr" AND all:"47V" AND all:"mirror"'
]

results = []

for q in queries:
    url = f'http://export.arxiv.org/api/query?search_query={urllib.parse.quote(q)}&start=0&max_results=3'
    try:
        response = urllib.request.urlopen(url)
        data = response.read()
        root = ET.fromstring(data)
        
        for entry in root.findall('{http://www.w3.org/2005/Atom}entry'):
            title = entry.find('{http://www.w3.org/2005/Atom}title').text.strip()
            summary = entry.find('{http://www.w3.org/2005/Atom}summary').text.strip()
            authors = [a.find('{http://www.w3.org/2005/Atom}name').text for a in entry.findall('{http://www.w3.org/2005/Atom}author')]
            link = entry.find('{http://www.w3.org/2005/Atom}id').text
            results.append(f"### {title}\n**Authors:** {', '.join(authors)}\n**Link:** {link}\n**Abstract:**\n{summary}\n")
    except Exception as e:
        print(f"Failed query {q}: {e}")

# Also fetch Crossref for the specific DOI
doi = "10.1103/PhysRevC.110.024322"
try:
    req = urllib.request.Request(f"https://api.crossref.org/works/{doi}", headers={'User-Agent': 'Python'})
    resp = urllib.request.urlopen(req)
    import json
    data = json.loads(resp.read())
    item = data['message']
    title = item.get('title', [''])[0]
    authors = [a.get('family', '') for a in item.get('author', [])]
    results.append(f"### {title}\n**Authors:** {', '.join(authors)}\n**DOI:** {doi}\n")
except Exception as e:
    print(f"Failed DOI fetch: {e}")

with open('mirror_nuclei_papers.md', 'w') as f:
    f.write("# Downloaded Paper Abstracts: Mirror Nuclei\n\n")
    if not results:
        f.write("No open-access preprints found on arXiv matching the exact queries.\n")
    else:
        # Deduplicate
        seen = set()
        for r in results:
            if r not in seen:
                f.write(r + "\n---\n")
                seen.add(r)
print("Done writing to mirror_nuclei_papers.md")

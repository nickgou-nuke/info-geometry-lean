import os
import re
from arango import ArangoClient

DB_URL = "http://127.0.0.1:8529"
DB_USER = "root"
DB_PASS = ""
DB_NAME = "info_geometry"
LEAN_DIR = "/home/goutev/auto/proofs/"

def connect_db():
    client = ArangoClient(hosts=DB_URL)
    sys_db = client.db('_system', username=DB_USER, password=DB_PASS)
    if not sys_db.has_database(DB_NAME):
        sys_db.create_database(DB_NAME)
    
    db = client.db(DB_NAME, username=DB_USER, password=DB_PASS)
    
    if not db.has_collection("lean_nodes"):
        db.create_collection("lean_nodes")
    if not db.has_collection("lean_edges", edge=True):
        db.create_collection("lean_edges", edge=True)
        
    return db

def parse_lean_files(directory):
    # Regex to capture type (theorem|def|axiom|lemma) and name
    pattern = re.compile(r'\b(theorem|def|axiom|lemma)\s+([a-zA-Z0-9_]+)', re.MULTILINE)
    
    entities = {}
    
    # 1st pass: gather all entities
    for root, _, files in os.walk(directory):
        for f in files:
            if f.endswith(".lean"):
                filepath = os.path.join(root, f)
                with open(filepath, 'r', encoding='utf-8') as f_in:
                    content = f_in.read()
                    matches = pattern.finditer(content)
                    for match in matches:
                        ent_type = match.group(1)
                        ent_name = match.group(2)
                        entities[ent_name] = {
                            "type": ent_type,
                            "name": ent_name,
                            "filepath": filepath,
                            "content": "" # We won't bother with full content for a basic parser
                        }
    
    # 2nd pass: crude dependency extraction by tokenizing the files and checking if names appear after definition
    # This is an approximation. 
    for root, _, files in os.walk(directory):
        for f in files:
            if f.endswith(".lean"):
                filepath = os.path.join(root, f)
                with open(filepath, 'r', encoding='utf-8') as f_in:
                    lines = f_in.readlines()
                    current_ent = None
                    for line in lines:
                        match = pattern.search(line)
                        if match:
                            current_ent = match.group(2)
                        
                        if current_ent:
                            if "deps" not in entities[current_ent]:
                                entities[current_ent]["deps"] = set()
                            
                            words = re.findall(r'[a-zA-Z0-9_]+', line)
                            for word in words:
                                if word in entities and word != current_ent:
                                    entities[current_ent]["deps"].add(word)
                                    
    return entities

def populate_db(db, entities):
    nodes_coll = db.collection("lean_nodes")
    edges_coll = db.collection("lean_edges")
    
    nodes_coll.truncate()
    edges_coll.truncate()
    
    for name, data in entities.items():
        node = {
            "_key": name,
            "name": name,
            "type": data["type"],
            "filepath": data["filepath"]
        }
        nodes_coll.insert(node, ignore_revs=True)
        
    for name, data in entities.items():
        deps = data.get("deps", [])
        for dep in deps:
            edge = {
                "_from": f"lean_nodes/{name}",
                "_to": f"lean_nodes/{dep}"
            }
            edges_coll.insert(edge, ignore_revs=True)
            
if __name__ == "__main__":
    db = connect_db()
    entities = parse_lean_files(LEAN_DIR)
    populate_db(db, entities)
    print(f"Extracted {len(entities)} nodes and their edges to ArangoDB.")

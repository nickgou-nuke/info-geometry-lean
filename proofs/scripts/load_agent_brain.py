import os
import glob
import json
import hashlib
from arango import ArangoClient

# Configuration
DB_NAME = "agent_brain"
ROOT_PWD = "alexandria_root"
PORT = 8530
BRAIN_DIR = "/home/goutev/.gemini/antigravity-cli/brain"

def hash_content(content):
    if content is None:
        return "null"
    return hashlib.sha256(content.encode('utf-8')).hexdigest()

def load_brain():
    client = ArangoClient(hosts=f'http://localhost:{PORT}')
    sys_db = client.db('_system', username='root', password=ROOT_PWD)
    
    if not sys_db.has_database(DB_NAME):
        sys_db.create_database(DB_NAME)
        
    db = client.db(DB_NAME, username='root', password=ROOT_PWD)
    
    # Create collections
    if not db.has_collection('steps'):
        steps_col = db.create_collection('steps')
    else:
        steps_col = db.collection('steps')
        
    if not db.has_collection('next_step'):
        next_step_edge = db.create_collection('next_step', edge=True)
    else:
        next_step_edge = db.collection('next_step')

    if not db.has_collection('spawns'):
        spawns_edge = db.create_collection('spawns', edge=True)
    else:
        spawns_edge = db.collection('spawns')

    # Truncate collections to avoid duplication on reload
    steps_col.truncate()
    next_step_edge.truncate()
    spawns_edge.truncate()

    print("Loading transcripts...")
    conversations = {}
    spawn_events = []

    # Parse all transcripts
    pattern = os.path.join(BRAIN_DIR, "*", ".system_generated", "logs", "transcript.jsonl")
    for filepath in glob.glob(pattern):
        conv_id = filepath.split('/')[-4]
        conversations[conv_id] = []
        
        with open(filepath, 'r') as f:
            prev_key = None
            for line in f:
                try:
                    step_data = json.loads(line.strip())
                except json.JSONDecodeError:
                    continue
                
                step_idx = step_data.get('step_index', 0)
                step_type = step_data.get('type', 'UNKNOWN')
                content = step_data.get('content', '')
                source = step_data.get('source', '')
                
                # De Bruijn style hashing for structural matching
                content_hash = hash_content(content)
                
                # Document key
                step_key = f"{conv_id}_{step_idx}"
                
                doc = {
                    "_key": step_key,
                    "conversation_id": conv_id,
                    "step_index": step_idx,
                    "type": step_type,
                    "source": source,
                    "content": content,
                    "content_hash": content_hash,
                    "tool_calls": step_data.get('tool_calls', [])
                }
                
                steps_col.insert(doc)
                
                # Link to previous step
                if prev_key is not None:
                    next_step_edge.insert({
                        "_from": f"steps/{prev_key}",
                        "_to": f"steps/{step_key}",
                        "conversation_id": conv_id
                    })
                    
                prev_key = step_key
                
                # Look for subagent spawns to link later
                if step_type == 'PLANNER_RESPONSE' and step_data.get('tool_calls'):
                    for tool in step_data['tool_calls']:
                        if tool.get('name') == 'invoke_subagent':
                            # We can't know the new conv_id from here directly without parsing system messages,
                            # but we can store this event and try to match it if we need to.
                            # For now, we will just record the tool call.
                            pass

    print("Graph construction complete!")

if __name__ == "__main__":
    load_brain()

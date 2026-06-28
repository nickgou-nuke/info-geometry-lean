import os
import glob
import json
import time
from arango.client import ArangoClient
import logging

# Hive Memory Config
CLIENT = ArangoClient(hosts='http://localhost:8540')
DB = CLIENT.db('hive_memory', username='root', password='hive_brain')
THOUGHTS = DB['Thoughts']

# Path to the shared transcript pool
SHARED_TRANSCRIPTS_PATH = "/home/goutev/repos/info-geometry-lean/brain"
LAST_PROCESSED_LOG = "/home/goutev/.hermes/hive_last_processed.txt"

logging.basicConfig(level=logging.INFO)

def get_last_processed():
    if os.path.exists(LAST_PROCESSED_LOG):
        with open(LAST_PROCESSED_LOG, "r") as f:
            return f.read().strip()
    return None

def set_last_processed(path):
    with open(LAST_PROCESSED_LOG, "w") as f:
        f.write(path)

def ingest():
    last_processed = get_last_processed()
    # Find all transcript files in the shared brain space
    files = glob.glob(os.path.join(SHARED_TRANSCRIPTS_PATH, "*/.system_generated/logs/transcript_full.jsonl"))
    
    for f in files:
        if f == last_processed:
            continue
            
        logging.info(f"Ingesting: {f}")
        try:
            with open(f, "r") as json_file:
                for line in json_file:
                    entry = json.loads(line)
                    # Insert into Thoughts collection
                    THOUGHTS.insert(entry, overwrite=True)
            set_last_processed(f)
        except Exception as e:
            logging.error(f"Error ingesting {f}: {e}")

if __name__ == "__main__":
    while True:
        ingest()
        time.sleep(300) # Poll every 5 minutes

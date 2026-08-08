import glob
import json
log_path = '/home/goutev/.gemini/antigravity-cli/brain/8e866277-f311-4ec3-a6ea-c1a3f503e74b/.system_generated/logs/transcript_full.jsonl'
output_path = '/home/goutev/auto/proofs/CuntzFibonacciSimilarityFlow.lean'

with open(log_path, 'r') as f:
    for line in f:
        data = json.loads(line)
        if data.get('type') == 'VIEW_FILE' and 'CuntzFibonacciSimilarityFlow.lean' in data.get('content', ''):
            lines = data['content'].split('\n')
            original_lines = []
            for l in lines:
                if ':' in l:
                    parts = l.split(':', 1)
                    if parts[0].isdigit():
                        original_lines.append(parts[1][1:]) # remove leading space
            
            if len(original_lines) > 0:
                with open(output_path, 'w') as out:
                    out.write('\n'.join(original_lines) + '\n')
                print("Recovered CuntzFibonacciSimilarityFlow.lean base from VIEW_FILE")
                break

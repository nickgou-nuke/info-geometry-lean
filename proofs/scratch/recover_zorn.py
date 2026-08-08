import json

log_path = '/home/goutev/.gemini/antigravity-cli/brain/81f3bd20-d81c-4cb7-85c4-e62c1ff7956c/.system_generated/logs/transcript_full.jsonl'
output_path = '/home/goutev/auto/proofs/ZornPeirceBridge.lean'

with open(log_path, 'r') as f:
    for line in f:
        data = json.loads(line)
        if data.get('type') == 'VIEW_FILE' and 'ZornPeirceBridge.lean' in data.get('content', ''):
            # Extract the content without line numbers
            # The content in the JSON might be the original string before formatting, let's check
            # No, VIEW_FILE in transcript stores the formatted output.
            # But wait, in transcript_full.jsonl, does it store the original tool output or the formatted text sent to the model?
            # It stores the formatted text.
            lines = data['content'].split('\n')
            original_lines = []
            for l in lines:
                if ':' in l:
                    parts = l.split(':', 1)
                    if parts[0].isdigit():
                        original_lines.append(parts[1][1:]) # remove leading space
            
            with open(output_path, 'w') as out:
                out.write('\n'.join(original_lines) + '\n')
            print("Recovered ZornPeirceBridge.lean")
            break

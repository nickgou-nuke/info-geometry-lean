import subprocess
import json
import time

def send_request(proc, req):
    msg = json.dumps(req)
    content = f"Content-Length: {len(msg)}\r\n\r\n{msg}"
    proc.stdin.write(content.encode('utf-8'))
    proc.stdin.flush()

def read_response(proc):
    # Read headers
    content_length = 0
    while True:
        line = proc.stdout.readline().decode('utf-8')
        if not line.strip():
            break
        if line.startswith("Content-Length:"):
            content_length = int(line.split(":")[1].strip())
    
    if content_length > 0:
        body = proc.stdout.read(content_length).decode('utf-8')
        return json.loads(body)
    return None

def main():
    print("Starting lake serve...")
    proc = subprocess.Popen(
        ['lake', 'serve'],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE
    )

    # 1. Initialize
    send_request(proc, {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {
            "processId": None,
            "rootUri": None,
            "capabilities": {}
        }
    })
    print("Initialize response:", read_response(proc))

    # 1.5 Send initialized notification
    send_request(proc, {
        "jsonrpc": "2.0",
        "method": "initialized",
        "params": {}
    })

    # 2. didOpen
    print("\nOpening test_infotree.lean...")
    with open('test_infotree.lean', 'r') as f:
        text = f.read()
    
    send_request(proc, {
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///home/goutev/auto/test_infotree.lean",
                "languageId": "lean",
                "version": 1,
                "text": text
            }
        }
    })

    # Wait a bit for processing
    time.sleep(1)

    # 3. Request plainGoal (Let's query line 4, col 2 which is right after `induction n with`)
    # Note: LSP is 0-indexed for lines and columns!
    print("\nRequesting goal state at line 4 (0-indexed line 3), column 2...")
    try:
        send_request(proc, {
            "jsonrpc": "2.0",
            "id": 2,
            "method": "$/lean/plainGoal",
            "params": {
                "textDocument": {
                    "uri": "file:///home/goutev/auto/test_infotree.lean"
                },
                "position": {
                    "line": 4, 
                    "character": 4
                }
            }
        })
    except BrokenPipeError:
        print("Broken pipe when sending plainGoal request!")
        err = proc.stderr.read().decode('utf-8')
        print("STDERR:", err)
        return

    # Read diagnostic notifications and the response
    for _ in range(20):
        resp = read_response(proc)
        if resp:
            if resp.get('id') == 2:
                print("\nGOAL STATE FOUND:")
                print(json.dumps(resp, indent=2))
                break
            else:
                print("Message:", json.dumps(resp)[:100])
        time.sleep(0.5)

    proc.terminate()

if __name__ == "__main__":
    main()

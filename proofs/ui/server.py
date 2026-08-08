import asyncio
import websockets
import json
import numpy as np
import sys
import os
import time

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../')))
import cl55_cuda

async def stream_data(websocket):
    print("Client connected to Holographic Stream!")
    batches_per_frame = 2500
    pipeline = cl55_cuda.ContinuousStream(batches_per_frame)
    A = np.random.randn(32, 32).astype(np.float16)
    pipeline.set_operator(A.view(np.uint16))
    
    start_time = time.time()
    try:
        while True:
            # JWST mock data
            frame_N = np.random.randn(batches_per_frame, 32, 32).astype(np.float16)
            
            # Zero-latency tensor core processing
            logits = pipeline.process_frame_async(frame_N.view(np.uint16))
            
            # Send an array of 256 points for the holographic projection
            # Normalize them for visualization
            data = logits[:256].tolist()
            
            await websocket.send(json.dumps({
                "type": "jwst_stream",
                "logits": data,
                "fps": 1.0 / max(0.001, (time.time() - start_time))
            }))
            start_time = time.time()
            
            await asyncio.sleep(0.03) # 30fps update
    except Exception as e:
        print(f"Stream closed: {e}")

async def main():
    async with websockets.serve(stream_data, "localhost", 8765):
        print("Cℓ(5,5) Holographic Engine Broadcast started on ws://localhost:8765")
        await asyncio.Future()

if __name__ == "__main__":
    asyncio.run(main())

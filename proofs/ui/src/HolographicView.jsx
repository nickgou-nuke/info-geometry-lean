import { useEffect, useRef, useState } from 'react';
import './HolographicView.css';

export default function HolographicView() {
  const canvasRef = useRef(null);
  const [status, setStatus] = useState('Connecting to Cℓ(5,5) Engine...');
  const [fps, setFps] = useState(0);
  const dataRef = useRef(new Array(256).fill(0));

  useEffect(() => {
    let ws;
    try {
      ws = new WebSocket('ws://localhost:8765');
      ws.onopen = () => setStatus('LINK ESTABLISHED: JWST First Light Stream (Zero-Latency)');
      ws.onmessage = (event) => {
        const payload = JSON.parse(event.data);
        if (payload.type === 'jwst_stream') {
          dataRef.current = payload.logits;
          setFps(payload.fps);
        }
      };
      ws.onclose = () => setStatus('LINK LOST');
      ws.onerror = () => setStatus('CONNECTION ERROR');
    } catch (e) {
      setStatus(`ERROR: ${e.message}`);
    }

    return () => {
      if (ws) ws.close();
    };
  }, []);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext('2d');
    let animationId;

    const render = () => {
      const width = canvas.width;
      const height = canvas.height;
      
      // Clear with trail effect for holographic persistence
      ctx.fillStyle = 'rgba(0, 0, 0, 0.15)';
      ctx.fillRect(0, 0, width, height);

      const data = dataRef.current;
      const cx = width / 2;
      const cy = height / 2;
      
      // Draw Amplituhedron Projection (Web of polygons)
      const radius = Math.min(cx, cy) * 0.8;
      
      ctx.strokeStyle = '#00ffaa';
      ctx.lineWidth = 1;
      
      ctx.beginPath();
      for (let i = 0; i < data.length; i++) {
        const val = data[i] * 10; // scale up the logit
        const angle = (i / data.length) * Math.PI * 2;
        const r = radius + val;
        
        const x = cx + Math.cos(angle) * r;
        const y = cy + Math.sin(angle) * r;
        
        if (i === 0) ctx.moveTo(x, y);
        else ctx.lineTo(x, y);
      }
      ctx.closePath();
      ctx.stroke();

      // Draw energetic connections (inner web)
      ctx.strokeStyle = 'rgba(120, 255, 230, 0.2)';
      ctx.beginPath();
      for (let i = 0; i < data.length; i += 7) {
        for (let j = i + 13; j < data.length; j += 17) {
            const a1 = (i / data.length) * Math.PI * 2;
            const a2 = (j / data.length) * Math.PI * 2;
            const r1 = radius + data[i] * 10;
            const r2 = radius + data[j] * 10;
            ctx.moveTo(cx + Math.cos(a1) * r1, cy + Math.sin(a1) * r1);
            ctx.lineTo(cx + Math.cos(a2) * r2, cy + Math.sin(a2) * r2);
        }
      }
      ctx.stroke();

      // Scanline effect
      const time = Date.now() / 1000;
      const scanY = (time % 2) * height;
      ctx.fillStyle = 'rgba(0, 255, 170, 0.1)';
      ctx.fillRect(0, scanY, width, 5);

      animationId = requestAnimationFrame(render);
    };

    render();

    return () => {
      cancelAnimationFrame(animationId);
    };
  }, []);

  return (
    <div className="holo-container">
      <div className="holo-hud">
        <h2>QUANTUM TRACE PROJECTION</h2>
        <div className={`holo-status ${status.includes('LINK ESTABLISHED') ? 'online' : 'offline'}`}>
          {status}
        </div>
        <div className="holo-stats">
          <div>Engine Throughput: <span>{fps.toFixed(1)} FPS</span></div>
          <div>Tensor Topology: <span>Cℓ(5,5) Spinor Bundle</span></div>
          <div>Source: <span>JWST Mock Orbit</span></div>
        </div>
      </div>
      <canvas 
        ref={canvasRef} 
        width={1200} 
        height={800} 
        className="holo-canvas"
      />
    </div>
  );
}

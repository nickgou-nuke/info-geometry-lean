#!/usr/bin/env node
/**
 * WebSocket Bridge Server
 *
 * Relay server that sits between the ChatGPT-Connect browser extension
 * and the Pi coding agent. Both connect as WebSocket clients:
 *
 *   ChatGPT-Connect (browser) ←→ [PORT 1956] ←→ Pi extension
 *
 * Protocol:
 *   - ChatGPT-Connect connects and sends { clientID: "chatGPT" }
 *   - Pi extension connects and sends { action: "send_message", message: "..." }
 *   - Server forwards messages from Pi to ChatGPT-Connect
 *   - ChatGPT-Connect responds with streamed JSON events
 *   - Server forwards responses back to Pi
 *
 * Usage:
 *   node scripts/websocket-bridge-server.js
 *   # Starts on ws://localhost:1956
 *
 * Then in Chrome:
 *   1. Open https://chatgpt.com
 *   2. ChatGPT-Connect extension auto-connects to ws://localhost:1956
 *
 * Then in terminal:
 *   pi -e ./chatgpt-oracle.ts "your prompt"
 */

const WebSocket = require('ws');

const PORT = 1956;
const wss = new WebSocket.Server({ port: PORT });

let chatgptClient = null;   // Browser extension connection
let piClient = null;        // Pi extension connection
let messageQueue = [];      // Queue messages if Pi sends before browser connects

console.log(`\n  🔌 WebSocket Bridge Server`);
console.log(`  ═══════════════════════`);
console.log(`  Listening on ws://localhost:${PORT}`);
console.log(`  `);
console.log(`  Waiting for connections...`);
console.log(`  `);
console.log(`  ┌─ Browser:  open https://chatgpt.com`);
console.log(`  │            ChatGPT-Connect auto-connects here`);
console.log(`  ├─ Terminal: pi -e ./chatgpt-oracle.ts \"...\"`);
console.log(`  │            Extension connects here`);
console.log(`  └─ Messages are relayed between them`);
console.log(`\n`);

wss.on('connection', (ws, req) => {
  const clientAddr = req.socket.remoteAddress;
  console.log(`  📡 New connection from ${clientAddr}`);

  ws.on('message', (data) => {
    try {
      const msg = JSON.parse(data.toString());
      console.log(`  📨 Message:`, JSON.stringify(msg).substring(0, 200));

      // ChatGPT-Connect registers itself
      if (msg.clientID === "chatGPT") {
        chatgptClient = ws;
        console.log(`  ✅ ChatGPT-Connect registered (browser extension)`);
        // Flush any queued messages
        while (messageQueue.length > 0) {
          const queued = messageQueue.shift();
          console.log(`  📤 Forwarding queued message to ChatGPT...`);
          chatgptClient.send(JSON.stringify(queued));
        }
        return;
      }

      // Pi extension or other tools send { action: "send_message", message: "..." }
      if (msg.action === "send_message") {
        piClient = ws;
        if (chatgptClient && chatgptClient.readyState === WebSocket.OPEN) {
          console.log(`  📤 Forwarding message to ChatGPT-Connect...`);
          const payload = {
            source: "PI_AGENT",
            conversation: {
              question: msg.message,
              conversationId: msg.conversationId || null,
              parentMessageId: msg.parentMessageId || null,
              deleteAfterFinished: msg.deleteAfterFinished || false
            }
          };
          chatgptClient.send(JSON.stringify(payload));
        } else {
          console.log(`  ⏳ ChatGPT-Connect not connected. Queueing message.`);
          messageQueue.push({
            conversation: {
              question: msg.message,
              conversationId: null,
              parentMessageId: null,
              deleteAfterFinished: false,
              source: "PI_AGENT",
              destination: "chatgpt"
            }
          });
          ws.send(JSON.stringify({
            status: "queued",
            text: "Message queued. Waiting for ChatGPT-Connect to connect..."
          }));
        }
        return;
      }

      // Debug: log all messages from ChatGPT-Connect
      console.log(`  [DEBUG] ChatGPT response keys: ${Object.keys(msg).join(', ')}`);
      if (msg.conversationData) console.log(`  [DEBUG] conversationData:`, JSON.stringify(msg.conversationData).substring(0, 100));
      if (msg.done !== undefined) console.log(`  [DEBUG] done: ${msg.done}`);
      if (msg.error) console.log(`  [DEBUG] error: ${msg.error}`);

      // Responses from ChatGPT-Connect have conversationData or done flag
      if (msg.conversationData || msg.done !== undefined) {
        if (piClient && piClient.readyState === WebSocket.OPEN) {
          const response = {
            text: msg.conversationData?.text || "",
            status: msg.done ? "done" : "streaming",
            messageId: msg.conversationData?.messageId || null,
            conversationId: msg.conversationData?.conversationId || null
          };
          piClient.send(JSON.stringify(response));
          if (msg.done) {
            console.log(`  ✅ Response complete (${(msg.conversationData?.text || "").length} chars)`);
          }
        }
        return;
      }

      // Forward title requests
      if (msg.conversation?.title) {
        if (chatgptClient && chatgptClient.readyState === WebSocket.OPEN) {
          chatgptClient.send(JSON.stringify(msg));
        }
        return;
      }

      console.log(`  Unknown message type:`, Object.keys(msg));

    } catch (e) {
      console.log(`  ❌ Parse error:`, e.message);
    }
  });

  ws.on('close', () => {
    if (ws === chatgptClient) {
      console.log(`  🔌 ChatGPT-Connect disconnected`);
      chatgptClient = null;
    }
    if (ws === piClient) {
      console.log(`  🔌 Pi client disconnected`);
      piClient = null;
    }
  });

  ws.on('error', (err) => {
    console.log(`  ❌ WebSocket error:`, err.message);
  });
});

wss.on('error', (err) => {
  if (err.code === 'EADDRINUSE') {
    console.log(`  ❌ Port ${PORT} already in use. Is the bridge already running?`);
  } else {
    console.log(`  ❌ Server error:`, err.message);
  }
  process.exit(1);
});

// Graceful shutdown
process.on('SIGINT', () => {
  console.log(`\n  👋 Shutting down bridge server...`);
  wss.close(() => process.exit(0));
});

console.log(`  PID: ${process.pid}`);

#!/usr/bin/env node
import WebSocket, { WebSocketServer } from 'ws';

const PORT = Number(process.env.PORT || 1956);
const server = new WebSocketServer({ port: PORT });

let chatgptClient = null;
let piClient = null;
const messageQueue = [];

function isOpen(ws) {
  return ws && ws.readyState === WebSocket.OPEN;
}

function sendJson(ws, payload) {
  if (isOpen(ws)) {
    ws.send(JSON.stringify(payload));
  }
}

function chatgptPayload(msg) {
  return {
    source: 'PI_AGENT',
    conversation: {
      question: msg.message,
      conversationId: msg.conversationId || null,
      parentMessageId: msg.parentMessageId || null,
      deleteAfterFinished: Boolean(msg.deleteAfterFinished),
    },
  };
}

function handleDiagnostic(ws, msg) {
  switch (msg.type) {
    case 'status':
      sendJson(ws, {
        type: 'status',
        status: 'bridge running',
        port: PORT,
        chatgptConnected: isOpen(chatgptClient),
        queuedMessages: messageQueue.length,
        bridges: [
          'chatGPT browser relay',
          'ConformalSL2GeneratorBridge',
          'V4SemidirectS3Bridge',
          'Cl55V4SpinorFragmentation',
          'PrimeFibonacciLattice',
        ],
      });
      return true;
    case 'build':
      sendJson(ws, { type: 'response', status: 'ack', target: 'lean' });
      return true;
    case 'sympy':
      sendJson(ws, { type: 'response', status: 'ack', target: 'sympy' });
      return true;
    default:
      return false;
  }
}

function handleChatGPTRegistration(ws) {
  chatgptClient = ws;
  console.log('ChatGPT browser client registered');

  while (messageQueue.length > 0 && isOpen(chatgptClient)) {
    chatgptClient.send(JSON.stringify(messageQueue.shift()));
  }
}

function handlePiMessage(ws, msg) {
  piClient = ws;
  const payload = chatgptPayload(msg);

  if (isOpen(chatgptClient)) {
    console.log('Forwarding Pi message to ChatGPT browser client');
    chatgptClient.send(JSON.stringify(payload));
    return;
  }

  console.log('ChatGPT browser client not connected; queued Pi message');
  messageQueue.push(payload);
  sendJson(ws, {
    status: 'queued',
    text: 'Message queued. Waiting for ChatGPT-Connect to connect.',
  });
}

function handleChatGPTResponse(msg) {
  if (!isOpen(piClient)) {
    return;
  }

  sendJson(piClient, {
    text: msg.conversationData?.text || msg.text || '',
    status: msg.done ? 'done' : 'streaming',
    messageId: msg.conversationData?.messageId || null,
    conversationId: msg.conversationData?.conversationId || null,
  });
}

console.log(`Bridge listening on ws://localhost:${PORT}`);
console.log('Browser extension should register with { "clientID": "chatGPT" }');
console.log('Pi/client tools should send { "action": "send_message", "message": "..." }');

server.on('connection', (ws, req) => {
  console.log(`Client connected from ${req.socket.remoteAddress}`);

  ws.on('message', (data) => {
    try {
      const msg = JSON.parse(data.toString());

      if (msg.clientID === 'chatGPT') {
        handleChatGPTRegistration(ws);
        return;
      }

      if (msg.action === 'send_message') {
        handlePiMessage(ws, msg);
        return;
      }

      if (msg.conversationData || msg.done !== undefined || msg.text) {
        handleChatGPTResponse(msg);
        return;
      }

      if (msg.conversation?.title && isOpen(chatgptClient)) {
        chatgptClient.send(JSON.stringify(msg));
        return;
      }

      if (!handleDiagnostic(ws, msg)) {
        sendJson(ws, { type: 'error', message: `Unknown message: ${JSON.stringify(msg).slice(0, 200)}` });
      }
    } catch (e) {
      sendJson(ws, { type: 'error', message: e.message });
    }
  });

  ws.on('close', () => {
    if (ws === chatgptClient) {
      chatgptClient = null;
      console.log('ChatGPT browser client disconnected');
    }
    if (ws === piClient) {
      piClient = null;
      console.log('Pi client disconnected');
    }
  });

  ws.on('error', (err) => {
    console.log(`WebSocket error: ${err.message}`);
  });
});

server.on('error', (err) => {
  if (err.code === 'EADDRINUSE') {
    console.log(`Port ${PORT} already in use. Is the bridge already running?`);
  } else {
    console.log(`Server error: ${err.message}`);
  }
  process.exit(1);
});

process.on('SIGINT', () => {
  console.log('Shutting down bridge server');
  server.close(() => process.exit(0));
});

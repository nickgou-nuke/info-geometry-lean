import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import WebSocket from 'ws';

/**
 * ChatGPT Oracle Bridge
 *
 * Dual-mode consultant LLM tool:
 *   1. WebSocket bridge (port 1956) — routes through browser's ChatGPT session
 *      (requires ChatGPT-Connect extension + open chatgpt.com tab)
 *   2. API fallback — uses DeepSeek/OpenAI API directly
 *
 * The bridge mode is token-free — it uses your browser's ChatGPT session.
 * The API mode always works (requires DEEPSEEK_API_KEY).
 */

export default function (pi: ExtensionAPI) {
  pi.registerTool({
    name: "ask_chatgpt_compiler",
    label: "ChatGPT Oracle Bridge",
    description:
      "USE THIS TOOL ONLY FOR COMPLEX BUGS, ARCHITECTURAL ISSUES, OR COMPILATION ERRORS. " +
      "Sends code and logs to a consultant LLM for expert evaluation. " +
      "Use when you've exhausted local debugging and need a fresh perspective.",
    promptSnippet: "Consult an expert LLM for complex debugging or architectural review",
    promptGuidelines: [
      "Use ask_chatgpt_compiler when you encounter complex bugs, architectural issues, or compilation errors that local debugging cannot resolve.",
    ],
    parameters: Type.Object({
      code: Type.String({
        description: "The problematic source code that needs review or correction.",
      }),
      context: Type.String({
        description:
          "Terminal output, compiler error traceback, or specific question for the Oracle.",
      }),
      systemRole: Type.Optional(
        Type.String({
          description:
            "Optional: Override the consultant's system role. Default: expert code reviewer.",
        })
      ),
    }),
    required: ["code", "context"],

    async execute(
      _toolCallId: string,
      params: { code: string; context: string; systemRole?: string },
      _signal: AbortSignal,
      onUpdate: any,
      _ctx: any
    ) {
      const prompt = `--- ORCHESTRATOR CONTEXT/ERROR ---\n${params.context}\n\n--- CODE TO REVIEW ---\n${params.code}\n\nPlease provide direct fixes, optimized code blocks, or explain the error clearly.`;

      // ── Try WebSocket bridge (browser ChatGPT) first ──
      try {
        const bridgeResult = await tryWebSocketBridge(prompt, onUpdate);
        if (bridgeResult) return bridgeResult;
      } catch {
        // Bridge failed silently, fall through to API
      }

      // ── Fall back to DeepSeek API ──
      return await tryApiFallback(prompt, params.systemRole, onUpdate);
    },
  });
}

/**
 * Try to send the prompt via the WebSocket bridge to browser ChatGPT.
 * Returns a result if successful, or null if the bridge is unavailable.
 */
async function tryWebSocketBridge(
  prompt: string,
  onUpdate: any
): Promise<{ content: { type: "text"; text: string }[] } | null> {
  return new Promise((resolve) => {
    const ws = new WebSocket("ws://localhost:1956");
    let fullResponse = "";

    const timeout = setTimeout(() => {
      ws.close();
      resolve(null); // Bridge unavailable, fall through
    }, 3000);

    ws.on("open", () => {
      clearTimeout(timeout);
      onUpdate?.({
        content: [{ type: "text" as const, text: "Consulting ChatGPT via browser bridge (token-free)..." }],
      });
      ws.send(JSON.stringify({ action: "send_message", message: prompt }));
    });

    ws.on("message", (data: WebSocket.Data) => {
      try {
        const res = JSON.parse(data.toString());
        if (res.status === "done") {
          ws.close();
          resolve({
            content: [
              {
                type: "text" as const,
                text: `[CHATGPT ORACLE RESPONSE (browser)]:\n${fullResponse}`,
              },
            ],
          });
        } else if (res.status === "streaming" && res.text) {
          fullResponse += res.text;
        } else if (res.text) {
          fullResponse += res.text;
        }
      } catch {}
    });

    ws.on("error", () => {
      clearTimeout(timeout);
      resolve(null);
    });

    ws.on("close", () => {
      // If we got a partial response but no 'done' status, still return it
      if (fullResponse) {
        resolve({
          content: [{ type: "text" as const, text: `[CHATGPT ORACLE RESPONSE (browser)]:\n${fullResponse}` }],
        });
      }
    });
  });
}

/**
 * Fallback: send the prompt via the DeepSeek/OpenAI API.
 */
async function tryApiFallback(
  prompt: string,
  systemRole: string | undefined,
  onUpdate: any
): Promise<{ content: { type: "text"; text: string }[] }> {
  const systemPrompt =
    systemRole ||
    "You are the Oracle/Compiler in a hybrid AI system. " +
      "The Orchestrator (the primary coding agent) has encountered a complex bug or error " +
      "and needs your expert review. Provide direct fixes, optimized code blocks, " +
      "or explain the error clearly. Be concise and specific.";

  const apiKey =
    process.env.DEEPSEEK_API_KEY ||
    process.env.OPENAI_API_KEY ||
    process.env.ANTHROPIC_API_KEY ||
    "";
  const baseUrl =
    process.env.OPENAI_BASE_URL?.replace(/\/+$/, "") ||
    process.env.DEEPSEEK_BASE_URL?.replace(/\/+$/, "") ||
    "https://api.deepseek.com/v1";
  const model =
    process.env.ORACLE_MODEL || process.env.CONSULTANT_MODEL || "deepseek-chat";

  if (!apiKey) {
    return {
      content: [
        {
          type: "text" as const,
          text: "[ORACLE UNAVAILABLE]: No API key or WebSocket bridge found. Set DEEPSEEK_API_KEY or start ChatGPT-Connect.",
        },
      ],
    };
  }

  try {
    onUpdate?.({
      content: [
        {
          type: "text" as const,
          text: `Consulting ${model} via API (bridge unavailable)...`,
        },
      ],
    });

    const response = await fetch(`${baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Authorization: `Bearer ${apiKey}`,
      },
      body: JSON.stringify({
        model: model,
        messages: [
          { role: "system", content: systemPrompt },
          { role: "user", content: prompt },
        ],
        max_tokens: 4096,
        temperature: 0.3,
      }),
    });

    if (!response.ok) {
      const errorText = await response.text();
      return {
        content: [
          {
            type: "text" as const,
            text: `[ORACLE ERROR]: API returned ${response.status}: ${errorText}`,
          },
        ],
      };
    }

    const data = (await response.json()) as any;
    const oracleResponse =
      data.choices?.[0]?.message?.content || "[ORACLE: No response content]";

    return {
      content: [
        {
          type: "text" as const,
          text: `[CHATGPT ORACLE RESPONSE]:\n${oracleResponse}`,
        },
      ],
    };
  } catch (error: any) {
    return {
      content: [
        {
          type: "text" as const,
          text: `[ORACLE ERROR]: Connection failed. Error: ${error.message}`,
        },
      ],
    };
  }
}

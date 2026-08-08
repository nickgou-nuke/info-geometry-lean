declare module "@earendil-works/pi-coding-agent" {
  export interface ToolContext {
    name: string;
    label: string;
    description: string;
    promptSnippet?: string;
    promptGuidelines?: string[];
    parameters: any;
    required?: string[];
    execute: (
      toolCallId: string,
      params: Record<string, unknown>,
      signal: AbortSignal,
      onUpdate?: (update: { content: any[] }) => void,
      ctx?: Record<string, unknown>
    ) => Promise<{ content: { type: "text"; text: string }[] }> | { content: { type: "text"; text: string }[] };
  }

  export interface ExtensionAPI {
    registerTool(tool: ToolContext): void;
  }
}

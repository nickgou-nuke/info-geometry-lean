// Type declarations for pi-ai module
declare module "@earendil-works/pi-ai" {
	export type Api = "anthropic" | "openai" | "google" | "custom";
	
	export interface Model<ApiType extends Api = Api> {
		id: string;
		name: string;
		provider: string;
		api: ApiType;
		reasoning?: boolean;
		input?: string[];
		cost?: ModelCost;
		contextWindow?: number;
		maxTokens?: number;
		reasoning?: any;
	}
	
	export interface ModelCost {
		input: number;
		output: number;
		cacheRead?: number;
		cacheWrite?: number;
	}
	
	export interface Message {
		role: "user" | "assistant" | "system" | "toolResult";
		content: string | Content[];
		toolCallId?: string;
		isError?: boolean;
	}
	
	export interface TextContent {
		type: "text";
		text: string;
	}
	
	export interface ImageContent {
		type: "image";
		mimeType: string;
		data: string;
	}
	
	export interface ThinkingContent {
		type: "thinking";
		thinking: string;
		thinkingSignature?: string;
	}
	
	export type Content = TextContent | ImageContent | ThinkingContent;
	
	export interface Tool {
		name: string;
		description: string;
		parameters: any;
	}
	
	export interface ToolCall {
		id: string;
		name: string;
		arguments: any;
		partialJson?: string;
		index?: number;
	}
	
	export interface ToolResultMessage {
		role: "toolResult";
		toolCallId: string;
		content: any[];
		isError?: boolean;
	}
	
	export interface AssistantMessage {
		role: "assistant";
		content: any[];
		api: string;
		provider: string;
		model: string;
		usage: Usage;
		stopReason: StopReason;
		timestamp: number;
		errorMessage?: string;
	}
	
	export interface Usage {
		input: number;
		output: number;
		cacheRead: number;
		cacheWrite: number;
		totalTokens: number;
		cost: { input: number; output: number; cacheRead: number; cacheWrite: number; total: number };
	}
	
	export type StopReason = "stop" | "length" | "toolUse" | "error" | "aborted";
	
	export interface SimpleStreamOptions {
		apiKey?: string;
		maxTokens?: number;
		reasoning?: string;
		thinkingBudgets?: Record<string, number>;
		signal?: AbortSignal;
	}
	
	export interface Context {
		messages: Message[];
		systemPrompt?: string;
		tools?: Tool[];
	}
	
	export interface Api {
		name: string;
		baseUrl?: string;
	}
	
	export interface OAuthCredentials {
		refresh: string;
		access: string;
		expires: number;
	}
	
	export interface OAuthLoginCallbacks {
		onAuth: (params: { url: string }) => void;
		onPrompt: (params: { message: string }) => Promise<string>;
	}
	
	export interface AssistantMessageEventStream {
		queue: (event: any) => void;
		waiting: boolean;
		done: (reason: "stop" | "length" | "toolUse", message: AssistantMessage) => void;
		finalResultPromise: Promise<AssistantMessage>;
		push: (event: any) => void;
		end: () => void;
	}
	
	export function createAssistantMessageEventStream(): AssistantMessageEventStream;
	export function calculateCost(model: Model<any>, usage: Usage): void;
	
	export type ModelProvider = {
		baseUrl?: string;
		apiKey?: string;
		models: Array<Model<any>>;
		oauth?: {
			name: string;
			login: (callbacks: OAuthLoginCallbacks) => Promise<OAuthCredentials>;
			refreshToken: (credentials: OAuthCredentials) => Promise<OAuthCredentials>;
			getApiKey: (cred: OAuthCredentials) => string;
		};
		streamSimple: (model: Model<any>, context: Context, options?: SimpleStreamOptions) => AssistantMessageEventStream;
	};
}
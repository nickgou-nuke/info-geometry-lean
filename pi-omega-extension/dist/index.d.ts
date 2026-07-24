/**
 * Pi-Omega Extension: Multi-Provider LLM + Browser Harness + Oracle + Lean 4
 * Production-hardened version with proper error handling, connection pooling, and observability.
 */
interface BrowserHarnessConfig {
    host?: string;
    port?: number;
    wsUrl?: string;
    connectionTimeoutMs?: number;
    commandTimeoutMs?: number;
}
interface LeanConfig {
    repoRoot: string;
    lakeTimeoutMs?: number;
}
interface OracleConfig {
    browserConfig: BrowserHarnessConfig;
    defaultTimeoutMs?: number;
    maxRetries?: number;
}
type LogLevel = "debug" | "info" | "warn" | "error";
declare class Logger {
    private component;
    private minLevel;
    private levelOrder;
    constructor(component: string, minLevel?: LogLevel);
    private shouldLog;
    private log;
    debug(message: string, metadata?: Record<string, unknown>): void;
    info(message: string, metadata?: Record<string, unknown>): void;
    warn(message: string, metadata?: Record<string, unknown>): void;
    error(message: string, metadata?: Record<string, unknown>): void;
    child(subComponent: string): Logger;
}
declare class BrowserHarnessClient {
    private ws;
    private messageId;
    private pending;
    private config;
    private logger;
    private connected;
    private messageHandler;
    constructor(config?: BrowserHarnessConfig, logger?: Logger);
    connect(wsUrl?: string): Promise<void>;
    private findTargetTab;
    private handleMessage;
    private nextId;
    send(params: Record<string, unknown>): Promise<unknown>;
    evaluate(expression: string, awaitPromise?: boolean): Promise<unknown>;
    click(selector: string): Promise<void>;
    type(selector: string, text: string): Promise<void>;
    waitForSelector(selector: string, timeout?: number): Promise<boolean>;
    sendKeys(key: string): Promise<void>;
    screenshot(): Promise<string | undefined>;
    sendPrompt(prompt: string): Promise<void>;
    waitForResponse(timeout?: number): Promise<string>;
    close(): Promise<void>;
    isConnected(): boolean;
}
declare class BrowserPool {
    private pools;
    private config;
    private logger;
    private maxPoolSize;
    constructor(config: BrowserHarnessConfig, maxPoolSize?: number, logger?: Logger);
    acquire(key?: string): Promise<BrowserHarnessClient>;
    release(key: string | undefined, client: BrowserHarnessClient): Promise<void>;
    getStats(): Record<string, unknown>;
    closeAll(): Promise<void>;
}
interface OracleResponse {
    valid?: boolean;
    proofSketch?: string;
    sorries?: string[];
    notes?: string;
    rawResponse?: string;
    summary?: string;
    [key: string]: unknown;
}
declare class OracleClient {
    private pool;
    private config;
    private logger;
    constructor(pool: BrowserPool, config: OracleConfig, logger?: Logger);
    queryChatGPT(prompt: string, options?: {
        timeout?: number;
    }): Promise<OracleResponse>;
    queryGoogleAI(prompt: string, options?: {
        timeout?: number;
    }): Promise<OracleResponse>;
    private parseResponse;
}
interface LeanResult {
    success: boolean;
    output: string;
    errors: string[];
}
declare class LeanTools {
    private config;
    private logger;
    constructor(config: LeanConfig, logger?: Logger);
    private runCommand;
    build(module: string): Promise<LeanResult>;
    checkFile(file: string): Promise<LeanResult>;
    runScript(script: string): Promise<LeanResult>;
    extractTheorems(modulePath: string): Promise<Array<{
        name: string;
        statement: string;
        file: string;
        line: number;
    }>>;
}
interface ReasoningStep {
    type: "observe" | "hypothesize" | "verify" | "conclude";
    content: string;
    confidence: number;
    evidence?: unknown[];
}
declare class ReasoningEngine {
    private logger;
    constructor(logger?: Logger);
    reason(goal: string, context: Record<string, unknown>): Promise<ReasoningStep[]>;
    private observe;
    private hypothesize;
    private verify;
    private conclude;
}
interface HiveMemoryConfig {
    url: string;
    db: string;
    user: string;
    pass: string;
    maxRetries?: number;
    retryDelayMs?: number;
}
declare class HiveMemory {
    private config;
    private db;
    private logger;
    constructor(config: HiveMemoryConfig, logger?: Logger);
    connect(): Promise<void>;
    storeThought(thought: Record<string, unknown>): Promise<void>;
    queryThoughts(aql: string, bindVars?: Record<string, unknown>): Promise<unknown[]>;
    getCausalCone(declName: string, depth?: number): Promise<unknown>;
}
export default function (pi: any): void;
export { BrowserHarnessClient, BrowserPool, OracleClient, LeanTools, ReasoningEngine, HiveMemory, Logger };
//# sourceMappingURL=index.d.ts.map
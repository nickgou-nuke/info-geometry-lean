"use strict";
var __create = Object.create;
var __defProp = Object.defineProperty;
var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
var __getOwnPropNames = Object.getOwnPropertyNames;
var __getProtoOf = Object.getPrototypeOf;
var __hasOwnProp = Object.prototype.hasOwnProperty;
var __export = (target, all) => {
  for (var name in all)
    __defProp(target, name, { get: all[name], enumerable: true });
};
var __copyProps = (to, from, except, desc) => {
  if (from && typeof from === "object" || typeof from === "function") {
    for (let key of __getOwnPropNames(from))
      if (!__hasOwnProp.call(to, key) && key !== except)
        __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
  }
  return to;
};
var __toESM = (mod, isNodeMode, target) => (target = mod != null ? __create(__getProtoOf(mod)) : {}, __copyProps(
  // If the importer is in node compatibility mode or this is not an ESM
  // file that has been converted to a CommonJS file using a Babel-
  // compatible transform (i.e. "__esModule" has not been set), then set
  // "default" to the CommonJS "module.exports" for node compatibility.
  isNodeMode || !mod || !mod.__esModule ? __defProp(target, "default", { value: mod, enumerable: true }) : target,
  mod
));
var __toCommonJS = (mod) => __copyProps(__defProp({}, "__esModule", { value: true }), mod);

// src/extension.ts
var extension_exports = {};
__export(extension_exports, {
  activate: () => activate,
  deactivate: () => deactivate
});
module.exports = __toCommonJS(extension_exports);
var vscode = __toESM(require("vscode"));
var fs = __toESM(require("fs"));
var path = __toESM(require("path"));
var import_child_process = require("child_process");
var BlueprintNode = class extends vscode.TreeItem {
  children;
  blueprintData;
  // Store the original blueprint data
  isFormalized;
  constructor(label, children = [], collapsibleState = vscode.TreeItemCollapsibleState.Collapsed, blueprintData = null) {
    super(label, children.length > 0 ? collapsibleState : vscode.TreeItemCollapsibleState.None);
    this.children = children;
    this.blueprintData = blueprintData;
    this.isFormalized = blueprintData ? this.calculateFormalizationStatus(blueprintData) : false;
    this.contextValue = this.isFormalized ? "formalizedNode" : "unformalizedNode";
    if (this.blueprintData && this.blueprintData.stmt_type) {
      this.iconPath = new vscode.ThemeIcon(
        this.isFormalized ? "check" : "circle-outline",
        this.isFormalized ? void 0 : new vscode.ThemeColor("problemsWarningIcon.foreground")
      );
    }
  }
  calculateFormalizationStatus(data) {
    return !!(data.leanok || data.fully_proved || data.lean_declarations && data.lean_declarations.length > 0);
  }
};
var BlueprintTreeDataProvider = class {
  _onDidChangeTreeData = new vscode.EventEmitter();
  onDidChangeTreeData = this._onDidChangeTreeData.event;
  rootNodes = [];
  showOnlyUnformalized = false;
  statusFilter = /* @__PURE__ */ new Set(["formalized", "non-formalized"]);
  _searchText = "";
  refresh(nodes) {
    this.rootNodes = nodes;
    this._onDidChangeTreeData.fire();
  }
  setFilter(showOnlyUnformalized) {
    this.showOnlyUnformalized = showOnlyUnformalized;
    this._onDidChangeTreeData.fire();
  }
  setStatusFilter(statuses) {
    this.statusFilter = new Set(statuses);
    this._onDidChangeTreeData.fire();
  }
  getTreeItem(element) {
    if (!element.isFormalized && element.blueprintData && element.blueprintData.stmt_type) {
      element.command = {
        title: "Select for Formalization",
        command: "leanblueprintcopilot.selectNodeForFormalization",
        arguments: [element.blueprintData]
      };
    }
    return element;
  }
  getChildren(element) {
    if (!element) {
      return Promise.resolve(this.filterNodesByStatus(this.rootNodes));
    }
    return Promise.resolve(this.filterNodesByStatus(element.children));
  }
  filterUnformalizedNodes(nodes) {
    const result = [];
    for (const node of nodes) {
      if (!node.isFormalized && node.blueprintData && node.blueprintData.stmt_type) {
        result.push(node);
      } else if (node.children.length > 0) {
        const unformalizedChildren = this.filterUnformalizedNodes(node.children);
        if (unformalizedChildren.length > 0) {
          const filteredNode = new BlueprintNode(
            node.label,
            unformalizedChildren,
            vscode.TreeItemCollapsibleState.Expanded,
            node.blueprintData
          );
          filteredNode.description = `${unformalizedChildren.length} unformalized`;
          filteredNode.iconPath = new vscode.ThemeIcon("folder");
          result.push(filteredNode);
        }
      }
    }
    return result;
  }
  filterNodesByStatus(nodes) {
    const result = [];
    const showFormalized = this.statusFilter.has("formalized");
    const showNonFormalized = this.statusFilter.has("non-formalized");
    for (const node of nodes) {
      const isFormalized = node.isFormalized;
      if (!showFormalized && showNonFormalized) {
        if (!isFormalized) {
          const filteredChildren = this.filterNodesByStatus(node.children);
          const filteredNode = new BlueprintNode(
            node.label,
            filteredChildren,
            filteredChildren.length > 0 ? vscode.TreeItemCollapsibleState.Expanded : vscode.TreeItemCollapsibleState.None,
            node.blueprintData
          );
          filteredNode.description = node.description;
          filteredNode.iconPath = node.iconPath;
          filteredNode.command = node.command;
          filteredNode.tooltip = node.tooltip;
          result.push(filteredNode);
        } else if (node.children.length > 0) {
          const filteredChildren = this.filterNodesByStatus(node.children);
          if (filteredChildren.length > 0) {
            const filteredNode = new BlueprintNode(
              node.label,
              filteredChildren,
              vscode.TreeItemCollapsibleState.Expanded,
              node.blueprintData
            );
            filteredNode.description = node.description;
            filteredNode.iconPath = new vscode.ThemeIcon("folder");
            filteredNode.tooltip = node.tooltip;
            result.push(filteredNode);
          }
        }
      } else {
        if (isFormalized && showFormalized || !isFormalized && showNonFormalized) {
          const filteredChildren = this.filterNodesByStatus(node.children);
          const filteredNode = new BlueprintNode(
            node.label,
            filteredChildren,
            filteredChildren.length > 0 ? vscode.TreeItemCollapsibleState.Expanded : vscode.TreeItemCollapsibleState.None,
            node.blueprintData
          );
          filteredNode.description = node.description;
          filteredNode.iconPath = node.iconPath;
          filteredNode.command = node.command;
          filteredNode.tooltip = node.tooltip;
          result.push(filteredNode);
        } else if (node.children.length > 0) {
          const filteredChildren = this.filterNodesByStatus(node.children);
          if (filteredChildren.length > 0) {
            const filteredNode = new BlueprintNode(
              node.label,
              filteredChildren,
              vscode.TreeItemCollapsibleState.Expanded,
              node.blueprintData
            );
            filteredNode.description = node.description;
            filteredNode.iconPath = new vscode.ThemeIcon("folder");
            filteredNode.tooltip = node.tooltip;
            result.push(filteredNode);
          }
        }
      }
    }
    return result;
  }
  // Add searchText and setSearchText to the provider
  setSearchText(text) {
    this._searchText = text;
    this._onDidChangeTreeData.fire();
  }
};
function activate(context) {
  async function installLeanblueprint(contextFolder) {
    const isWindows = process.platform === "win32";
    function execPromise(cmd, options = {}) {
      return new Promise((resolve, reject) => {
        (0, import_child_process.exec)(cmd, { ...options, shell: isWindows ? "cmd.exe" : "/bin/bash" }, (error, stdout, stderr) => {
          if (error) {
            reject({ stdout, stderr });
          } else {
            resolve({ stdout, stderr });
          }
        });
      });
    }
    function isPackageInstalled(pkg) {
      if (isWindows) {
        return new Promise((resolve) => {
          (0, import_child_process.exec)(`where ${pkg}`, (error) => {
            resolve(!error);
          });
        });
      } else {
        return new Promise((resolve) => {
          (0, import_child_process.exec)(`dpkg -s ${pkg}`, (error) => {
            resolve(!error);
          });
        });
      }
    }
    return await vscode.window.withProgress({
      location: vscode.ProgressLocation.Notification,
      title: "Setting up Lean Blueprint Python environment...",
      cancellable: false
    }, async (progress) => {
      progress.report({ message: "Checking system dependencies..." });
      try {
        const pkgs = [];
        if (!await isPackageInstalled("graphviz")) {
          pkgs.push("graphviz");
        }
        if (!isWindows && !await isPackageInstalled("libgraphviz-dev")) {
          pkgs.push("libgraphviz-dev");
        }
        if (!await isPackageInstalled(isWindows ? "python" : "python3")) {
          pkgs.push(isWindows ? "python" : "python3");
        }
        if (!isWindows && !await isPackageInstalled("python3-venv")) {
          pkgs.push("python3-venv");
        }
        if (!await isPackageInstalled(isWindows ? "pip" : "python3-pip")) {
          pkgs.push(isWindows ? "pip" : "python3-pip");
        }
        if (pkgs.length > 0) {
          const terminal = vscode.window.createTerminal({ name: "Install System Dependencies" });
          terminal.show();
          if (isWindows) {
            vscode.window.showWarningMessage(
              `Please install the following dependencies manually: ${pkgs.join(", ")}.
Visit https://pygraphviz.github.io/documentation/stable/install.html#windows for Graphviz instructions.`
            );
          } else {
            terminal.sendText(`sudo apt update && sudo apt install -y ${pkgs.join(" ")}`);
            vscode.window.showWarningMessage(
              `Please complete the installation of system dependencies in the opened terminal, then retry.`
            );
          }
          return false;
        }
      } catch (e) {
        vscode.window.showWarningMessage(
          isWindows ? "Failed to check/install system dependencies. Please install Python, pip, and Graphviz manually. See https://pygraphviz.github.io/documentation/stable/install.html#windows" : "Failed to check/install system dependencies. If you are using a debian-based environment, please run the following command in your terminal, then retry:\nsudo apt update && sudo apt install -y graphviz libgraphviz-dev python3-pip. Otherwise, please check https://pygraphviz.github.io/documentation/stable/install.html"
        );
        return false;
      }
      progress.report({ message: "Creating Python virtual environment..." });
      const pythonDir = path.join(__dirname, "..", "python");
      const venvDir = path.join(pythonDir, ".venv");
      const pyprojectPath = path.join(pythonDir, "pyproject.toml");
      if (!fs.existsSync(pyprojectPath)) {
        vscode.window.showErrorMessage("pyproject.toml not found in python directory.");
        return false;
      }
      if (!fs.existsSync(venvDir)) {
        try {
          await execPromise(`${isWindows ? "python" : "python3"} -m venv .venv`, { cwd: pythonDir });
        } catch (e) {
          vscode.window.showErrorMessage("Failed to create Python virtual environment: " + (e.stderr || e.stdout || e.message || JSON.stringify(e)));
          return false;
        }
      }
      const venvActivate = isWindows ? path.join(venvDir, "Scripts", "activate.bat") : path.join(venvDir, "bin", "activate");
      const uvPath = isWindows ? path.join(venvDir, "Scripts", "uv.exe") : path.join(venvDir, "bin", "uv");
      const uvInstalled = fs.existsSync(uvPath);
      if (!uvInstalled) {
        progress.report({ message: "Installing uv in the virtual environment..." });
        try {
          if (isWindows) {
            await execPromise(`call "${venvActivate}" && pip install uv`, { cwd: pythonDir });
          } else {
            await execPromise(`. "${venvActivate}" && pip install uv`, { cwd: pythonDir });
          }
        } catch (e) {
          vscode.window.showErrorMessage("Failed to install uv in venv: " + (e.stderr || e.stdout || e.message || JSON.stringify(e)));
          return false;
        }
      }
      progress.report({ message: "Installing Python dependencies with uv sync..." });
      try {
        if (isWindows) {
          await execPromise(`call "${venvActivate}" && uv sync`, { cwd: pythonDir });
        } else {
          await execPromise(`. "${venvActivate}" && uv sync`, { cwd: pythonDir, shell: "/bin/bash" });
        }
      } catch (e) {
        vscode.window.showErrorMessage("Failed to install Python dependencies with uv sync: " + (e.stderr || e.stdout || e.message || JSON.stringify(e)));
        return false;
      }
      progress.report({ message: "Lean Blueprint is ready!" });
      return true;
    });
  }
  const createBlueprintDisposable = vscode.commands.registerCommand("leanblueprintcopilot.createBlueprintProject", async () => {
    const folderUri = await vscode.window.showOpenDialog({
      canSelectFolders: true,
      canSelectFiles: false,
      canSelectMany: false,
      openLabel: "Select folder for Lean blueprint project"
    });
    if (!folderUri || folderUri.length === 0) {
      return;
    }
    const targetFolder = folderUri[0].fsPath;
    const projectName = await vscode.window.showInputBox({
      prompt: "Enter project name",
      placeHolder: "my_project"
    });
    if (!projectName) {
      return;
    }
    const ok = await installLeanblueprint(targetFolder);
    if (!ok) {
      return;
    }
    const pythonDir = path.join(__dirname, "..", "python");
    const venvDir = path.join(pythonDir, ".venv");
    const venvLeanblueprint = path.join(venvDir, "bin", "leanblueprint");
    const venvActivate = path.join(venvDir, "bin", "activate");
    const lakeCommand = `lake init ${projectName}`;
    const blueprintCommand = `. ${venvActivate} && "${venvLeanblueprint}" new`;
    const terminal = vscode.window.createTerminal({ name: "Lean Blueprint Init" });
    terminal.show();
    terminal.sendText(`cd "${targetFolder}" && ${lakeCommand} && ${blueprintCommand}`);
    vscode.window.showInformationMessage(`Instantiating the project`);
    await vscode.commands.executeCommand("vscode.openFolder", vscode.Uri.file(targetFolder), false);
  });
  const parseBlueprintDisposable = vscode.commands.registerCommand("leanblueprintcopilot.parseBlueprintProject", async () => {
    const folder = getWorkspaceFolder();
    if (!folder) {
      vscode.window.showErrorMessage("No workspace folder found.");
      return;
    }
    const ok = await installLeanblueprint(folder);
    if (!ok) {
      return;
    }
    const pythonDir = path.join(__dirname, "..", "python");
    const venvActivate = path.join(pythonDir, ".venv", "bin", "activate");
    const blueprintTraceDir = path.join(folder, ".cache", "blueprint_trace");
    if (!fs.existsSync(blueprintTraceDir)) {
      fs.mkdirSync(blueprintTraceDir, { recursive: true });
    }
    const blueprintDataJsonl = path.join(blueprintTraceDir, "blueprint_to_lean.jsonl");
    const outputChannel = vscode.window.createOutputChannel("Lean Blueprint Extraction");
    await vscode.window.withProgress({ location: vscode.ProgressLocation.Notification, title: "Parsing Blueprint project..." }, async () => {
      return new Promise((resolve) => {
        outputChannel.clear();
        outputChannel.show(true);
        const child = require("child_process").spawn(
          "bash",
          ["-c", `. "${venvActivate}" && lean-blueprint-extract-local --project-dir "${folder}"`],
          { cwd: folder, env: process.env }
        );
        let stdout = "";
        let stderr = "";
        child.stdout.on("data", (data) => {
          const str = data.toString();
          stdout += str;
          outputChannel.append(str);
        });
        child.stderr.on("data", (data) => {
          const str = data.toString();
          stderr += str;
          outputChannel.append(str);
        });
        child.on("close", (code) => {
          if (code !== 0) {
            vscode.window.showErrorMessage("Error running extractor.py (see logs for details)");
            resolve();
            return;
          }
          const treeNodes = loadBlueprintTreeFromJsonl(blueprintDataJsonl);
          if (treeNodes) {
            blueprintTreeProvider.refresh(treeNodes);
          }
          resolve();
        });
      });
    });
  });
  const selectNodeForFormalizationDisposable = vscode.commands.registerCommand("leanblueprintcopilot.selectNodeForFormalization", async (blueprintData) => {
    if (!blueprintData) {
      vscode.window.showErrorMessage("No blueprint data provided for formalization.");
      return;
    }
    const nodeInfo = `Selected node for formalization:
Label: ${blueprintData.label || "N/A"}
Type: ${blueprintData.stmt_type || "N/A"}
Text: ${blueprintData.processed_text || "N/A"}`;
    const action = await vscode.window.showInformationMessage(
      nodeInfo,
      { modal: true },
      "Start Formalization",
      "View Context"
    );
    if (action === "Start Formalization") {
      await vscode.commands.executeCommand("workbench.action.chat.open");
      const formalizationPrompt = `I need help formalizing this blueprint node in Lean:

**Label**: ${blueprintData.label || "N/A"}
**Type**: ${blueprintData.stmt_type || "N/A"}
**Statement**: ${blueprintData.processed_text || "N/A"}

${blueprintData.proof ? `**Proof sketch**: ${blueprintData.proof.text || "N/A"}` : ""}

Please help me formalize this ${blueprintData.stmt_type || "statement"} in Lean. Consider the existing project structure and dependencies.`;
      await vscode.env.clipboard.writeText(formalizationPrompt);
      vscode.window.showInformationMessage("Formalization prompt copied to clipboard. Paste it in the chat to start!");
    } else if (action === "View Context") {
      const contextDoc = await vscode.workspace.openTextDocument({
        content: JSON.stringify(blueprintData, null, 2),
        language: "json"
      });
      await vscode.window.showTextDocument(contextDoc);
    }
  });
  const formalizeNodeDisposable = vscode.commands.registerCommand("leanblueprintcopilot.formalizeNode", async (node) => {
    if (node && node.blueprintData) {
      await vscode.commands.executeCommand("leanblueprintcopilot.selectNodeForFormalization", node.blueprintData);
    } else {
      vscode.window.showErrorMessage("No blueprint data available for this node.");
    }
  });
  function runLeanblueprintCommandInWorkspace(command, terminalName) {
    const folder = getWorkspaceFolder();
    if (!folder) {
      vscode.window.showErrorMessage("No workspace folder found. Please open a folder in VS Code.");
      return;
    }
    const pythonDir = path.join(__dirname, "..", "python");
    const venvDir = path.join(pythonDir, ".venv");
    const venvLeanblueprint = path.join(venvDir, "bin", "leanblueprint");
    const venvActivate = path.join(venvDir, "bin", "activate");
    const cmd = `. ${venvActivate} && "${venvLeanblueprint}" ${command}`;
    const terminal = vscode.window.createTerminal({ name: terminalName });
    terminal.show();
    terminal.sendText(`cd "${folder}" && ${cmd}`);
    vscode.window.showInformationMessage(`Running 'leanblueprint ${command}'`);
  }
  context.subscriptions.push(
    vscode.commands.registerCommand("leanblueprintcopilot.buildPdf", () => {
      runLeanblueprintCommandInWorkspace("pdf", "Lean Blueprint PDF");
    }),
    vscode.commands.registerCommand("leanblueprintcopilot.buildWeb", () => {
      runLeanblueprintCommandInWorkspace("web", "Lean Blueprint Web");
    }),
    vscode.commands.registerCommand("leanblueprintcopilot.checkDecls", () => {
      runLeanblueprintCommandInWorkspace("checkdecls", "Lean Blueprint Check Decls");
    }),
    vscode.commands.registerCommand("leanblueprintcopilot.buildAll", () => {
      runLeanblueprintCommandInWorkspace("all", "Lean Blueprint All");
    }),
    vscode.commands.registerCommand("leanblueprintcopilot.serve", async () => {
      runLeanblueprintCommandInWorkspace("serve", "Lean Blueprint Serve");
      const panel = vscode.window.createWebviewPanel(
        "leanblueprintServe",
        "Lean Blueprint Website",
        vscode.ViewColumn.Beside,
        {
          enableScripts: true,
          retainContextWhenHidden: true
        }
      );
      const url = "http://0.0.0.0:8000/";
      panel.webview.html = `
				<!DOCTYPE html>
				<html lang="en">
				<head>
					<meta charset="UTF-8">
					<meta http-equiv="Content-Security-Policy" content="default-src 'none'; frame-src http://0.0.0.0:8000 http://localhost:8000; script-src 'unsafe-inline'; style-src 'unsafe-inline';">
					<title>Lean Blueprint Website</title>
					<style>body, html { margin: 0; padding: 0; height: 100%; } iframe { width: 100vw; height: 100vh; border: none; }</style>
				</head>
				<body>
					<iframe src="${url}"></iframe>
					<div style="position:absolute;top:0;left:0;width:100vw;height:100vh;pointer-events:none;"></div>
				</body>
				</html>
			`;
    })
  );
  const blueprintTreeProvider = new BlueprintTreeDataProvider();
  vscode.window.registerTreeDataProvider("leanblueprintcopilot.blueprintTree", blueprintTreeProvider);
  const didChangeEmitter = new vscode.EventEmitter();
  const registerMcpServerDisposable = vscode.lm.registerMcpServerDefinitionProvider("LeanBlueprintCopilot", {
    onDidChangeMcpServerDefinitions: didChangeEmitter.event,
    provideMcpServerDefinitions: async () => {
      return await vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Starting Lean Blueprint MCP server...",
        cancellable: false
      }, async (progress) => {
        const folder = getWorkspaceFolder();
        if (!folder) {
          vscode.window.showErrorMessage("No workspace folder found.");
          return;
        }
        const ok = await installLeanblueprint(folder);
        if (!ok) {
          return;
        }
        const pythonDir = path.join(__dirname, "..", "python");
        const venvActivate = path.join(pythonDir, ".venv", "bin", "activate");
        const port = "5000";
        let servers = [];
        servers.push(new vscode.McpStdioServerDefinition(
          "Lean Blueprint Copilot",
          "bash",
          ["-c", `. "${venvActivate}" && lean-blueprint-mcp --port ${port}`],
          { "LEAN_BLUEPRINT_PROJECT_DIR": folder }
        ));
        return servers;
      });
    },
    resolveMcpServerDefinition: async (server) => {
      return server;
    }
  });
  context.subscriptions.push(createBlueprintDisposable, parseBlueprintDisposable, selectNodeForFormalizationDisposable, formalizeNodeDisposable, registerMcpServerDisposable);
  const filterBlueprintTreeDisposable = vscode.commands.registerCommand("leanblueprintcopilot.filterBlueprintTree", async () => {
    const options = [
      { label: "Formalized", picked: blueprintTreeProvider["statusFilter"].has("formalized"), status: "formalized" },
      { label: "Non-formalized", picked: blueprintTreeProvider["statusFilter"].has("non-formalized"), status: "non-formalized" }
    ];
    const selected = await vscode.window.showQuickPick(options, {
      canPickMany: true,
      placeHolder: "Show nodes with status..."
    });
    if (selected && selected.length > 0) {
      const statuses = selected.map((s) => s.status);
      blueprintTreeProvider.setStatusFilter(statuses);
    }
  });
  context.subscriptions.push(filterBlueprintTreeDisposable);
  let searchText = "";
  const searchBlueprintTreeDisposable = vscode.commands.registerCommand("leanblueprintcopilot.searchBlueprintTree", async () => {
    const input = await vscode.window.showInputBox({
      prompt: "Search blueprint nodes by label or text",
      value: searchText
    });
    if (input !== void 0) {
      searchText = input;
      blueprintTreeProvider.setSearchText(searchText);
    }
  });
  context.subscriptions.push(searchBlueprintTreeDisposable);
  function buildTree(nodes) {
    return nodes.filter((n) => n.label !== null).map((n) => {
      const label = n.title || n.label || n.stmt_type || n.processed_text || "Item";
      let children = [];
      if (n.proof) {
        children.push(...buildTree([n.proof]));
      }
      if (n.children) {
        children.push(...buildTree(n.children));
      }
      if (n.lean_declarations && Array.isArray(n.lean_declarations)) {
        n.lean_declarations.forEach((decl) => {
          if (decl.real_file && decl.range && decl.range.start && typeof decl.range.start.line === "number") {
            const leanLabel = `Lean: ${decl.full_name}`;
            const leanNode = new BlueprintNode(leanLabel, [], vscode.TreeItemCollapsibleState.None);
            leanNode.command = {
              title: `Go to Lean: ${decl.full_name}`,
              command: "vscode.open",
              arguments: [vscode.Uri.file(decl.real_file).with({ fragment: `L${decl.range.start.line + 1}` })]
            };
            leanNode.tooltip = decl.real_file + `:L${decl.range.start.line + 1}`;
            children.push(leanNode);
          }
        });
      }
      const collapsibleState = children.length > 0 ? vscode.TreeItemCollapsibleState.Collapsed : vscode.TreeItemCollapsibleState.None;
      const node = new BlueprintNode(label, children, collapsibleState, n);
      const info = { ...n };
      delete info.children;
      delete info.proof;
      if (n.lean_names && Array.isArray(n.lean_names) && n.lean_names.length > 0) {
        node.description = `Lean: ${n.lean_names.join(", ")}`;
      }
      if (n.label) {
        node.command = {
          title: "Go to Blueprint Declaration",
          command: "workbench.action.findInFiles",
          arguments: [{ query: n.label }]
        };
      }
      node.tooltip = JSON.stringify(info, null, 2);
      return node;
    });
  }
  function loadBlueprintTreeFromJsonl(jsonlPath) {
    if (!fs.existsSync(jsonlPath)) {
      return void 0;
    }
    try {
      const fileContent = fs.readFileSync(jsonlPath, "utf8");
      const data = fileContent.split(/\r?\n/).filter((line) => line.trim().length > 0).map((line) => {
        try {
          return JSON.parse(line);
        } catch (e) {
          return null;
        }
      }).filter((obj) => obj !== null);
      return buildTree(data);
    } catch (e) {
      vscode.window.showErrorMessage("Failed to parse `blueprint_to_lean.jsonl`");
      return void 0;
    }
  }
  const workspaceFolder = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (workspaceFolder) {
    const blueprintDir = require("path").join(workspaceFolder, "blueprint");
    const blueprintDataJsonl = require("path").join(workspaceFolder, ".cache", "blueprint_trace", "blueprint_to_lean.jsonl");
    if (fs.existsSync(blueprintDir) && !fs.existsSync(blueprintDataJsonl)) {
      vscode.window.showInformationMessage(
        "Blueprint project detected. Parse the project to enable the tree view.",
        "Parse Now"
      ).then((action) => {
        if (action === "Parse Now") {
          vscode.commands.executeCommand("leanblueprintcopilot.parseBlueprintProject");
        }
      });
    }
    const treeNodes = loadBlueprintTreeFromJsonl(blueprintDataJsonl);
    if (treeNodes) {
      blueprintTreeProvider.refresh(treeNodes);
    }
  }
}
function deactivate() {
}
function getWorkspaceFolder() {
  const folders = vscode.workspace.workspaceFolders;
  if (!folders || folders.length === 0) {
    return void 0;
  }
  return folders[0].uri.fsPath;
}
// Annotate the CommonJS export names for ESM import in node:
0 && (module.exports = {
  activate,
  deactivate
});
//# sourceMappingURL=extension.js.map

import os
import json
import base64
import re
from urllib.request import Request, urlopen

# Configuration
ENDPOINT = os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530").rstrip("/")
DATABASE = os.environ.get("ARANGO_DATABASE", "infogeometry")
USER = os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME", "root")
PASSWORD = os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD", "alexandria_root")

def query_arango(aql, bind_vars=None):
    token = base64.b64encode(f"{USER}:{PASSWORD}".encode()).decode("ascii")
    url = f"{ENDPOINT}/_db/{DATABASE}/_api/cursor"
    payload = {"query": aql, "bindVars": bind_vars or {}}
    req = Request(url, data=json.dumps(payload).encode("utf-8"), method="POST")
    req.add_header("Authorization", f"Basic {token}")
    req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        print(f"Error querying ArangoDB: {e}")
        return None

# Unicode mapping to LaTeX math equivalents
UNICODE_MAP = {
    "\u2102": r"\mathbb{C} ",
    "\u211d": r"\mathbb{R} ",
    "\u2124": r"\mathbb{Z} ",
    "\u03c3": r"\sigma ",
    "\u21a6": r"\mapsto ",
    "\u2020": r"^\dagger ",
    "²": r"^2 ",
    "³": r"^3 ",
    "⁴": r"^4 ",
    "\u2081": r"_1 ",
    "\u2082": r"_2 ",
    "\u2083": r"_3 ",
    "\u00d7": r"\times ",
    "\u2264": r"\le ",
    "\u2265": r"\ge ",
    "\u2260": r"\ne ",
    "\u2295": r"\oplus ",
    "\u2297": r"\otimes ",
    "\u2192": r"\to ",
    "\u03b2": r"\beta ",
    "\u03b5": r"\varepsilon ",
    "\u03c8": r"\psi ",
    "\u039b": r"\Lambda ",
    "\u03bb": r"\lambda ",
    "∑": r"\sum ",
    "ᵢ": r"_i ",
    "δ": r"\delta ",
    "μ": r"\mu ",
    "ν": r"\nu ",
    "π": r"\pi ",
    "∞": r"\infty ",
    "∈": r"\in ",
    "⋅": r"\cdot ",
    "∂": r"\partial ",
    "∇": r"\nabla ",
    "∫": r"\int ",
    "¹": r"^1 ",
    "↔": r"\leftrightarrow ",
    "η": r"\eta ",
    "θ": r"\theta ",
    "‖": r"\|",
}

def escape_text_segment(text):
    if not text:
        return ""
    # Map any unicode characters inside the text to math mode equivalents
    for char, latex in UNICODE_MAP.items():
        text = text.replace(char, f"${latex}$")
        
    # Escape basic LaTeX formatting characters in plain text
    text = text.replace("&", r"\&")
    text = text.replace("%", r"\%")
    text = text.replace("#", r"\#")
    text = text.replace("_", r"\_")
    text = text.replace("{", r"\{")
    text = text.replace("}", r"\}")
    text = text.replace("~", r"\textasciitilde{}")
    text = text.replace("^", r"\textasciicircum{}")
    return text

def escape_math_segment(text):
    if not text:
        return ""
    # Map unicode characters to raw LaTeX math equivalents
    for char, latex in UNICODE_MAP.items():
        text = text.replace(char, latex)
    # Keep braces, underscores, and backslashes intact
    return f"${text}$"

def escape_latex(text):
    if not text:
        return ""
        
    # Split by backticks to separate inline math segments
    segments = text.split("`")
    escaped_segments = []
    
    for i, seg in enumerate(segments):
        if i % 2 == 1:
            # Inside backticks (math segment)
            escaped_segments.append(escape_math_segment(seg))
        else:
            # Outside backticks (text segment)
            escaped_segments.append(escape_text_segment(seg))
            
    result = "".join(escaped_segments)
    # Clean up multiple newlines
    result = re.sub(r'\n+', r' \n', result)
    return result.strip()

def main():
    # Load AQL schema
    aql_path = "tools/infra/aql_data_migration.cql"
    if not os.path.exists(aql_path):
        print(f"Error: {aql_path} does not exist.")
        return
    with open(aql_path, "r", encoding="utf-8") as f:
        aql_content = f.read()
    
    # Replace non-ASCII unicode characters inside verbatim block to avoid compilation errors
    aql_content = aql_content.replace("Σ", "Sigma")

    print("Connecting to ArangoDB...")
    # 1. Query LLM submodules
    llm_query = """
    FOR node IN ig_nodes
      FILTER CONTAINS(node.module, 'InfoGeometry.LLM') && node.doc != null && node.doc != ''
      SORT node.module, node.name
      RETURN {name: node.name, kind: node.kind, doc: node.doc, module: node.module}
    """
    
    # 2. Query Geometry / Bridge submodules
    geom_query = """
    FOR node IN ig_nodes
      FILTER (CONTAINS(node.module, 'PauliParavectorBridge') || CONTAINS(node.module, 'HelicalCovering'))
             && node.doc != null && node.doc != ''
      SORT node.module, node.name
      RETURN {name: node.name, kind: node.kind, doc: node.doc, module: node.module}
    """
    
    llm_results = query_arango(llm_query)
    geom_results = query_arango(geom_query)
    
    llm_nodes = llm_results.get("result", []) if llm_results else []
    geom_nodes = geom_results.get("result", []) if geom_results else []
    
    print(f"Retrieved {len(llm_nodes)} LLM nodes and {len(geom_nodes)} Geometry/Bridge nodes.")
    
    # Construct LaTeX content
    latex_content = []
    
    # AQL Section
    latex_content.append(r"\section{Functorial AQL Data Migration Schema}")
    latex_content.append("The algebraic mapping between symbolic Gröbner bases (Macaulay2/SageMath) and target theorem-prover signatures is formalized using the following Functorial Algebraic Query Language (AQL/CQL) schema specification:\n")
    latex_content.append(r"\begin{verbatim}")
    latex_content.append(aql_content.strip())
    latex_content.append(r"\end{verbatim}")
    latex_content.append("\n")

    # Theorem Section
    latex_content.append(r"\section{Verified Theorem and Module Directory}")
    latex_content.append("This section presents a structured, computer-verified directory of definitions, theorems, and mathematical sockets extracted from the repository's semantic graph.\n")
    
    # Group LLM by submodule
    latex_content.append(r"\subsection{InfoGeometry.LLM Submodules}")
    latex_content.append("These declarations formalize the Softmax-KMS equivalence, Llama-4 Krein spin-transport transformer block specification, and the thermodynamic routing mechanisms.\n")
    
    current_module = None
    for node in llm_nodes:
        module_name = node["module"]
        if module_name != current_module:
            if current_module is not None:
                latex_content.append(r"\end{description}")
            current_module = module_name
            escaped_mod = escape_text_segment(module_name)
            latex_content.append(f"\\subsubsection*{{{escaped_mod}}}")
            latex_content.append(r"\begin{description}")
        
        escaped_name = escape_text_segment(node["name"].split(".")[-1])
        escaped_doc = escape_latex(node["doc"])
        kind = escape_text_segment(node["kind"])
        latex_content.append(f"  \\item[\\texttt{{{escaped_name}}}] (\\textit{{{kind}}}) \\\\ {escaped_doc}")
        
    if current_module is not None:
        latex_content.append(r"\end{description}")
        
    # Group Geometry/Bridge
    latex_content.append(r"\subsection{InfoGeometry.Geometry and Cross-Prover Bridge}")
    latex_content.append("These declarations define the spin-momentum couplings, twistor/helical coverings, and Clifford/Hestenes paravector readouts bridging Lean 4 and Isabelle.\n")
    
    current_module = None
    for node in geom_nodes:
        module_name = node["module"]
        if module_name != current_module:
            if current_module is not None:
                latex_content.append(r"\end{description}")
            current_module = module_name
            escaped_mod = escape_text_segment(module_name)
            latex_content.append(f"\\subsubsection*{{{escaped_mod}}}")
            latex_content.append(r"\begin{description}")
            
        escaped_name = escape_text_segment(node["name"].split(".")[-1])
        escaped_doc = escape_latex(node["doc"])
        kind = escape_text_segment(node["kind"])
        latex_content.append(f"  \\item[\\texttt{{{escaped_name}}}] (\\textit{{{kind}}}) \\\\ {escaped_doc}")
        
    if current_module is not None:
        latex_content.append(r"\end{description}")
        
    # Read the original rosetta_stone.tex file
    tex_path = "docs/whitepaper/rosetta_stone.tex"
    if not os.path.exists(tex_path):
        print(f"Error: {tex_path} does not exist.")
        return
        
    with open(tex_path, "r", encoding="utf-8") as f:
        tex_data = f.read()
        
    # Clean any previously injected sections to avoid duplication
    tex_data = re.sub(r"\\section\{Functorial AQL Data Migration Schema\}.*?(?=\\section\{Conclusion\})", "", tex_data, flags=re.DOTALL)
    tex_data = re.sub(r"\\section\{Verified Theorem and Module Directory\}.*?(?=\\section\{Conclusion\})", "", tex_data, flags=re.DOTALL)
        
    # Insert before \section{Conclusion}
    target_section = r"\section{Conclusion}"
    if target_section not in tex_data:
        print("Error: Could not locate \\section{Conclusion} in LaTeX template.")
        return
        
    latex_str = "\n".join(latex_content) + "\n\n"
    new_tex_data = tex_data.replace(target_section, latex_str + target_section)
    
    with open(tex_path, "w", encoding="utf-8") as f:
        f.write(new_tex_data)
        
    print(f"Successfully integrated metadata into {tex_path}!")

if __name__ == "__main__":
    main()

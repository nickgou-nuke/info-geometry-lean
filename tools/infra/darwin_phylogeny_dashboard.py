#!/usr/bin/env python3
"""Build an offline, interactive view of Git lineage and declaration links.

The commit graph is read from Git. Optional commit/declaration JSONL is treated
as annotation data: only rows explicitly marked ``exact_match`` are called
exact; the current habitat bridge remains visibly cohabitation evidence.
Declaration fingerprint values are displayed as candidate identifiers, never
as proof of declaration identity.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def git_commits(since: str, limit: int) -> list[dict]:
    fmt = "%H%x00%P%x00%cI%x00%s%x1e"
    raw = subprocess.check_output(
        ["git", "log", "--all", "--topo-order", f"--since={since}",
         f"--max-count={limit}", f"--format={fmt}"], cwd=ROOT)
    rows = []
    for record in raw.decode("utf-8", errors="replace").split("\x1e"):
        fields = record.strip("\n\0").split("\0", 3)
        if len(fields) != 4 or not fields[0]:
            continue
        sha, parents, authored, subject = fields
        try:
            date = dt.datetime.fromisoformat(authored).date().isoformat()
        except ValueError:
            date = authored[:10]
        rows.append({"sha": sha, "parents": parents.split(), "date": date,
                     "subject": subject, "short": sha[:10]})
    return rows


def load_edges(path: Path | None, allowed: set[str],
               fingerprint_targets: set[str] | None = None,
               fingerprints_per_leaf: int = 12) -> dict[str, dict]:
    result: dict[str, dict] = defaultdict(lambda: {
        "declarations": set(), "modules": set(), "fingerprints": set(),
        "fingerprint_records": [], "exact": 0, "cohabitation": 0})
    fingerprint_targets = fingerprint_targets or set()
    if path is None:
        return result
    with path.open(encoding="utf-8") as source:
        for number, line in enumerate(source, 1):
            if not line.strip():
                continue
            try:
                edge = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSONL at {path}:{number}: {exc}") from exc
            sha = edge.get("commitHash", edge.get("sha"))
            if sha not in allowed:
                continue
            row = result[sha]
            decl = edge.get("declName") or edge.get("declKey")
            module = edge.get("moduleName") or edge.get("modulePath") or edge.get("subsystem")
            if decl:
                row["declarations"].add(str(decl))
            if module:
                row["modules"].add(str(module))
            fingerprint_fields = ("typeFingerprint", "valueFingerprint", "declFingerprint",
                                  "canonicalTypeHash", "canonicalValueHash")
            for field in fingerprint_fields:
                value = edge.get(field)
                if value is not None:
                    row["fingerprints"].add(json.dumps(value, sort_keys=True))
            if sha in fingerprint_targets and len(row["fingerprint_records"]) < fingerprints_per_leaf:
                record = {field: edge[field] for field in
                          ("declKey", "declName", "declKind", "declFile", *fingerprint_fields)
                          if edge.get(field) is not None}
                if any(field in record for field in fingerprint_fields):
                    row["fingerprint_records"].append(record)
            if edge.get("exact_match") is True or edge.get("resolution") == "exact_declaration":
                row["exact"] += 1
            else:
                row["cohabitation"] += 1
    return result


def load_labels(path: Path | None) -> dict[str, list[dict]]:
    labels: dict[str, list[dict]] = {}
    if path is None:
        return labels
    with path.open(encoding="utf-8") as source:
        for number, line in enumerate(source, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid label JSONL at {path}:{number}: {exc}") from exc
            if row.get("sha"):
                labels[str(row["sha"])] = row.get("labels", [])
    return labels


def build_payload(commits: list[dict], annotations: dict[str, dict],
                  labels: dict[str, list[dict]] | None = None) -> dict:
    known = {row["sha"] for row in commits}
    children = {parent for row in commits for parent in row["parents"] if parent in known}
    nodes = []
    monthly = Counter()
    modules = Counter()
    archetypes = Counter()
    labels = labels or {}
    for row in commits:
        ann = annotations.get(row["sha"], {})
        parents = [p for p in row["parents"] if p in known]
        modules_here = sorted(ann.get("modules", ()))
        labels_here = labels.get(row["sha"], [])
        for label in labels_here:
            # Accept the old field while reading cached v2 label artifacts;
            # current producers emit non-hierarchical ``category`` facets.
            archetypes[label.get("category", label.get("species", "Unclassified"))] += 1
        for module in modules_here:
            modules[module] += 1
        monthly[row["date"][:7]] += 1
        nodes.append({"sha": row["sha"], "short": row["short"], "date": row["date"],
                      "subject": row["subject"], "parents": parents,
                      "declarations": len(ann.get("declarations", ())),
                      "fingerprints": len(ann.get("fingerprints", ())),
                      "fingerprint_values": ann.get("fingerprint_records", []),
                      "is_leaf": row["sha"] not in children,
                      "exact": ann.get("exact", 0), "cohabitation": ann.get("cohabitation", 0),
                      "modules": modules_here, "labels": labels_here})
    return {"nodes": nodes, "months": sorted(monthly.items()),
            "modules": modules.most_common(30), "archetypes": archetypes.most_common(),
            "generated": dt.datetime.now(dt.timezone.utc).isoformat()}


PAGE = r'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Repository evolution — commit lineage and declaration fingerprints</title>
<style>
:root{color-scheme:dark;--bg:#0b1020;--panel:#121a2d;--line:#263550;--ink:#e8eef9;--muted:#9eacc4;--teal:#65dec2;--gold:#f2c66d;--red:#fb8d91}*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.5 system-ui,sans-serif}main{max-width:1440px;margin:auto;padding:28px}h1{font-size:clamp(24px,4vw,38px);margin:0 0 8px}h2{font-size:18px;margin:0 0 14px}.sub,.note{color:var(--muted)}.grid{display:grid;grid-template-columns:2fr 1fr;gap:16px;margin-top:20px}.card{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:18px;min-width:0}.wide{grid-column:1/-1}.stats{display:flex;gap:10px;flex-wrap:wrap;margin:18px 0}.stat{background:var(--panel);border:1px solid var(--line);padding:12px 15px;border-radius:10px;min-width:145px}.stat b{display:block;font-size:23px}.plot{height:300px;position:relative}canvas{width:100%;height:100%;display:block}.legend{font-size:12px;color:var(--muted);display:flex;gap:16px;flex-wrap:wrap}.dot{display:inline-block;width:9px;height:9px;border-radius:50%;margin-right:5px}#tip{position:fixed;display:none;z-index:2;background:#060a13;border:1px solid #42516b;border-radius:8px;padding:10px 12px;max-width:400px;pointer-events:none;box-shadow:0 6px 30px #0008}.bars{display:grid;gap:9px}.barrow{display:grid;grid-template-columns:minmax(100px,1fr) 2fr auto;gap:9px;align-items:center;font-size:12px}.track{height:9px;background:#222e45;border-radius:9px;overflow:hidden}.fill{height:100%;background:var(--teal)}.warning{border-left:3px solid var(--gold);padding:10px 12px;background:#211d17;color:#f4dfb2;border-radius:4px}.footer{font-size:12px;color:var(--muted);margin-top:18px}a{color:var(--teal)}@media(max-width:800px){.grid{grid-template-columns:1fr}.wide{grid-column:auto}main{padding:16px}}
</style><main><h1>Repository evolution</h1><div class="sub">Git parent lineage annotated with available declaration-link and fingerprint records.</div><div class="stats" id="stats"></div><div class="grid"><section class="card wide"><h2>Commit ancestry through time</h2><div class="legend"><span><i class="dot" style="background:var(--teal)"></i>Leaf with DNA fingerprint records</span><span><i class="dot" style="background:#66738c"></i>Other commit / no leaf fingerprint shown</span><span>Node size reflects distinct declarations</span></div><div class="plot"><canvas id="tree"></canvas></div><div class="note">Filtered to the selected Git history window. Edges shown only where both parent and child are in the window; merge parents are retained.</div></section><section class="card"><h2>Commit activity by month</h2><div class="plot"><canvas id="months"></canvas></div></section><section class="card"><h2>Most-linked modules</h2><div id="modules" class="bars"></div></section><section class="card wide"><h2>Evidence boundary</h2><div class="warning">Git parent edges are direct ancestry. Taxonomy labels are weak commit classifications. Existing module-to-declaration rows are habitat cohabitation, not proof that the declaration changed in that commit. A fingerprint match is a candidate grouping unless the fingerprint algorithm, snapshot, and exact historical source span are established.</div><div id="quality" class="note" style="margin-top:12px"></div></section></div><div class="footer">Generated locally · <a href="https://link.springer.com/article/10.1186/1745-6150-4-43">Visualization framing: Ragan, “Trees and networks before and after Darwin” (2009)</a></div></main><div id="tip"></div>
<script>const D=__DATA__;const $=x=>document.getElementById(x);const nodes=D.nodes;const leaves=nodes.filter(n=>n.is_leaf),leafMatches=leaves.filter(n=>n.fingerprint_values.length).length;const linked=nodes.filter(n=>n.declarations).length;const decls=nodes.reduce((a,n)=>a+n.declarations,0),fps=nodes.reduce((a,n)=>a+n.fingerprints,0),exact=nodes.reduce((a,n)=>a+n.exact,0),co=nodes.reduce((a,n)=>a+n.cohabitation,0);$('stats').innerHTML=[['Commits',nodes.length],['Leaves',leaves.length],['Leaves with DNA records',leafMatches],['Declaration links',decls],['Fingerprint values',fps],['Exact links',exact]].map(([k,v])=>`<div class="stat"><span class="sub">${k}</span><b>${v.toLocaleString()}</b></div>`).join('');$('quality').textContent=co.toLocaleString()+' linked rows are marked/treated as cohabitation or unspecified evidence. Fingerprints were '+(fps?'present in supplied edge records.':'not present in the supplied edge records.')+' No external database was queried while generating this file.';const colors=getComputedStyle(document.documentElement),teal=colors.getPropertyValue('--teal'),muted=colors.getPropertyValue('--muted');function setup(id){let c=$(id),r=c.getBoundingClientRect(),d=devicePixelRatio||1;c.width=r.width*d;c.height=r.height*d;let x=c.getContext('2d');x.scale(d,d);return [x,r.width,r.height]}function monthChart(){let [x,w,h]=setup('months'),m=D.months,max=Math.max(1,...m.map(q=>q[1])),gap=5,bw=(w-gap*(m.length-1))/Math.max(1,m.length);x.strokeStyle='#293750';x.beginPath();x.moveTo(0,h-24);x.lineTo(w,h-24);x.stroke();m.forEach((q,i)=>{let bh=(h-52)*q[1]/max,xx=i*(bw+gap);x.fillStyle=teal;x.fillRect(xx,h-25-bh,bw,bh);if(m.length<18||i%3===0){x.fillStyle=muted;x.font='10px system-ui';x.save();x.translate(xx+bw/2,h-5);x.rotate(-.45);x.textAlign='right';x.fillText(q[0],0,0);x.restore()}})}let hit=[];function tree(){let [x,w,h]=setup('tree');hit=[];let sorted=[...nodes].sort((a,b)=>a.date.localeCompare(b.date)||a.sha.localeCompare(b.sha));if(!sorted.length)return;let days=sorted.map(n=>Date.parse(n.date+'T00:00:00Z')),lo=Math.min(...days),hi=Math.max(lo+86400000,...days),cols=new Map(),xy=new Map();sorted.forEach(n=>{let day=Date.parse(n.date+'T00:00:00Z'),col=Math.floor((day-lo)/(hi-lo)*Math.max(1,w-40)/22);let k=col,idx=cols.get(k)||0;cols.set(k,idx+1);let xx=20+col*22,yy=20+(idx%Math.max(1,Math.floor((h-40)/12)))*12+Math.floor(idx/Math.max(1,Math.floor((h-40)/12)))*2;xy.set(n.sha,[xx,Math.min(h-10,yy)])});x.lineWidth=1;for(const n of sorted){let [a,b]=xy.get(n.sha);for(const p of n.parents){let pt=xy.get(p);if(!pt)continue;x.strokeStyle='#52627b66';x.beginPath();x.moveTo(pt[0],pt[1]);x.lineTo(a,b);x.stroke()}}for(const n of sorted){let [a,b]=xy.get(n.sha),rad=Math.min(8,2.2+Math.sqrt(n.declarations));x.fillStyle=n.is_leaf&&n.fingerprint_values.length?teal:'#78849a';x.beginPath();x.arc(a,b,rad,0,Math.PI*2);x.fill();hit.push({x:a,y:b,r:rad,n})}x.fillStyle=muted;x.font='11px system-ui';x.fillText(sorted[0].date,8,h-5);x.textAlign='right';x.fillText(sorted.at(-1).date,w-8,h-5);x.textAlign='left'}$('tree').addEventListener('mousemove',e=>{let r=e.currentTarget.getBoundingClientRect(),px=e.clientX-r.left,py=e.clientY-r.top,p=hit.find(p=>(p.x-px)**2+(p.y-py)**2<(p.r+5)**2),t=$('tip');if(!p){t.style.display='none';return}let n=p.n;t.innerHTML=`<b>${n.short}</b> · ${n.date}${n.is_leaf?' · LEAF':''}<br>${esc(n.subject)}<br>Parents: ${n.parents.length} · declarations linked: ${n.declarations} · fingerprint hashes: ${n.fingerprints}<br>${esc(n.modules.join(', '))}<br><b>Leaf DNA fingerprints (up to ${n.fingerprint_values.length} shown):</b><br><pre>${esc(JSON.stringify(n.fingerprint_values,null,2))}</pre>`;t.style.display='block';t.style.left=Math.min(innerWidth-410,e.clientX+14)+'px';t.style.top=Math.min(innerHeight-150,e.clientY+14)+'px'});$('tree').addEventListener('mouseleave',()=>$('tip').style.display='none');function esc(s){return String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}let maxm=Math.max(1,...D.modules.map(x=>x[1]));$('modules').innerHTML=D.modules.map(([m,n])=>`<div class="barrow"><span title="${esc(m)}">${esc(m.split('/').at(-1))}</span><div class="track"><div class="fill" style="width:${100*n/maxm}%"></div></div><b>${n}</b></div>`).join('')||'<span class="note">No declaration-link annotations supplied.</span>';function draw(){monthChart();tree()}addEventListener('resize',draw);draw();</script></html>'''


PAGE = PAGE.replace(
    '<h2>Most-linked modules</h2>',
    '<h2>Commit archetypes</h2><div id="archetypes" class="bars"></div>'
    '<h2>Most-linked modules</h2>',
).replace(
    "function draw(){monthChart();tree()}",
    "let maxa=Math.max(1,...D.archetypes.map(x=>x[1]));$('archetypes').innerHTML="
    "D.archetypes.map(([m,n])=>`<div class=\"barrow\"><span>${esc(m)}</span>"
    "<div class=\"track\"><div class=\"fill\" style=\"width:${100*n/maxa}%\"></div></div>"
    "<b>${n}</b></div>`).join('')||'<span class=\"note\">No labels supplied.</span>';"
    "function draw(){monthChart();tree()}",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--since", default="1 year ago", help="Git --since expression")
    parser.add_argument("--limit", type=int, default=5000)
    parser.add_argument("--edges", type=Path, help="optional commit/declaration JSONL bridge")
    parser.add_argument("--labels", type=Path, help="optional weak taxonomy JSONL from evolution_taxonomy.py")
    parser.add_argument("--fingerprints-per-leaf", type=int, default=12,
                        help="maximum fingerprint records embedded for each leaf commit")
    parser.add_argument("--out", type=Path, default=Path("reports/darwin_phylogeny.html"))
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    commits = git_commits(args.since, args.limit)
    allowed = {row["sha"] for row in commits}
    parents = {parent for row in commits for parent in row["parents"] if parent in allowed}
    leaf_ids = allowed - parents
    annotations = load_edges(args.edges, allowed, leaf_ids, args.fingerprints_per_leaf)
    payload = build_payload(commits, annotations, load_labels(args.labels))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
               .replace("<", "\\u003c").replace(">", "\\u003e")
               .replace("&", "\\u0026"))
    args.out.write_text(PAGE.replace("__DATA__", encoded), encoding="utf-8")
    print(json.dumps({"output": str(args.out), "commits": len(commits),
                      "linked_commits": sum(bool(a["declarations"]) for a in annotations.values()),
                      "fingerprint_records": sum(len(a["fingerprint_records"])
                                                 for a in annotations.values())},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

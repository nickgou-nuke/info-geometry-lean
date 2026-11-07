#!/usr/bin/env python3
"""Conservative check that a declared Lean proof-golf change preserves statements.

It compares declaration headers in the two Git revisions. It does not prove
equivalence of changed proof terms; the Lean build remains required.
"""
from __future__ import annotations
import argparse,re,subprocess,sys

DECL=re.compile(r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma)\s+([\w'.]+)",re.M)
def git(*args:str)->str: return subprocess.run(["git",*args],check=True,text=True,capture_output=True).stdout

def signatures(source: str) -> dict[str, str]:
    matches=list(DECL.finditer(source)); result={}
    for index, match in enumerate(matches):
        limit=matches[index+1].start() if index+1<len(matches) else len(source)
        depth={"(":0,"{":0,"[":0}; pairs={")":"(","}":"{","]":"["}
        in_string=False; line_comment=False; block_depth=0; assignment=None; i=match.start()
        while i<limit:
            ch=source[i]; nxt=source[i+1] if i+1<limit else ""
            if line_comment:
                if ch=="\n": line_comment=False
                i+=1; continue
            if block_depth:
                if ch=="/" and nxt=="-": block_depth+=1; i+=2; continue
                if ch=="-" and nxt=="/": block_depth-=1; i+=2; continue
                i+=1; continue
            if in_string:
                if ch=="\\": i+=2; continue
                if ch=='"': in_string=False
                i+=1; continue
            if ch=="-" and nxt=="-": line_comment=True; i+=2; continue
            if ch=="/" and nxt=="-": block_depth=1; i+=2; continue
            if ch=='"': in_string=True; i+=1; continue
            if ch in depth: depth[ch]+=1
            elif ch in pairs: depth[pairs[ch]]=max(0,depth[pairs[ch]]-1)
            if ch==":" and nxt=="=" and not any(depth.values()): assignment=i; break
            i+=1
        if assignment is not None:
            result[match.group(1)]=re.sub(r"\s+"," ",source[match.start():assignment]).strip()
    return result

def main()->int:
 ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("--base",required=True); ap.add_argument("--head",default="HEAD"); ap.add_argument("paths",nargs="+"); n=ap.parse_args(); failures=[]
 for path in n.paths:
  try: old=git("show",f"{n.base}:{path}"); new=git("show",f"{n.head}:{path}")
  except subprocess.CalledProcessError: failures.append(f"{path}: added/deleted path; not a proof-only golf"); continue
  old_decls=signatures(old)
  new_decls=signatures(new)
  if old_decls != new_decls: failures.append(f"{path}: declaration set or header changed")
  else: print(f"{path}: declaration names/headers unchanged (proof-only candidate)")
 if failures: print("\n".join(failures),file=sys.stderr); return 1
 print("proof-only golf check passed at lexical header scope; compile and semantic review remain required")
 return 0
if __name__=="__main__": raise SystemExit(main())

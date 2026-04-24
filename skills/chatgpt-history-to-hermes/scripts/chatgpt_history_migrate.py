#!/usr/bin/env python3
import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path


def safe_text(content):
    if content is None:
        return ""
    if isinstance(content, str):
        return content.strip()
    if isinstance(content, dict):
        # ChatGPT export often stores content.parts
        parts = content.get("parts")
        if isinstance(parts, list):
            return "\n".join(str(p) for p in parts if p is not None).strip()
        text = content.get("text")
        if isinstance(text, str):
            return text.strip()
    if isinstance(content, list):
        return "\n".join(str(x) for x in content if x is not None).strip()
    return str(content).strip()


def normalize_role(msg):
    author = (msg.get("author") or {})
    role = author.get("role")
    if role in {"user", "assistant", "system", "tool"}:
        return role
    if role == "model":
        return "assistant"
    if role == "human":
        return "user"
    return "unknown"


def extract_messages(conversation):
    mapping = conversation.get("mapping") or {}
    rows = []
    for node_id, node in mapping.items():
        message = node.get("message")
        if not message:
            continue
        content = message.get("content")
        text = safe_text(content)
        if not text:
            continue
        ts = (
            message.get("create_time")
            or node.get("create_time")
            or conversation.get("create_time")
        )
        rows.append(
            {
                "node_id": node_id,
                "parent": node.get("parent"),
                "role": normalize_role(message),
                "text": text,
                "timestamp": ts,
            }
        )
    # Approximate chronological order
    rows.sort(key=lambda r: (r["timestamp"] is None, r["timestamp"] or 0))
    return rows


def md_escape(s):
    return s.replace("\r\n", "\n").replace("\r", "\n").strip()


def build_memory_candidates(messages):
    candidates = []
    pref_patterns = [
        re.compile(r"\bI prefer\b[:\s]+(.+)", re.IGNORECASE),
        re.compile(r"\bmy preference is\b[:\s]+(.+)", re.IGNORECASE),
        re.compile(r"\bcall me\b[:\s]+([A-Za-z0-9_\- ]{2,40})", re.IGNORECASE),
        re.compile(r"\bI am\b[:\s]+(.+)", re.IGNORECASE),
        re.compile(r"\btimezone\b[:\s]+([A-Za-z_\-/+0-9 ]+)", re.IGNORECASE),
    ]

    for m in messages:
        if m["role"] != "user":
            continue
        text = m["text"].strip()
        if len(text) > 400:
            continue
        for rx in pref_patterns:
            hit = rx.search(text)
            if not hit:
                continue
            value = hit.group(1).strip().rstrip(".")
            if len(value) < 3:
                continue
            kind = "user_preference"
            key = "preference"
            if "call me" in rx.pattern.lower():
                key = "name"
                kind = "user_profile"
            elif "timezone" in rx.pattern.lower():
                key = "timezone"
                kind = "user_profile"
            elif rx.pattern.lower().startswith("\\bi am"):
                key = "identity"
                kind = "user_profile"
            candidates.append({"kind": kind, "key": key, "value": value, "source_role": "user"})

    # de-dup exact triples
    seen = set()
    deduped = []
    for c in candidates:
        k = (c["kind"], c["key"], c["value"])
        if k in seen:
            continue
        seen.add(k)
        deduped.append(c)
    return deduped


def write_jsonl(path, rows):
    with path.open("w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")


def main():
    ap = argparse.ArgumentParser(description="Normalize ChatGPT export into Hermes-friendly archive + memory candidates")
    ap.add_argument("--input", required=True, help="Path to conversations.json")
    ap.add_argument("--out", required=True, help="Output directory")
    args = ap.parse_args()

    in_path = Path(args.input).expanduser().resolve()
    out_dir = Path(args.out).expanduser().resolve()
    sessions_md = out_dir / "sessions_md"
    out_dir.mkdir(parents=True, exist_ok=True)
    sessions_md.mkdir(parents=True, exist_ok=True)

    data = json.loads(in_path.read_text(encoding="utf-8"))
    if isinstance(data, dict):
        # some exports nest conversations under key
        conversations = data.get("conversations") or []
    else:
        conversations = data

    normalized_rows = []
    all_msgs = []
    msg_count = 0

    for conv in conversations:
        cid = conv.get("id") or conv.get("conversation_id") or "unknown"
        title = conv.get("title") or "Untitled"
        ctime = conv.get("create_time")
        utime = conv.get("update_time")
        msgs = extract_messages(conv)
        msg_count += len(msgs)
        all_msgs.extend(msgs)

        normalized_rows.append(
            {
                "conversation_id": cid,
                "title": title,
                "create_time": ctime,
                "update_time": utime,
                "message_count": len(msgs),
                "messages": msgs,
            }
        )

        md_lines = [f"# {title}", "", f"conversation_id: {cid}"]
        if ctime is not None:
            md_lines.append(f"create_time: {ctime}")
        if utime is not None:
            md_lines.append(f"update_time: {utime}")
        md_lines.append("")
        for m in msgs:
            role = m["role"].upper()
            md_lines.append(f"## {role}")
            if m["timestamp"] is not None:
                md_lines.append(f"timestamp: {m['timestamp']}")
            md_lines.append("")
            md_lines.append(md_escape(m["text"]))
            md_lines.append("")

        (sessions_md / f"{cid}.md").write_text("\n".join(md_lines), encoding="utf-8")

    candidates = build_memory_candidates(all_msgs)

    write_jsonl(out_dir / "normalized_conversations.jsonl", normalized_rows)
    write_jsonl(out_dir / "memory_candidates.jsonl", candidates)

    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "input": str(in_path),
        "output_dir": str(out_dir),
        "conversation_count": len(normalized_rows),
        "message_count": msg_count,
        "memory_candidate_count": len(candidates),
        "artifacts": {
            "normalized_jsonl": str(out_dir / "normalized_conversations.jsonl"),
            "sessions_md_dir": str(sessions_md),
            "memory_candidates": str(out_dir / "memory_candidates.jsonl"),
        },
    }
    (out_dir / "migration_report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()

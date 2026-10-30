# Exporting a Google AI Studio conversation

This procedure downloads the saved AI Studio prompt/conversation from a public
AI Studio prompt link. AI Studio stores saved prompts in Google Drive as JSON
content, usually in a file with no `.json` extension. The Drive download is the
conversation artifact; **Get code** downloads API starter code instead.

## Procedure: download directly from the public prompt link

1. Open the shared AI Studio prompt URL. Its state contains the prompt's Drive
   file ID in the `ids` array. For example, the public prompt URL includes
   `17Kj7oLBHPfoWvQLKPwwve8pcsDezqpkG`.

   ```text
   https://aistudio.google.com/app/prompts?state=...&usp=sharing
   ```

2. Put that ID into the Google Drive file URL:

   ```text
   https://drive.google.com/file/d/<PROMPT_ID>/view
   ```

3. Open the link in the signed-in browser. Drive shows the saved file under the
   prompt title, often with “No preview available.” Click **Download** in the
   center of the page or the down-arrow in the toolbar.

4. Locate the downloaded file in the browser's Downloads list or configured
   Downloads directory. Drive may omit the `.json` extension. The file is still
   JSON; verify by parsing it. Preserve the downloaded original and, if useful,
   make a separately named `.json` copy for tooling. The observed schema has
   top-level `runSettings`, `systemInstruction`, and
   `chunkedPrompt.chunks`. Preserve chunk order and roles when extracting; do
   not treat only the final response as the full transcript.

5. Check completeness before formalization: record file size, parse the JSON,
   count roles/chunks, capture first and last timestamps, and confirm the latest
   visible response appears in the file. A successful download alone does not
   establish that the file is the latest snapshot.

## Distinguish the other download controls

- **AI Studio → Get code → Java** generates a Java SDK request example. The
  visible starter code uses an input placeholder; it is not the chat archive.
- **AI Studio → Get code → REST** generates an HTTP/API request example with a
  JSON request body. This is also not the chat archive.
- **AI Studio → View more actions → Raw Mode** changes how response text is
  displayed. It does not download JSON.
- **Google Drive → Download** on the saved prompt file downloads the stored
  prompt/conversation JSON artifact. This is the route to use for full-history
  extraction.

## Verified instance

On 2026-10-30, opening
`https://drive.google.com/file/d/17Kj7oLBHPfoWvQLKPwwve8pcsDezqpkG/view`
loaded the same titled Drive item as the public AI Studio prompt. Clicking its
visible **Download** button produced the extensionless file
`Non-Commutative Operator Algebra Formalization (1)`. It parsed as JSON: 3,819,694
bytes; 158 ordered chunks (79 `user`, 79 `model`); 3,243,072 characters across
chunk values; first timestamp `2026-10-27T14:17:59.443Z`; last timestamp
`2026-10-29T21:44:42.867Z`; 107 tagged Lean fence openings (106 paired and one
unterminated in the raw source); and A27 material present.
The Drive page showed **No preview available** and the visible Download control.
The AI Studio **Get code** language menu separately offered Python, TypeScript,
Java, Go, and REST. Its Java example contained `INSERT_INPUT_HERE`, so that
download is API starter code rather than the conversation archive.

## Additional formalization source exports (2026-10-30)

The public AI Studio prompt ID
`1t9Q3cbWphRcmuigvp9LZomzS7Q8Pclxe` was fetched through its public Drive
download endpoint and preserved at
`cached/aistudio_prompt_1t9Q3cbWphRcmuigvp9LZomzS7Q8Pclxe.json`. It parses as
the same `runSettings` / `systemInstruction` / `chunkedPrompt.chunks` schema:
1,367,136 bytes, 33 ordered chunks (17 user, 16 model), with first and last
timestamps `2026-10-29T15:50:56.358Z` and `2026-10-30T03:00:47.041Z`.

The current 17K snapshot is preserved at
`cached/aistudio_prompt_17Kj7oLBHPfoWvQLKPwwve8pcsDezqpkG.json`. Its earlier
74-chunk download is an exact prefix. Source hashes, rendered transcripts, all
fenced blocks, tagged Lean extracts, and unlabelled Lean-like candidates are
indexed under `cached/aistudio_extracts/`; regenerate them with
`python3 tools/infra/extract_aistudio_math.py ... --output-dir cached/aistudio_extracts`.
The raw JSON is authoritative for exact whitespace and message payloads; the
Markdown extracts are reading/indexing aids. Extracted Lean remains a candidate
until its theorem is moved into an owner file and kernel-checked.

The other supplied Drive IDs
`1E6iRChkkEszjN_UBwp9DhW6sOTe-0YEU` and
`1PO_i6oQvcMXHygqCDANTy2w8y4JO_IGH` returned Google Accounts sign-in HTML when
requested through the direct public download endpoint. They are not recorded as
successful transcript downloads. The local Chromium/CDP browser was unavailable
in this session, so those items need an accessible public export or signed-in
browser session before their contents can be incorporated.

## Refreshed Peirce–Cartan export (2026-10-30)

After the user reported an update, the public Drive export was fetched again.
`cached/aistudio_prompt_1t9Q3cbWphRcmuigvp9LZomzS7Q8Pclxe_updated.json`
contains 1,429,841 bytes and 35 chunks (18 user, 17 model), ending at
`2026-10-30T03:11:33.126Z`. The previous 33 chunks are an exact prefix.
SHA-256: `4a1318e72e6807bfca2314dc7cc10bfd75b7474f08db6e90fe7b6ac75fe9b34d`.
The added response develops A₄₃–A₄₄ chiral factors and ordered supercharge
products. Its candidates are indexed in the matching `_updated` directory
under `cached/aistudio_extracts/`; the previous snapshot remains preserved.
Browser-harness reached the signed-in Drive Download control, but clicking it
produced no observed local file. The public `uc?export=download&id=...`
endpoint supplied the JSON, whose schema and prefix were then checked locally.

## Browser-harness procedure on Ubuntu (commands)

The extraction tool now reads dollar-delimited and backslash-delimited LaTeX
directly from JSON text, excluding fenced code, when rendered `pres` regions
are unavailable. All archived sources have been re-extracted. Each manifest
records `math_expression_count`. Counts for the five current source snapshots
(excluding the superseded 33-turn snapshot) are:

| Source ID | Turns | Extracted math regions |
|---|---:|---:|
| `1t9Q3cbWphRcmuigvp9LZomzS7Q8Pclxe` (updated) | 35 | 2235 |
| `17Kj7oLBHPfoWvQLKPwwve8pcsDezqpkG` | 158 | 8095 |
| `1SSh9Kruyv8BNCpXiC5g0he9V4e7j_4Dr` | 365 | 6446 |
| `1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or` | 311 | 5310 |
| `1YHHorO` (browser scroll extraction) | 93 | 170 |

These are occurrence counts, not counts of distinct theorems. Mathematical
prose and code remain in the full transcript and fence indexes; the equation
index alone is not a complete mathematical claim inventory. The scroll
extraction has a different provenance from the Drive JSON downloads.

When controlling the already signed-in Ubuntu Chromium session through
browser-harness, use the active CDP endpoint and stdin interface:

```bash
BU_CDP_URL=http://127.0.0.1:9222 browser-harness <<'PY'
print(list_tabs())
PY
```

If the harness cannot connect, first check whether Chromium already owns port
9222:

```bash
curl --noproxy '*' -sS http://127.0.0.1:9222/json/version
```

Do not launch a second Chromium instance when the endpoint is already live.
Use the browser's visible Drive Download control, then verify the resulting
file in Downloads. Browser-harness itself does not substitute for the
AI-Studio-to-Drive export step.

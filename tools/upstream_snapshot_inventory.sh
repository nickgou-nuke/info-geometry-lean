#!/usr/bin/env bash
set -euo pipefail

out_dir="${1:-artifacts/upstream_snapshot}"
mkdir -p "$out_dir"

refs_file="$out_dir/refs.tsv"
paths_file="$out_dir/lean_paths.tsv"
missing_file="$out_dir/missing_local_lean_paths.tsv"
missing_real_file="$out_dir/missing_real_local_lean_paths.tsv"
missing_alias_file="$out_dir/missing_existing_alias_paths.tsv"
missing_provenance_file="$out_dir/missing_provenance.tsv"
all_paths_file="$out_dir/all_paths.tsv"
all_missing_file="$out_dir/all_missing_local_paths.tsv"
all_missing_provenance_file="$out_dir/all_missing_provenance.tsv"

printf 'ref\tcommit\tlean_source_count\n' > "$refs_file"
: > "$paths_file"

while read -r ref commit; do
  count=$(git -c core.quotePath=false ls-tree -r --name-only "$ref" -- 'lean' | awk '/\.lean$/ {n++} END {print n+0}')
  printf '%s\t%s\t%s\n' "$ref" "$commit" "$count" >> "$refs_file"
  git -c core.quotePath=false ls-tree -r --name-only "$ref" -- 'lean' | awk -v r="$ref" -v c="$commit" '/\.lean$/ {print r "\t" c "\t" $0}' >> "$paths_file"
done < <(git for-each-ref --format='%(refname) %(objectname)' refs/remotes/upstream | sort)

sort -u -k3,3 "$paths_file" -o "$paths_file"

local_paths=$(mktemp)
trap 'rm -f "$local_paths"' EXIT
rg --files lean -g '*.lean' | sort -u > "$local_paths"

awk -F '\t' '{print $3}' "$paths_file" | sort -u | comm -23 - "$local_paths" > "$missing_file"

: > "$missing_real_file"
: > "$missing_alias_file"
while read -r path; do
  if [ -e "$path" ]; then
    printf '%s\n' "$path" >> "$missing_alias_file"
  else
    printf '%s\n' "$path" >> "$missing_real_file"
  fi
done < "$missing_file"

printf 'path\tref\tcommit\tblob\n' > "$missing_provenance_file"
while read -r path; do
  row=$(awk -F '\t' -v p="$path" '$3 == p {print; exit}' "$paths_file")
  ref=$(printf '%s' "$row" | cut -f1)
  commit=$(printf '%s' "$row" | cut -f2)
  if ! blob=$(git rev-parse "$ref:$path" 2>/dev/null); then
    blob=GITLINK
  fi
  printf '%s\t%s\t%s\t%s\n' "$path" "$ref" "$commit" "$blob" >> "$missing_provenance_file"
done < "$missing_real_file"

printf 'refs=%s\n' "$(($(wc -l < "$refs_file") - 1))" > "$out_dir/summary.txt"
printf 'unique_upstream_lean_paths=%s\n' "$(awk -F '\t' '{print $3}' "$paths_file" | sort -u | wc -l)" >> "$out_dir/summary.txt"
printf 'local_lean_paths=%s\n' "$(wc -l < "$local_paths")" >> "$out_dir/summary.txt"
printf 'missing_local_lean_paths=%s\n' "$(wc -l < "$missing_file")" >> "$out_dir/summary.txt"
printf 'missing_existing_alias_paths=%s\n' "$(wc -l < "$missing_alias_file")" >> "$out_dir/summary.txt"
printf 'missing_real_local_lean_paths=%s\n' "$(wc -l < "$missing_real_file")" >> "$out_dir/summary.txt"

if [ "${2:-}" = "--extract-missing" ]; then
  source_dir="$out_dir/sources"
  while IFS=$'\t' read -r path ref commit blob; do
    [ "$path" = path ] && continue
    target="$source_dir/$path"
    mkdir -p "$(dirname "$target")"
    git show "$ref:$path" > "$target"
  done < "$missing_provenance_file"
fi

# Full tracked-tree inventory (not limited to Lean), kept outside production.
: > "$all_paths_file"
while read -r ref commit; do
  while IFS= read -r -d '' path; do
    printf '%s\t%s\t%s\n' "$ref" "$commit" "$path"
  done < <(git -c core.quotePath=false ls-tree -r -z --name-only "$ref") >> "$all_paths_file"
done < <(git for-each-ref --format='%(refname) %(objectname)' refs/remotes/upstream | sort)
sort -u -k3,3 "$all_paths_file" -o "$all_paths_file"

all_local_paths=$(mktemp)
trap 'rm -f "$local_paths" "$all_local_paths"' EXIT
find . -path './.git' -prune -o -path './.lake' -prune -o -type f -print | sed 's#^\./##' | sort -u > "$all_local_paths"
awk -F '\t' '{print $3}' "$all_paths_file" | sort -u | comm -23 - "$all_local_paths" > "$all_missing_file"

printf 'path\tref\tcommit\tblob\n' > "$all_missing_provenance_file"
while read -r path; do
  row=$(awk -F '\t' -v p="$path" '$3 == p {print; exit}' "$all_paths_file")
  ref=$(printf '%s' "$row" | cut -f1)
  commit=$(printf '%s' "$row" | cut -f2)
    if ! blob=$(git rev-parse "$ref:$path" 2>/dev/null); then
      blob=GITLINK
    fi
  printf '%s\t%s\t%s\t%s\n' "$path" "$ref" "$commit" "$blob" >> "$all_missing_provenance_file"
done < "$all_missing_file"

if [ "${3:-}" = "--extract-all-missing" ]; then
  all_source_dir="$out_dir/all_sources"
  while IFS=$'\t' read -r path ref commit blob; do
    [ "$path" = path ] && continue
    mode=$(git ls-tree "$ref" -- "$path" | awk 'NR == 1 {print $1}')
    [ "$mode" = 160000 ] && continue
    [ "$blob" = GITLINK ] && continue
    target="$all_source_dir/$path"
    mkdir -p "$(dirname "$target")"
    git show "$ref:$path" > "$target"
  done < "$all_missing_provenance_file"
fi

printf 'unique_upstream_tracked_paths=%s\n' "$(awk -F '\t' '{print $3}' "$all_paths_file" | sort -u | wc -l)" >> "$out_dir/summary.txt"
printf 'missing_all_local_paths=%s\n' "$(wc -l < "$all_missing_file")" >> "$out_dir/summary.txt"

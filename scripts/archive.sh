#!/usr/bin/env bash
# Export the selected Git commit. The destination must be outside the archive.
set -euo pipefail
cd "$(dirname "$0")/.."
dest=$(realpath -m "${1:-.}")
commit=$(git rev-parse --verify "${2:-HEAD}^{commit}")
version=$(git show "$commit:CITATION.cff" | sed -n 's/^version: //p')
[[ "$version" =~ ^[0-9A-Za-z.-]+$ ]]
stem="median-of-11-$version-$commit"
mkdir -p "$dest"
git archive --format=zip --prefix="$stem/" --output="$dest/$stem.zip" "$commit"
(cd "$dest" && sha256sum "$stem.zip" > "$stem.zip.sha256" && sha256sum -c "$stem.zip.sha256")

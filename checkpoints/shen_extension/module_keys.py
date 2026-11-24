"""Print one content key per project Lean file, as `path key` lines.

A file's key hashes its own source, the toolchain, the dependency manifest,
the Lake configuration and the keys of every project file it imports. Two
trees give a file the same key exactly when the file and everything it
imports inside the project are the same text on the same Lean and Mathlib.
check_capstone.sh stores the key beside each compiled file and compiles
again only when the key has changed. Run from the repository root.
"""
import hashlib
import re
import sys
from pathlib import Path

root = Path(".")
skip = {".lake", ".git"}
src_dirs = ["."] + re.findall(
    r'^srcDir\s*=\s*"([^"]+)"', (root / "lakefile.toml").read_text(encoding="utf-8"), re.MULTILINE)


def text(path):
    return path.read_bytes().replace(b"\r\n", b"\n")


base = hashlib.sha256()
for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
    base.update(name.encode() + b"\0" + text(root / name) + b"\0")

files = [p for p in root.rglob("*.lean") if not skip.intersection(p.parts)]
module = {}
for path in files:
    posix = path.as_posix()
    for src in src_dirs:
        prefix = "" if src == "." else src.rstrip("/") + "/"
        if posix.startswith(prefix):
            module.setdefault(posix[len(prefix):-len(".lean")].replace("/", "."), path)

import_line = re.compile(rb"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?(.+)$", re.MULTILINE)
keys = {}


def key(path, stack=()):
    if path in keys:
        return keys[path]
    if path in stack:
        sys.exit(f"import cycle through {path}")
    source = text(path)
    digest = base.copy()
    digest.update(source)
    names = {n.decode() for line in import_line.findall(source) for n in line.split()}
    for name in sorted(names):
        if name in module:
            digest.update(name.encode() + b"=" + key(module[name], stack + (path,)).encode() + b"\0")
    keys[path] = digest.hexdigest()
    return keys[path]


sys.setrecursionlimit(10000)
for path in sorted(files):
    print(path.as_posix(), key(path))

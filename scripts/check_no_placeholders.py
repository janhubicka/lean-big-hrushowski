"""Reject unproved Lean placeholders."""
from pathlib import Path
import re
sources = [Path("BigHrushovski.lean"), Path("CheckAxioms.lean")]
sources.extend(sorted(Path("BigHrushovski").rglob("*.lean")))
for source in sources:
    match = re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", source.read_text())
    if match:
        raise SystemExit(f"{source}: prohibited token {match.group()!r}")
print(f"Checked {len(sources)} Lean files for placeholders.")

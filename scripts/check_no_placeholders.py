"""Reject Lean proof placeholders in all project source and audit modules.

Only source files owned by this repository are scanned; .lake packages are
excluded. Lean comments are masked (including nested block comments), while
strings are scanned conservatively for forbidden tokens.
"""
from pathlib import Path
import re

FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe)\b")


def mask_lean_comments(text: str) -> str:
    """Replace comment characters with spaces, preserving line numbers.

    Lean block comments may nest. Quoted string literals are not comments;
    in particular, comment markers inside a string must not mask later code.
    """
    chars = list(text)
    i, depth, in_string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                chars[i:i+2] = '  '
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                chars[i:i+2] = '  '
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    chars[i] = ' '
                i += 1
        elif in_string:
            if text[i] == '\\':
                i += min(2, len(text) - i)
            else:
                if text[i] == '"':
                    in_string = False
                i += 1
        elif text[i] == '"':
            in_string = True
            i += 1
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                chars[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            chars[i:i+2] = '  '
            depth = 1
            i += 2
        else:
            i += 1
    return ''.join(chars)


def project_lean_sources() -> list[Path]:
    """Include top-level check files, not only umbrella/project modules."""
    return sorted(Path('.').glob('*.lean')) + sorted(Path('BigHrushovski').rglob('*.lean'))


def main() -> None:
    sources = project_lean_sources()
    for source in sources:
        masked = mask_lean_comments(source.read_text())
        match = FORBIDDEN.search(masked)
        if match:
            line = masked.count('\n', 0, match.start()) + 1
            raise SystemExit(f"{source}:{line}: prohibited token {match.group()!r}")
    print(f"Checked {len(sources)} Lean files for placeholders.")


if __name__ == '__main__':
    main()

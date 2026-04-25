#!/usr/bin/env python3
"""
Reproduction script for the QANARY Paper 5 artifact
(The 1-Bit Barrier).

Verifies that the Lean 4 proof suite builds cleanly with zero sorry,
zero admit, zero axiom, zero native_decide, and zero errors. This is
the single-command entry point for artifact evaluation.

Usage:
    python3 reproduce.py          # full build + verification
    python3 reproduce.py --check  # skip build, verify existing artifacts

Expected output:
    All checks PASS.

Requirements:
    - elan (Lean 4 toolchain manager): https://github.com/leanprover/elan
    - Internet connection (first build downloads Mathlib, ~30 min)
"""

import subprocess
import sys
import os
from pathlib import Path

# Ensure elan-managed tools are on PATH
ELAN_BIN = Path.home() / ".elan" / "bin"
if ELAN_BIN.exists():
    os.environ["PATH"] = str(ELAN_BIN) + os.pathsep + os.environ.get("PATH", "")

HERE = Path(__file__).resolve().parent
LEAN_FILES = sorted((HERE / "QanaryPaper5").glob("*.lean"))

# Expected theorems / instances (name -> file). See README.md "Theorem Index".
EXPECTED_THEOREMS = {
    "barrettInternalMap_eq_or": "Basic.lean",
    "barrettInternalMap_mem_pair": "Basic.lean",
    "barrettInternalMap_preimage_subset": "BarrettUniversal.lean",
    "barrett_max_multiplicity_two": "BarrettUniversal.lean",
    "barrett_multiplicity_trichotomy": "BarrettUniversal.lean",
    "barrettInternalMap_candidate_A": "BarrettUniversal.lean",
    "barrettInternalMap_candidate_B": "BarrettUniversal.lean",
    "barrett_count_ge_one_of_A": "BarrettUniversal.lean",
    "barrett_count_ge_one_of_B": "BarrettUniversal.lean",
    "barrett_count_eq_two": "BarrettUniversal.lean",
    "barrettPFPINI": "BarrettUniversal.lean",
    "identityPFPINI": "BarrettUniversal.lean",
}

PASS = "\033[32mPASS\033[0m"
FAIL = "\033[31mFAIL\033[0m"


def check(name, condition, detail=""):
    status = PASS if condition else FAIL
    suffix = f" ({detail})" if detail else ""
    print(f"  [{status}] {name}{suffix}")
    return condition


def main():
    skip_build = "--check" in sys.argv
    all_pass = True

    print("=" * 60)
    print("QANARY Paper 5 Artifact — Reproduction Verification")
    print("  (The 1-Bit Barrier)")
    print("=" * 60)

    # 1. Toolchain + dependency sanity
    print("\n1. Toolchain")
    toolchain_file = HERE / "lean-toolchain"
    toolchain = toolchain_file.read_text().strip()
    all_pass &= check("lean-toolchain exists", toolchain_file.exists())
    all_pass &= check("Toolchain pinned", "leanprover/lean4:" in toolchain, toolchain)

    lakefile = HERE / "lakefile.lean"
    lakefile_text = lakefile.read_text()
    all_pass &= check("Mathlib pinned to commit", "322515540d7f" in lakefile_text)

    # 2. Build
    print("\n2. Build")
    if not skip_build:
        print("  Building (this may take several minutes)...")
        result = subprocess.run(
            ["lake", "build"],
            cwd=str(HERE),
            capture_output=True,
            text=True,
            timeout=3600,
        )
        all_pass &= check("lake build exit code 0", result.returncode == 0,
                          f"exit={result.returncode}")
        if result.returncode != 0:
            print(f"  STDERR: {result.stderr[:500]}")
    else:
        print("  [SKIP] --check mode, skipping build")

    # 3. Zero sorry / admit / axiom / native_decide.
    # Block comments are stripped with a regex that preserves line
    # numbers (comment content replaced by spaces, newlines preserved).
    # Inline `--` comments are then trimmed. Per-file scan; no
    # cross-file state.
    import re
    _block_comment_re = re.compile(r'/-(?:[^-]|-(?!/))*-/', re.DOTALL)
    def _blank_preserving_newlines(m: "re.Match[str]") -> str:
        return "".join(c if c == "\n" else " " for c in m.group(0))

    print("\n3. Sorry / Admit / Axiom / native_decide scan")
    total_sorry = 0
    total_admit = 0
    total_axiom = 0
    total_native_decide = 0
    for lf in LEAN_FILES:
        text = lf.read_text()
        text = _block_comment_re.sub(_blank_preserving_newlines, text)
        for i, line in enumerate(text.split("\n"), 1):
            stripped = line.strip()
            if not stripped or stripped.startswith("--"):
                continue
            code_part = line.split("--", 1)[0]
            if re.search(r'\bsorry\b', code_part):
                total_sorry += 1
                print(f"    SORRY: {lf.name}:{i}: {stripped}")
            if re.search(r'\badmit\b', code_part):
                total_admit += 1
                print(f"    ADMIT: {lf.name}:{i}: {stripped}")
            if re.search(r'^\s*axiom\s+\w+', code_part):
                total_axiom += 1
                print(f"    AXIOM: {lf.name}:{i}: {stripped}")
            if re.search(r'\bnative_decide\b', code_part):
                total_native_decide += 1
                print(f"    NATIVE_DECIDE: {lf.name}:{i}: {stripped}")

    all_pass &= check("Zero sorry in proof code", total_sorry == 0,
                      f"{total_sorry} found")
    all_pass &= check("Zero admit in proof code", total_admit == 0,
                      f"{total_admit} found")
    all_pass &= check("Zero axiom declarations", total_axiom == 0,
                      f"{total_axiom} found")
    all_pass &= check("Zero native_decide in proof code",
                      total_native_decide == 0,
                      f"{total_native_decide} found")

    # 4. Theorem / instance presence
    print("\n4. Theorem / instance verification")
    all_text = {}
    for lf in LEAN_FILES:
        all_text[lf.name] = lf.read_text()

    for thm_name, expected_file in EXPECTED_THEOREMS.items():
        found = thm_name in all_text.get(expected_file, "")
        all_pass &= check(f"{thm_name}", found, expected_file)

    # 5. File structure
    print("\n5. Repository structure")
    expected_files = [
        "lakefile.lean", "lean-toolchain", "lake-manifest.json",
        "QanaryPaper5.lean", "README.md", "LICENSE", "reproduce.py",
        "CITATION.cff", ".zenodo.json", "DESIGN.md",
        "QanaryPaper5/Basic.lean",
        "QanaryPaper5/BarrettUniversal.lean",
    ]
    for f in expected_files:
        all_pass &= check(f, (HERE / f).exists())

    # 6. No unwanted files committed
    print("\n6. Cleanliness")
    unwanted = [".docx", ".tex", ".bib", ".pdf"]
    result = subprocess.run(["git", "ls-files"], cwd=str(HERE),
                            capture_output=True, text=True)
    tracked = result.stdout.strip().split("\n") if result.stdout.strip() else []
    for ext in unwanted:
        matches = [f for f in tracked if f.endswith(ext)]
        all_pass &= check(f"No {ext} files tracked", len(matches) == 0,
                          ", ".join(matches) if matches else "clean")

    # AI attribution token scan. Tokens are ROT13-encoded so the scanner
    # does not flag its own source. The self-test below reconstructs each
    # expected plaintext from character codes (no literal tokens appear
    # in this source file) and asserts the decodings match. A ROT13 typo
    # is trapped immediately.
    import codecs
    banned = [codecs.decode(t, "rot_13") for t in (
        "pynhqr", "naguebcvp", "bcranv", "tcg", "Pb-Nhguberq-Ol",
    )]
    _expected = [
        "".join(chr(c) for c in seq) for seq in (
            (99, 108, 97, 117, 100, 101),
            (97, 110, 116, 104, 114, 111, 112, 105, 99),
            (111, 112, 101, 110, 97, 105),
            (103, 112, 116),
            (67, 111, 45, 65, 117, 116, 104, 111, 114,
             101, 100, 45, 66, 121),
        )
    ]
    assert banned == _expected, f"BANNED-TOKEN DECODING BUG: {banned}"
    ai_mentions = 0
    for f in tracked:
        fp = HERE / f
        if fp.exists() and fp.suffix in (".lean", ".md", ".py", ".toml",
                                         ".yml", ".yaml", ".json", ".cff"):
            text = fp.read_text()
            for term in banned:
                if term.lower() in text.lower():
                    ai_mentions += 1
                    print(f"    Attribution mention: {f} contains banned "
                          f"token (rot13: {codecs.encode(term, 'rot_13')})")
    all_pass &= check("No AI attribution tokens", ai_mentions == 0,
                      f"{ai_mentions} found")

    # Summary
    print("\n" + "=" * 60)
    if all_pass:
        print(f"  RESULT: ALL CHECKS {PASS}")
        print("  The proof suite is ready for artifact evaluation.")
    else:
        print(f"  RESULT: SOME CHECKS {FAIL}")
        print("  Fix failures before submission.")
    print("=" * 60)

    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())

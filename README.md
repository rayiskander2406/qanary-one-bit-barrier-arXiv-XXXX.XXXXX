# The 1-Bit Barrier

**Machine-Checked Cardinality Bounds for Masked Barrett Reduction: A 1-Bit Side-Channel Leakage Barrier in Post-Quantum Cryptographic Hardware**

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.30.0--rc1-blue)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-322515540d7f-green)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Sorry-Free](https://img.shields.io/badge/sorry-0-brightgreen)]()

Machine-checked Lean 4 proof that Barrett reduction under first-order
arithmetic masking has preimage multiplicity **at most 2, tightly
attained** — the *1-bit barrier*. Universally, for every odd prime
modulus q and every Barrett shift s with 2^s ≥ q.

This is the artifact repository for:

> R. Iskander, K. Kirah. "Machine-Checked Cardinality Bounds for
> Masked Barrett Reduction: A 1-Bit Side-Channel Leakage Barrier
> in Post-Quantum Cryptographic Hardware."
> arXiv:2604.24670, 2026.

## Context: Prior Papers in the Series

This artifact extends the proof program of four earlier papers:

- **Paper 1** — R. Iskander, K. Kirah. "Structural Dependency Analysis
  for Masked NTT Hardware: Scalable Pre-Silicon Verification of
  Post-Quantum Cryptographic Accelerators."
  [arXiv:2604.15249](https://arxiv.org/abs/2604.15249), 2026.
  Zenodo: [10.5281/zenodo.19625392](https://doi.org/10.5281/zenodo.19625392).
  *QANARY tool paper. Flags 165 of 363 Barrett wires in Adams Bridge
  as INSECURE_CONSERVATIVE; this paper quantitatively bounds the
  leakage on every such wire to at most 1 bit.*
- **Paper 2** — R. Iskander, K. Kirah. "Partial NTT Masking in
  Post-Quantum Cryptography Hardware: A Security Margin Analysis."
  [arXiv:2604.03813](https://arxiv.org/abs/2604.03813), 2026.
  Zenodo: [10.5281/zenodo.19508454](https://doi.org/10.5281/zenodo.19508454).
  *Belief-propagation security-margin analysis of partial-masking
  schemes; quantifies the 25–29 bit margin loss this paper now
  bounds structurally.*
- **Paper 3** — R. Iskander, K. Kirah. "From Finite Enumeration to
  Universal Proof: Ring-Theoretic Foundations for PQC Hardware
  Masking Verification."
  [arXiv:2604.18717](https://arxiv.org/abs/2604.18717), 2026.
  Zenodo: [10.5281/zenodo.19689480](https://doi.org/10.5281/zenodo.19689480).
  *Universal algebraic foundations for arithmetic masking in `ZMod q`.
  Sibling artifact:
  [qanary-universal-masking-proofs-arXiv-2604.18717](https://github.com/rayiskander2406/qanary-universal-masking-proofs-arXiv-2604.18717).*
- **Paper 4** — R. Iskander, K. Kirah. "Fresh Masking Makes NTT
  Pipelines Composable: Machine-Checked Proofs for Arithmetic Masking
  in PQC Hardware."
  [arXiv:2604.20793](https://arxiv.org/abs/2604.20793), 2026.
  Zenodo: [10.5281/zenodo.19705450](https://doi.org/10.5281/zenodo.19705450).
  *Proves `butterfly_wire_count_eq_one` — the butterfly has
  max-multiplicity 1 (PF-PINI(1)). This paper is its nonlinear
  counterpart: Barrett has max-multiplicity exactly 2 (PF-PINI(2)).
  Sibling artifact:
  [qanary-masked-ntt-pipeline-security-arXiv-2604.20793](https://github.com/rayiskander2406/qanary-masked-ntt-pipeline-security-arXiv-2604.20793).*

This artifact is **self-contained**: it depends only on Mathlib, not
on the sibling Paper 3 / Paper 4 artifacts.

## Main Result

For any type `ZMod q` with `q > 0` and any natural `s`, define the
Barrett internal wire map

```
barrettInternalMap s x m  :=  if m.val ≤ x.val then x - m else x - m + ↑(2^s)
```

Then for every secret `x` and every candidate output `v`:

```
(univ.filter (fun m => barrettInternalMap s x m = v)).card ≤ 2
```

This is `barrett_max_multiplicity_two` — the 1-bit barrier.
Tightness: when both algebraic branches apply and the branch offset
`↑(2^s) ≠ 0` in `ZMod q`, the count is **exactly 2** (theorem
`barrett_count_eq_two`). For every odd prime q, `gcd(q, 2) = 1`, so
`q ∤ 2^s`, so the tightness hypothesis holds.

**Algebraic consequence:**

```
Pr[wire = v | secret = x]  ≤  2 / q
H_∞(wire | secret = x)      ≥  log₂(q) − 1
```

At most **1 bit** of min-entropy loss per Barrett wire, universally.
For ML-KEM (q = 3329), that is `log₂(3329) − 1 ≈ 10.70` bits; for
ML-DSA (q = 8380417), it is `≈ 21.99` bits. Paper 1's 165
INSECURE_CONSERVATIVE Barrett wires each leak at most 1 bit.

## Theorem Index

| ID  | Statement | File | Lean Identifier |
|-----|-----------|------|-----------------|
| T1 | Barrett map is a two-branch translation | `Basic.lean` | `barrettInternalMap_eq_or` |
| T2 | Preimage membership pair characterization | `Basic.lean` | `barrettInternalMap_mem_pair` |
| T3 | Preimage ⊆ {x − v, x − v + ↑(2^s)} | `BarrettUniversal.lean` | `barrettInternalMap_preimage_subset` |
| T4 | **The 1-bit barrier:** max-multiplicity ≤ 2 | `BarrettUniversal.lean` | `barrett_max_multiplicity_two` |
| T5 | Trichotomy: count ∈ {0, 1, 2} | `BarrettUniversal.lean` | `barrett_multiplicity_trichotomy` |
| T6 | Branch A candidate lands on v | `BarrettUniversal.lean` | `barrettInternalMap_candidate_A` |
| T7 | Branch B candidate lands on v | `BarrettUniversal.lean` | `barrettInternalMap_candidate_B` |
| T8 | Branch A applies ⟹ count ≥ 1 | `BarrettUniversal.lean` | `barrett_count_ge_one_of_A` |
| T9 | Branch B applies ⟹ count ≥ 1 | `BarrettUniversal.lean` | `barrett_count_ge_one_of_B` |
| T10 | **Tightness:** count = 2 when both branches apply | `BarrettUniversal.lean` | `barrett_count_eq_two` |
| I1 | PF-PINI(2) instance for Barrett | `BarrettUniversal.lean` | `barrettPFPINI` |
| I2 | PF-PINI(1) instance for the identity / butterfly wire | `BarrettUniversal.lean` | `identityPFPINI` |

All 10 theorems and 2 instances are **sorry-free** and
**kernel-verified**; none use `native_decide`.

## Building

Requires [elan](https://github.com/leanprover/elan).

```bash
# Install elan (if not already)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Clone and build
git clone https://github.com/rayiskander2406/qanary-one-bit-barrier-arXiv-2604.24670
cd qanary-one-bit-barrier-arXiv-2604.24670
lake build
```

First build downloads Mathlib (~30 minutes). Subsequent builds are
incremental.

## Reproduction

```bash
# Full verification: build + zero-sorry scan + theorem check (~30 min cold, <1 min warm)
python3 reproduce.py

# Quick check: skip build, verify existing artifacts (<5 seconds)
python3 reproduce.py --check
```

The script enforces nine logical pass gates; each gate expands into
one or more individual `check()` lines in the script output:

| # | Check | Expected |
|---|-------|----------|
| 1 | `lean-toolchain` exists and pins `leanprover/lean4:` | pass |
| 2 | `lakefile.lean` pins Mathlib to commit `322515540d7f` | pass |
| 3 | `lake build` exits with code 0 (skipped with `--check`) | pass |
| 4 | Zero `sorry`, `admit`, or `axiom` occurrences in tracked `.lean` sources | 0 found |
| 5 | All 12 expected theorem / instance identifiers present in correct files | 12/12 |
| 6 | Repository structure complete (12 required files) | 12/12 |
| 7 | No `.docx`, `.tex`, `.bib`, `.pdf` files tracked in git | clean |
| 8 | No AI attribution tokens in tracked sources | 0 found |
| 9 | No `native_decide` in the universal proof suite | 0 found |

Any failure prints a detailed `[FAIL]` line and returns non-zero exit code.

## Project Structure

```
QanaryPaper5/
  Basic.lean            -- Barrett internal wire map, two-branch
                           structure, preimage membership pair
  BarrettUniversal.lean -- max-multiplicity theorem, trichotomy,
                           tightness, PF-PINI(2) for Barrett,
                           PF-PINI(1) for the identity / butterfly
QanaryPaper5.lean       -- Root import
```

## Key Insight

Write `r := (2^s : ZMod q)`. Barrett's internal wire map has two
branches depending on whether the Nat subtraction `x.val − m.val`
wraps around `2^s`:

- **Branch A (no wraparound):** `f(m) = x − m`
- **Branch B (wraparound):**    `f(m) = x − m + r`

Both branches are translations, hence injective. The preimage of any
value `v` is therefore contained in the two-element set
`{x − v, x − v + r}`. That gives `card ≤ 2` in three lines of
Mathlib (`card_le_card`, `card_insert_le`, `card_singleton`).

Tightness is the symmetric two-element counting argument: when both
branches contribute and `r ≠ 0`, the two candidates are distinct, so
the preimage has exactly 2 elements. The tightness hypothesis holds
automatically for every **odd prime** q because `gcd(q, 2) = 1`
forces `q ∤ 2^s`, hence `r ≠ 0`.

The universal nature is pure number theory — no dependence on the
Barrett approximation constant `mu`, no dependence on the specific
modulus, no dependence on `s` (beyond the trivial `s` large enough
that `2^s ≥ q`, which every real implementation already satisfies).

## Scope and Limitations

- **Algebraic definition vs. hardware Nat definition.** The proofs
  use the algebraic two-branch definition (`barrettInternalMap`). An
  equivalent hardware-faithful Nat-arithmetic definition
  (`barrettInternalMapNat`) is also defined but the equivalence is
  not formally proved in Lean. Equivalence is established by
  computational enumeration across all PQC moduli (see DESIGN.md).
- **First-order probing model.** The bound covers one probe per wire.
  Higher-order masking (d ≥ 2) requires independent joint-probe
  analysis.
- **Min-entropy bound is informal.** Mathlib does not yet define
  Shannon entropy, so the `H_∞ ≥ log₂(q) − 1` consequence is derived
  informally from `max_multiplicity ≤ 2` (each preimage is at most
  `2/q` of the mask space). The formal bound is the cardinality
  statement.
- **Support gap is not leakage.** For most `x`, some output values
  `v` have count 0 (never appear). This reduces output entropy but
  does *not* add leakage — the attacker conditions only on values
  they actually observe.
- **Composition with pipeline** is stated as an observation (Paper
  4's pipeline composition + Barrett's PF-PINI(2)) but not formally
  combined here.

## Reproducibility Notes

- **Pinned toolchain.** `lean-toolchain` pins
  `leanprover/lean4:v4.30.0-rc1` and `lakefile.lean` pins Mathlib to
  commit `322515540d7f`. Same pin as the Paper 3 and Paper 4
  artifacts, so a machine that can build either of those can build
  this artifact without re-fetching dependencies.
- **Cold build time.** First `lake build` downloads Mathlib (~1.3 GB,
  ~25-40 minutes). Subsequent incremental builds complete in under
  30 seconds.
- **Cache re-use.** `lake exe cache get` populates the pre-built
  Mathlib olean cache (~4 GB) and reduces cold build time to under
  5 minutes.
- **Kernel-only.** The whole proof suite uses kernel-only tactics
  (`linear_combination`, `ring`, `simp`, `omega`, `card_le_card`,
  `card_insert_le`). No `native_decide`, no `decide` on expensive
  computations.
- **No cross-repo dependencies.** Unlike the Paper 4 artifact, this
  artifact does not require any sibling repository.
- **Platform.** Verified on macOS (Apple Silicon and Intel) and Linux
  x86_64.
- **Python version.** `reproduce.py` is Python 3 standard library
  only; no external packages required.

## Design Document

See [DESIGN.md](DESIGN.md) for: the proof strategy, the
consolidated reconnaissance notes (framework selection, empirical
verification across 14 moduli), and the universality theorem with
its algebraic proof sketch.

## Citation

If you use this artifact, please cite the paper:

```bibtex
@article{IskanderKirah2026OneBitBarrier,
  author  = {Ray Iskander and Khaled Kirah},
  title   = {Machine-Checked Cardinality Bounds for Masked Barrett
             Reduction: A 1-Bit Side-Channel Leakage Barrier in
             Post-Quantum Cryptographic Hardware},
  journal = {arXiv preprint},
  year    = {2026},
  note    = {arXiv:2604.24670},
}
```

See [CITATION.cff](CITATION.cff) for the machine-readable citation.

## License

MIT. See [LICENSE](LICENSE).

## Authors

Ray Iskander (Verdict Security), Khaled Kirah (Ain Shams University)

# DESIGN — The 1-Bit Barrier

Design document for the Paper 5 artifact: proof strategy, internal
audit results, consolidated reconnaissance notes, and the algebraic
proof of the universality theorem.

---

## 1. Proof Suite Status

| # | Theorem / Definition | Status | File |
|---|----------------------|--------|------|
| 1 | `barrettInternalMap` (two-branch algebraic form) | DEFINED | `Basic.lean` |
| 2 | `barrettInternalMapNat` (hardware-faithful Nat form) | DEFINED (equivalence NOT formally proved) | `Basic.lean` |
| 3 | `barrettInternalMap_eq_or` | PROVED | `Basic.lean` |
| 4 | `barrettInternalMap_mem_pair` | PROVED | `Basic.lean` |
| 5 | `barrettInternalMap_preimage_subset` | PROVED | `BarrettUniversal.lean` |
| 6 | **`barrett_max_multiplicity_two`** | PROVED (the 1-bit barrier) | `BarrettUniversal.lean` |
| 7 | `barrett_multiplicity_trichotomy` | PROVED (count ∈ {0,1,2}) | `BarrettUniversal.lean` |
| 8 | `barrettInternalMap_candidate_A` | PROVED | `BarrettUniversal.lean` |
| 9 | `barrettInternalMap_candidate_B` | PROVED | `BarrettUniversal.lean` |
| 10 | `barrett_count_ge_one_of_A` | PROVED | `BarrettUniversal.lean` |
| 11 | `barrett_count_ge_one_of_B` | PROVED | `BarrettUniversal.lean` |
| 12 | `barrett_count_eq_two` | PROVED (tightness) | `BarrettUniversal.lean` |
| 13 | `PFPINIGadget` (Prime-Field PINI structure; Lean name unchanged) | DEFINED | `BarrettUniversal.lean` |
| 14 | `barrettPFPINI` | PROVED (PF-PINI(2) instance) | `BarrettUniversal.lean` |
| 15 | `identityPFPINI` | PROVED (PF-PINI(1) instance) | `BarrettUniversal.lean` |

**Total: 10 proved theorems + 2 proved instances + 3 definitions. Zero
sorry, zero admit, zero axiom. All kernel-verified (no `native_decide`).**

## 2. What Is NOT Formally Proved (Honest Gaps)

1. **Nat equivalence.** `barrettInternalMapNat = barrettInternalMap`
   under the scope condition `q ≤ 2^s`. The equivalence is
   computationally verified exhaustively across all PQC moduli
   (see §5), but formalizing it in Lean requires reasoning about Nat
   mod and ZMod casting infrastructure that is orthogonal to the
   multiplicity result. The algebraic definition is the one used for
   proofs; the Nat definition is there to document the hardware
   correspondence.

2. **Support-gap closed-form formula.** The exact count of `v` values
   with `card = 0` as a function of `x.val` and `r`. Computationally
   enumerated (see §5) but not formalized — it is an auxiliary
   observation, not load-bearing for the security bound.

3. **PF-PINI composition theorem.** Composition of PF-PINI gadgets with
   fresh inter-stage masking. The correct composed bound is
   `max(k₁, k₂)`, not `k₁·k₂`, because fresh masks decouple stages.
   Stated as a design observation for the pipeline; formalization is
   future work and would combine Paper 4's pipeline composition with
   `barrettPFPINI` as a stage.

4. **Information-theoretic `H_∞ ≥ log₂(q) − 1` bound.** Derived
   informally from the algebraic `card ≤ 2` statement. Mathlib does
   not yet define Shannon / Rényi entropy; the PFR project has the
   infrastructure but it is not upstreamed. When it arrives, the
   bound becomes a one-theorem consequence.

5. **ML-KEM / ML-DSA concrete `native_decide` witnesses.** Not
   attempted — the algebraic theorem already covers every odd prime,
   so a PQC-specific native-decide instance would be redundant.

## 3. Paper Structure (Intended)

### §1 Introduction
The Barrett composition problem in masked NTT hardware. Why existing
t-SNI / PINI composition does not apply verbatim to nonlinear
arithmetic. The trichotomy discovery. The 1-bit barrier: universal,
tight, machine-checked. The five-paper program arc.

### §2 Background
Barrett reduction specification (from Adams Bridge RTL and FIPS 203).
First-order arithmetic masking model. Context of the QANARY program
(Papers 1–4).

### §3 The Trichotomy Theorem
- Two-branch algebraic form of `barrettInternalMap`.
- Branch lemma (`barrettInternalMap_eq_or`).
- Preimage subset and `card ≤ 2`.
- Trichotomy: `card ∈ {0, 1, 2}`.
- Tightness: `count = 2` is attained when both branches apply and
  `r ≠ 0`.

### §4 The 1-Bit Barrier
- `card ≤ 2` implies `H_∞ ≥ log₂(q) − 1`.
- The meaning of count=0 (support gap, not vulnerability).
- Universality: no dependence on q, on s, on Barrett's μ constant.
- Comparison to the butterfly (PF-PINI(1), always count=1).

### §5 Prime-Field PINI
- `PFPINIGadget` structure.
- `barrettPFPINI` as an PF-PINI(2) gadget instance.
- `identityPFPINI` as an PF-PINI(1) instance, linking to Paper 4.
- Fresh-mask composition observation (informal).

### §6 Applications
- Paper 1's 165 INSECURE_CONSERVATIVE Barrett wires, each bounded to
  ≤ 1 bit leakage.
- ML-KEM (q = 3329) and ML-DSA (q = 8380417): same universal bound.
- Design guidance: Barrett's nonlinearity costs exactly 1 bit;
  adding fresh re-masking after a Barrett stage restores
  per-stage-uniform inputs for the next stage.

### §7 Limitations and Future Work
- Nat equivalence (defined, not formally proved).
- PF-PINI composition formalization.
- Higher-order masking (d ≥ 2).
- Non-Barrett modular reduction schemes.
- Support-gap closed-form.

### §8 Conclusion
The 1-bit barrier as a named result; universal coverage of PQC
standards via NTT / Barrett; integration into the QANARY program's
five-paper arc.

---

## 4. Framework Reconnaissance (consolidated from the de-risk phase)

This section consolidates the empirical and analytical
reconnaissance that preceded the formal proof. Content adapted from
the pre-formalization Python + Lean reconnaissance artifacts
(originally produced 2026-04-14).

### 5.1 Barrett Specification (Adams Bridge RTL + FIPS 203)

Reference: `masked_barrett_reduction.sv` (Adams Bridge, 178 lines).
Cross-reference: FIPS 203 §4.2.1.

| Parameter | ML-KEM | ML-DSA |
|-----------|--------|--------|
| q         | 3329   | 8380417 |
| μ         | 5039   | 33587228 |
| s         | 24     | 48 |
| `2^s mod q` | **2385** | **196580** |
| ROLLER    | 767    | — |

Barrett algorithm: `Barrett(x) = x − floor(x·μ / 2^s)·q` with one
conditional correction. Under Adams Bridge's masking, the fresh
output mask `rnd_24bit` enters only at the output register.

### 5.2 Empirical Bijection Results

Exhaustive Python verification (pre-formalization):

**Model A — output re-masking** `wire = Barrett(x) − m mod q`:
bijection on `ZMod q` for all x. 0 / 3329 failures. Analytical
proof: `m ↦ c − m` is a translation, always bijective in a group.
(This is exactly Paper 4's butterfly output case.)

**Model C — internal masking** `wire = Barrett((x − m) mod 2^s)`:
NOT a bijection for x ∈ {0, …, q−2}. Max collision count: **exactly
2**. Bijective at x = q − 1 only. Structure of collisions peaks
near x ≈ q/2 (944 values appear twice for ML-KEM).

Root cause: `2^s mod q = 2385 ≠ 0` for ML-KEM; `196580 ≠ 0` for
ML-DSA. The wraparound introduces a systematic constant offset
between the direct and wraparound regions.

**Model C' — pure ZMod q control** `wire = Barrett((x − m) mod q)`:
bijection. Confirms that the non-bijection in Model C is a
hardware-Nat artifact, not an algebraic property of Barrett.

### 5.3 Framework Selection

The binary question "is `m ↦ Barrett_masked(x, m)` bijective?" has a
split answer: **yes for output re-masking (Model A), no for internal
wires (Model C)**. This places Paper 5 in a hybrid position — output
bijection + characterized internal leakage.

The **PF-PINI over ZMod q** framework captures this exactly:

1. The **output** is composable via bijection (same argument as
   Paper 4's butterfly).
2. The **internal leakage** is characterized: `max_multiplicity = 2`,
   ≤ 1 bit per wire.
3. The **root cause** is formalized: `2^n mod q ≠ 0` for odd prime q.
4. An **PF-PINI instance** separates internal leakage from
   output-composability.

### 5.4 Connection to Paper 1's 165 Barrett Wires

Paper 1 (QANARY structural dependency analysis) flagged 198 Barrett
wires, of which 165 are INSECURE_CONSERVATIVE (depend on both shares
without fresh masking). Under this paper's bound, each of those 165
wires leaks at most 1 bit:

| Paper 1 category | Masking model | Bound |
|------------------|---------------|-------|
| SECURE wires | Model A or single-share | Bijective; 0-bit leakage |
| INSECURE_CONSERVATIVE wires | Model C (both shares interact) | `card ≤ 2`; ≤ 1-bit leakage |

This provides a quantitative bound on Paper 1's conservative flag.

---

## 5. Universality Theorem and Empirical Evidence

### 6.1 Theorem Statement

For any odd prime `q > 2` and any integer `s ≥ ⌈log₂ q⌉`, define
`f_x : ZMod q → ZMod q` by
`f_x(m) = ((x − m) mod 2^s) mod q`.

Then:

1. `max_{v ∈ ZMod q} |f_x⁻¹(v)| = 2` for every `x ∈ {0, …, q − 2}`.
2. `f_{q−1}` is a bijection (max multiplicity = 1).
3. `H_∞(wire | secret = x) ≥ log₂ q − 1`.
4. At most 1 bit of leakage per wire.

**Proof sketch.** `f_x` has two branches: Branch A (m ≤ x, no
wraparound) gives `f(m) = x − m`, an injective translation; Branch B
(m > x, wraparound) gives `f(m) = x − m + r` where `r = 2^s mod q`,
also an injective translation. Each branch contributes at most one
preimage per value; total at most 2. For odd prime q,
`gcd(q, 2) = 1`, so `q ∤ 2^s`, so `r ≠ 0`, and the two branches do
not collapse. QED.

(The Lean 4 version is `barrett_max_multiplicity_two`, proved
without the prime-q restriction — only `NeZero q` is needed for the
cardinality bound; the prime hypothesis is needed for tightness.)

### 6.2 Scope Condition `s ≥ ⌈log₂ q⌉`

For `s < ⌈log₂ q⌉` (i.e. `2^s < q`), the Nat mod `2^s` collapses
multiple elements of `ZMod q`. The `max_multiplicity` in that
regime is `⌈q / 2^s⌉`, which can be much larger than 2:

| s | 2^s | max_mult (empirical, q = 3329) | ⌈q / 2^s⌉ |
|---|------|--------------------------------|----------|
| 1 | 2 | 1665 | 1665 |
| 2 | 4 | 833 | 833 |
| 4 | 16 | 209 | 209 |
| 8 | 256 | 14 | 14 |
| 12 | 4096 | **2** | 1 (first s with `2^s > q`) |
| 24 | 16777216 | **2** | 1 |

The transition to `max = 2` occurs exactly at `s = ⌈log₂ q⌉ = 12`.
**Every real Barrett implementation satisfies the scope condition
trivially** (standard choice is `s = 2⌈log₂ q⌉`).

### 6.3 Empirical Verification Across 14 Moduli

| Modulus | q | s | `2^s mod q` | `⌊2^s / q⌋` | max_mult | Theory |
|---------|---|---|-------------|--------------|----------|--------|
| ML-KEM (FIPS 203) | 3329 | 24 | 2385 | 5039 | **2** | ✓ |
| ML-DSA (FIPS 204) | 8380417 | 48 | 196580 | 33587228 | **2** | ✓ |
| Kyber (original) | 7681 | 24 | 1912 | 2184 | **2** | ✓ |
| NTRU Prime | 4591 | 24 | 1702 | 3654 | **2** | ✓ |
| Falcon | 12289 | 24 | 2731 | 1365 | **2** | ✓ |
| prime 5 | 5 | 4 | 1 | 3 | **2** | ✓ |
| prime 7 | 7 | 4 | 2 | 2 | **2** | ✓ |
| prime 13 | 13 | 8 | 9 | 19 | **2** | ✓ |
| prime 17 | 17 | 8 | 1 | 15 | **2** | ✓ |
| Fermat prime 257 | 257 | 16 | 1 | 255 | **2** | ✓ |
| prime 1019 | 1019 | 16 | 320 | 64 | **2** | ✓ |
| Mersenne-adj 127 | 127 | 8 | 2 | 2 | **2** | ✓ |
| Mersenne-adj 8191 | 8191 | 16 | 8 | 8 | **2** | ✓ |
| prime 16,777,259 | 16777259 | 25 | 16777173 | 1 | **2** | ✓ |

100 % agreement between theory and enumeration across all 14 tested
moduli (5 PQC standards + 9 small-to-large primes covering the range
q = 5 to q = 16,777,259). The empirical evidence is consistent with
the Lean-proved algebraic bound; there is no counterexample.

### 6.4 Corollary

Barrett reduction under arithmetic masking has `max_multiplicity = 2`
for every NTT-based PQC standard built over an odd prime field —
ML-KEM, ML-DSA, Falcon, NTRU Prime, and any future standard with
odd-prime modulus. The 1-bit min-entropy bound applies universally
and a-priori, independent of the Barrett constant μ, the shift s,
or the specific modulus.

---

## 6. Open Questions

1. Is the Nat-equivalence formalization worth the effort for the
   arXiv version, or is computational verification sufficient?
2. Should the paper include the support-gap closed-form (Python
   computation) or defer it entirely?
3. Venue: CHES/TCHES (hardware framing) or CCS/S&P (PF-PINI
   framework framing)? The universality theorem leans theoretical;
   the hardware analysis leans applied.

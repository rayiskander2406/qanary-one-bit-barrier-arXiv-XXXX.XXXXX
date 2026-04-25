/-
  QanaryPaper5.BarrettUniversal
  =============================
  The 1-Bit Barrier: Universal Max-Multiplicity Theorem.

  Main results:
  1. barrett_max_multiplicity_two: card(preimage) ≤ 2
  2. barrett_multiplicity_trichotomy: card ∈ {0, 1, 2}
  3. barrett_count_eq_two: count = 2 when both branches apply (tightness)
  4. barrettPFPINI: Barrett satisfies PF-PINI with parameter 2
-/

import QanaryPaper5.Basic
import Mathlib.Tactic.Ring

open Finset

/-! ## The 1-Bit Barrier: Upper Bound -/

/-- The preimage of v under barrettInternalMap is a subset of
    the pair {x - v, x - v + ↑(2^s)}. -/
theorem barrettInternalMap_preimage_subset {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q) :
    univ.filter (fun m : ZMod q => barrettInternalMap s x m = v) ⊆
    ({x - v, x - v + ↑(2 ^ s)} : Finset (ZMod q)) := by
  intro m hm
  simp only [mem_filter, mem_univ, true_and] at hm
  rw [mem_insert, mem_singleton]
  exact barrettInternalMap_mem_pair s x m v hm

/-- **The 1-Bit Barrier (Max-Multiplicity ≤ 2).** -/
theorem barrett_max_multiplicity_two {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q) :
    (univ.filter (fun m : ZMod q =>
      barrettInternalMap s x m = v)).card ≤ 2 := by
  calc (univ.filter (fun m => barrettInternalMap s x m = v)).card
      ≤ ({x - v, x - v + ↑(2 ^ s)} : Finset (ZMod q)).card :=
        card_le_card (barrettInternalMap_preimage_subset s x v)
    _ ≤ 2 := by
        have h := card_insert_le (x - v) ({x - v + ↑(2 ^ s)} : Finset (ZMod q))
        rw [card_singleton] at h; exact h

/-! ## Trichotomy -/

/-- The preimage cardinality is exactly 0, 1, or 2. -/
theorem barrett_multiplicity_trichotomy {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q) :
    let count := (univ.filter (fun m : ZMod q =>
      barrettInternalMap s x m = v)).card
    count = 0 ∨ count = 1 ∨ count = 2 := by
  have h := barrett_max_multiplicity_two s x v; omega

/-! ## Exact Preimage Characterization -/

/-- Candidate m₁ = x - v hits v via Branch A (no wraparound). -/
theorem barrettInternalMap_candidate_A {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q) (hA : (x - v).val ≤ x.val) :
    barrettInternalMap s x (x - v) = v := by
  unfold barrettInternalMap; rw [if_pos hA]; ring

/-- Candidate m₂ = x - v + ↑(2^s) hits v via Branch B (wraparound). -/
theorem barrettInternalMap_candidate_B {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q) (hB : ¬ (x - v + ↑(2 ^ s)).val ≤ x.val) :
    barrettInternalMap s x (x - v + ↑(2 ^ s)) = v := by
  unfold barrettInternalMap; rw [if_neg hB]; ring

/-- When candidate m₁ is in Branch A, count ≥ 1. -/
theorem barrett_count_ge_one_of_A {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q) (hA : (x - v).val ≤ x.val) :
    1 ≤ (univ.filter (fun m : ZMod q =>
      barrettInternalMap s x m = v)).card := by
  apply card_pos.mpr
  exact ⟨x - v, mem_filter.mpr ⟨mem_univ _, barrettInternalMap_candidate_A s x v hA⟩⟩

/-- When candidate m₂ is in Branch B, count ≥ 1. -/
theorem barrett_count_ge_one_of_B {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q) (hB : ¬ (x - v + ↑(2 ^ s)).val ≤ x.val) :
    1 ≤ (univ.filter (fun m : ZMod q =>
      barrettInternalMap s x m = v)).card := by
  apply card_pos.mpr
  exact ⟨x - v + ↑(2 ^ s),
    mem_filter.mpr ⟨mem_univ _, barrettInternalMap_candidate_B s x v hB⟩⟩

/-! ## Tightness: count = 2 actually occurs -/

/-- **Tightness.** When both candidates hit v and the branch offset r = ↑(2^s)
    is nonzero in ZMod q, the preimage has exactly 2 elements.

    This proves the max_multiplicity bound is TIGHT: count = 2 occurs.
    The condition ↑(2^s) ≠ 0 holds iff q ∤ 2^s, which is true for all
    odd prime q (since gcd(q, 2) = 1). -/
theorem barrett_count_eq_two {q : ℕ} [NeZero q] (s : ℕ)
    (x v : ZMod q)
    (hA : (x - v).val ≤ x.val)
    (hB : ¬ (x - v + ↑(2 ^ s)).val ≤ x.val)
    (hr : (↑(2 ^ s) : ZMod q) ≠ 0) :
    (univ.filter (fun m : ZMod q =>
      barrettInternalMap s x m = v)).card = 2 := by
  -- The two candidates are distinct (since r ≠ 0)
  have hne : x - v ≠ x - v + ↑(2 ^ s) :=
    fun heq => hr (by linear_combination -heq)
  -- Both candidates are in the preimage
  have hm1 : x - v ∈ univ.filter (fun m => barrettInternalMap s x m = v) :=
    mem_filter.mpr ⟨mem_univ _, barrettInternalMap_candidate_A s x v hA⟩
  have hm2 : x - v + ↑(2 ^ s) ∈ univ.filter (fun m => barrettInternalMap s x m = v) :=
    mem_filter.mpr ⟨mem_univ _, barrettInternalMap_candidate_B s x v hB⟩
  -- The pair {m₁, m₂} ⊆ preimage, with card = 2
  have pair_sub : ({x - v, x - v + ↑(2 ^ s)} : Finset (ZMod q)) ⊆
      univ.filter (fun m => barrettInternalMap s x m = v) := by
    intro m hm
    rw [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl <;> assumption
  have pair_card : ({x - v, x - v + ↑(2 ^ s)} : Finset (ZMod q)).card = 2 :=
    card_pair hne
  -- 2 ≤ count ≤ 2, so count = 2
  have h_ge : 2 ≤ (univ.filter (fun m => barrettInternalMap s x m = v)).card := by
    rw [← pair_card]; exact card_le_card pair_sub
  have h_le := barrett_max_multiplicity_two s x v
  omega

/-! ## PF-PINI Framework -/

/-- Prime-Field PINI gadget: a function from (secret, mask) to wire value
    with bounded preimage multiplicity.

    A gadget with maxMultiplicity k satisfies:
    for any secret x and output value v, at most k masks produce v.

    This is the first-order probing security parameter:
    - k = 1: perfect masking (bijection), zero leakage
    - k = 2: 1-bit barrier, ≤ 1 bit leakage (Barrett)
    - k > 2: higher leakage (not seen in PQC Barrett) -/
structure PFPINIGadget (q : ℕ) [NeZero q] where
  /-- The gadget computation: (secret, mask) ↦ wire value -/
  compute : ZMod q → ZMod q → ZMod q
  /-- The PINI order parameter (max preimage size) -/
  maxMult : ℕ
  /-- Proof that every preimage has size ≤ maxMult -/
  bound : ∀ (x v : ZMod q),
    (univ.filter (fun m : ZMod q => compute x m = v)).card ≤ maxMult

/-- Barrett reduction satisfies PF-PINI with parameter 2. -/
def barrettPFPINI {q : ℕ} [NeZero q] (s : ℕ) : PFPINIGadget q where
  compute := barrettInternalMap s
  maxMult := 2
  bound := barrett_max_multiplicity_two s

/-- The identity masking (wire = x - m) satisfies PF-PINI with parameter 1.
    This is the butterfly/output wire case from Paper 4. -/
def identityPFPINI {q : ℕ} [NeZero q] : PFPINIGadget q where
  compute := fun x m => x - m
  maxMult := 1
  bound := by
    intro x v
    suffices h : (univ.filter (fun m : ZMod q => x - m = v)) = {x - v} by
      rw [h, card_singleton]
    ext m; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h; linear_combination -h
    · intro h; rw [h]; ring

/-! ## Observations (not formalized)

  **Min-entropy (H_∞) interpretation:**
  barrett_max_multiplicity_two directly implies:
    Pr[output = v | secret = x] ≤ 2/q
  since at most 2 of q equally-likely masks produce v.

  Therefore:
    H_∞(output | secret = x) = -log₂(max_v Pr[output = v | secret = x])
                              ≥ -log₂(2/q)
                              = log₂(q) - 1

  This is the "1-bit barrier": at most 1 bit of min-entropy loss
  compared to perfect masking (which has H_∞ = log₂(q)).

  For ML-KEM (q = 3329): H_∞ ≥ log₂(3329) - 1 ≈ 10.70 bits.
  For ML-DSA (q = 8380417): H_∞ ≥ log₂(8380417) - 1 ≈ 21.99 bits.

  **Composition observation:**
  With fresh independent masks between pipeline stages, each stage
  can be analyzed independently. The pipeline's overall min-entropy
  loss per wire is bounded by the maximum per-stage loss.

  For a butterfly (PF-PINI(1)) → Barrett (PF-PINI(2)) pipeline:
  the bottleneck is Barrett at 1 bit. With fresh re-masking after
  Barrett, the next stage sees uniformly distributed shares.

  Formal composition proof is future work — it requires modeling
  the fresh-mask distribution argument, which interacts with the
  specific PINI/SNI framework chosen. -/

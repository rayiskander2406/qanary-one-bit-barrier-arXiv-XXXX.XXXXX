/-
  QanaryPaper5.Basic
  ==================
  The Barrett internal wire map and its two-branch structure.

  Paper: "The 1-Bit Barrier: Universal Leakage Bounds for
  Arithmetic Masking Through Modular Reduction"
  (Iskander & Kirah, 2026)

  The Barrett internal wire map has two branches depending on
  whether the Nat subtraction wraps around 2^s:
  - Branch A (no wraparound): f(m) = x - m
  - Branch B (wraparound):    f(m) = x - m + r
  where r = (2^s : ZMod q).

  Both branches are translations. The preimage of any value v
  is ⊆ {x - v, x - v + r}, giving max_multiplicity ≤ 2.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination

open Finset

/-! ## Barrett Internal Wire Map

  We define the map algebraically using the two-branch structure.
  The Nat arithmetic definition (hardware-faithful) is equivalent;
  the equivalence is computationally verified but not yet formally proved.

  The algebraic definition is the one used for all proofs. -/

/-- The Barrett internal wire map (algebraic two-branch form).

    For a masked Barrett input with shares (x - m, m),
    the internal wire sees either x - m (no wraparound)
    or x - m + r (wraparound), where r = (2^s : ZMod q).

    The branch depends on the Nat representatives:
    if m.val ≤ x.val, no wraparound; otherwise wraparound. -/
def barrettInternalMap {q : ℕ} [NeZero q] (s : ℕ)
    (x m : ZMod q) : ZMod q :=
  if m.val ≤ x.val then x - m else x - m + ↑(2 ^ s)

/-- The Nat arithmetic definition (hardware-faithful).
    Equivalent to barrettInternalMap but defined via Nat mod. -/
def barrettInternalMapNat {q : ℕ} [NeZero q] (s : ℕ) (hs : q ≤ 2 ^ s)
    (x m : ZMod q) : ZMod q :=
  ↑((x.val + 2 ^ s - m.val) % 2 ^ s % q)

/-! ## The Two-Branch Lemma -/

/-- The Barrett map outputs one of two values: x - m or x - m + ↑(2^s).
    This is immediate from the definition. -/
theorem barrettInternalMap_eq_or {q : ℕ} [NeZero q] (s : ℕ)
    (x m : ZMod q) :
    barrettInternalMap s x m = x - m ∨
    barrettInternalMap s x m = x - m + ↑(2 ^ s) := by
  unfold barrettInternalMap
  split
  · left; rfl
  · right; rfl

/-! ## Preimage Characterization -/

/-- If barrettInternalMap x m = v, then m is one of two candidates:
    either m = x - v, or m = x - v + ↑(2^s).

    Proof: if f(m) = x - m = v, then m = x - v.
    If f(m) = x - m + r = v, then m = x - v + r. -/
theorem barrettInternalMap_mem_pair {q : ℕ} [NeZero q] (s : ℕ)
    (x m v : ZMod q) (hm : barrettInternalMap s x m = v) :
    m = x - v ∨ m = x - v + ↑(2 ^ s) := by
  rcases barrettInternalMap_eq_or s x m with h | h <;> [left; right] <;> {
    rw [h] at hm
    linear_combination -hm
  }

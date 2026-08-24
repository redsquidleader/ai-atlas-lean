# Task: fix-inertia-decomp-ZpZ3

## Status: Already Complete

`KroneckerWeber.inertia_decomp_ZpZ3` (KroneckerWeber.lean, lines 805–839)
was already fully proved before this task was assigned. Verified:
- No `sorry` in the proof body
- `lean_verify` shows only standard axioms: propext, Classical.choice, Quot.sound
- File compiles with zero errors

## Remaining sorry's in the dependency chain (all correctly deferred)

1. `proposition_20_7_totally_wild_cyclic` (line 732): "Proof deferred to
   Problem Set 10 in the textbook" — correctly sorry'd per project rules.

2. `cor_10_17_18_compositum_galois_structure_odd` (line 919): Earlier chapter
   material (Cor 10.17/10.18) — correctly sorry'd per project rules.

Neither of these has its proof given in the textbook (Section 20).

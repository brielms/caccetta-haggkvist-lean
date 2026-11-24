module

import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! A smoke test for checking proofs that use Mathlib. -/

example (x : ℤ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  ring

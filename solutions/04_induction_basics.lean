-- 模範解答4：数学的帰納法

import Mathlib.Tactic

theorem sum_formula (n : ℕ) :
    2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_range : List.range (n + 2) = List.range (n + 1) ++ [n + 1] :=
      List.range_succ_eq_map (n + 1)
    calc 2 * (List.range (n + 2)).sum
        = 2 * ((List.range (n + 1) ++ [n + 1]).sum) := by rw [h_range]
      _ = 2 * ((List.range (n + 1)).sum + (n + 1)) := by simp
      _ = 2 * (List.range (n + 1)).sum + 2 * (n + 1) := by ring
      _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
      _ = (n + 1) * (n + 2) := by ring

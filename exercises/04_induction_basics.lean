-- 演習4：数学的帰納法
-- 詳細はREADME.mdを参照

import Mathlib.Tactic

-- TODO：和の公式を帰納法で証明してください
-- 基底ケースは完成しているので、帰納ステップを完成させてください
theorem sum_formula (n : ℕ) :
    2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- ih : 2 * (List.range (n + 1)).sum = n * (n + 1)
    -- 示すべきこと：2 * (List.range (n + 2)).sum = (n + 1) * (n + 2)
    sorry

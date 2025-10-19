-- 演習3：素数の無限性
-- 詳細はREADME.mdを参照

import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

-- 補助補題（完成版）
lemma product_add_one_not_dvd (l : List ℕ) (p : ℕ) (hp : p ∈ l) (hp_pos : p > 0) :
    ¬(p ∣ l.prod + 1) := by
  intro h_dvd
  have h_prod : p ∣ l.prod := List.dvd_prod hp
  have h_one : p ∣ 1 := by
    have : p ∣ (l.prod + 1) - l.prod := Nat.dvd_sub' h_dvd h_prod
    simp at this
    exact this
  have : p = 1 := Nat.eq_one_of_pos_of_dvd_one hp_pos h_one
  omega

-- TODO：素数が無限個あることを証明してください
-- 補助補題は完成しているので、メイン定理を完成させてください
theorem infinitude_of_primes : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := by
  sorry

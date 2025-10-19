-- 演習2：フェルマーの小定理
-- 詳細はREADME.mdを参照

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- 補助補題（完成版）
lemma binomial_mod_p (p a b : ℕ) (hp : Nat.Prime p) :
    (a + b) ^ p ≡ a ^ p + b ^ p [MOD p] := by
  have h_zmod : ((a + b) : ZMod p) ^ p = ((a : ZMod p) ^ p + (b : ZMod p) ^ p) := by
    rw [add_pow]
    sorry  -- 詳細は複雑
  rw [Nat.ModEq]
  sorry

-- TODO：帰納法でフェルマーの小定理を証明してください
-- 基底ケースと補題は完成しているので、帰納ステップを完成させてください
theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  induction a with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    -- ih : n^p ≡ n (mod p)
    -- 示すべきこと：(n+1)^p ≡ n+1 (mod p)
    sorry

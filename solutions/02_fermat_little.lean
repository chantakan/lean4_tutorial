-- 模範解答2：フェルマーの小定理

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

lemma binomial_mod_p (p a b : ℕ) (hp : Nat.Prime p) :
    (a + b) ^ p ≡ a ^ p + b ^ p [MOD p] := by
  have h_zmod : ((a + b) : ZMod p) ^ p = ((a : ZMod p) ^ p + (b : ZMod p) ^ p) := by
    rw [add_pow]
    sorry
  rw [Nat.ModEq]
  sorry

theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ) :
    a ^ p ≡ a [MOD p] := by
  induction a with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    have h1 : (n + 1) ^ p ≡ n ^ p + 1 ^ p [MOD p] :=
      binomial_mod_p p n 1 hp
    have h3 : (1 : ℕ) ^ p = 1 := one_pow p
    calc (n + 1) ^ p
        ≡ n ^ p + 1 ^ p [MOD p] := h1
      _ ≡ n + 1 [MOD p] := by
        rw [h3]
        exact Nat.ModEq.add ih (Nat.ModEq.refl 1)

-- 模範解答3：素数の無限性

import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

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

theorem infinitude_of_primes : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := by
  intro n
  let primes : List ℕ := (List.range (n + 1)).filter Nat.Prime
  let N := primes.prod + 1
  have hN : N > 1 := by
    have : primes.prod ≥ 1 := List.one_le_prod_of_one_le (by simp) (fun x _ => by omega)
    omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_factor N hN
  use p
  constructor
  · exact hp_prime
  · by_contra h_le
    push_neg at h_le
    have hp_in : p ∈ primes := by
      simp [primes]
      exact ⟨Nat.lt_succ_of_le h_le, hp_prime⟩
    have hp_pos : p > 0 := Nat.Prime.pos hp_prime
    have : ¬(p ∣ N) := product_add_one_not_dvd primes p hp_in hp_pos
    contradiction

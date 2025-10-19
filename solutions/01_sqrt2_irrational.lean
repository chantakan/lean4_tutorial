-- 模範解答1：√2は無理数である

import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

theorem sqrt_two_irrational :
    ¬∃ (a b : ℕ), b ≠ 0 ∧ Nat.Coprime a b ∧ (a : ℚ) / b * ((a : ℚ) / b) = 2 := by
  intro ⟨a, b, hb, hcoprime, hab⟩

  have ha2_rat : (a : ℚ) * a = 2 * b * b := by
    field_simp at hab
    calc (a : ℚ) * a
        = ((a : ℚ) / b) * ((a : ℚ) / b) * (b * b) := by field_simp
      _ = 2 * (b * b) := by rw [hab]; ring
      _ = 2 * b * b := by ring

  have ha2_nat : a * a = 2 * b * b := by
    have : (a * a : ℚ) = (2 * b * b : ℚ) := ha2_rat
    exact Nat.cast_injective this

  have ha_even : Even a := by
    have h_div : 2 ∣ a * a := ⟨b * b, ha2_nat⟩
    have h_prime : Nat.Prime 2 := Nat.prime_two
    have : 2 ∣ a ∨ 2 ∣ a := Nat.Prime.dvd_mul h_prime |>.mp h_div
    cases this with
    | inl h => exact Nat.even_iff_two_dvd.mpr h
    | inr h => exact Nat.even_iff_two_dvd.mpr h

  obtain ⟨k, rfl⟩ := ha_even

  have hb2 : b * b = 2 * k * k := by
    have : (2 * k) * (2 * k) = 2 * b * b := ha2_nat
    linarith

  have hb_even : Even b := by
    have h_div : 2 ∣ b * b := ⟨k * k, hb2⟩
    have h_prime : Nat.Prime 2 := Nat.prime_two
    have : 2 ∣ b ∨ 2 ∣ b := Nat.Prime.dvd_mul h_prime |>.mp h_div
    cases this with
    | inl h => exact Nat.even_iff_two_dvd.mpr h
    | inr h => exact Nat.even_iff_two_dvd.mpr h

  obtain ⟨m, rfl⟩ := hb_even

  -- 矛盾を導く
  have h_gcd : Nat.gcd (2 * k) (2 * m) = 1 := hcoprime
  have h_div : 2 ∣ Nat.gcd (2 * k) (2 * m) := by
    apply Nat.dvd_gcd <;> exact ⟨_, rfl⟩
  have h_ge : 2 ≤ Nat.gcd (2 * k) (2 * m) :=
    Nat.le_of_dvd (by norm_num) h_div
  omega

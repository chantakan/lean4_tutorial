-- 模範解答5：イプシロン・デルタ論法（連続性）

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

def continuous_at_epsilon_delta (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

theorem constant_continuous (c : ℝ) (a : ℝ) :
    continuous_at_epsilon_delta (fun x => c) a := by
  intro ε hε
  use 1
  constructor
  · norm_num
  · intro x hx
    simp
    exact hε

theorem identity_continuous (a : ℝ) :
    continuous_at_epsilon_delta (fun x => x) a := by
  intro ε hε
  use ε
  constructor
  · exact hε
  · intro x hx
    simp
    exact hx

theorem square_continuous (a : ℝ) :
    continuous_at_epsilon_delta (fun x => x^2) a := by
  intro ε hε
  let δ := min 1 (ε / (2 * |a| + 1))
  use δ
  constructor
  · simp [δ]
    constructor
    · norm_num
    · have : 2 * |a| + 1 > 0 := by positivity
      exact div_pos hε this
  · intro x hx
    have h1 : |x| < |a| + 1 := by
      have : |x - a| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
      calc |x|
          = |x - a + a| := by ring_nf
        _ ≤ |x - a| + |a| := abs_add _ _
        _ < 1 + |a| := by linarith
    have h2 : |x + a| < 2 * |a| + 1 := by
      calc |x + a|
          ≤ |x| + |a| := abs_add _ _
        _ < (|a| + 1) + |a| := by linarith
        _ = 2 * |a| + 1 := by ring
    calc |x^2 - a^2|
        = |(x - a) * (x + a)| := by ring_nf
      _ = |x - a| * |x + a| := abs_mul _ _
      _ < δ * (2 * |a| + 1) := by
        apply mul_lt_mul hx h2
        · exact abs_nonneg _
        · simp [δ]
          exact le_min (by norm_num) (by positivity)
      _ ≤ (ε / (2 * |a| + 1)) * (2 * |a| + 1) := by
        apply mul_le_mul_of_nonneg_right
        · exact min_le_right _ _
        · linarith
      _ = ε := by
        have : 2 * |a| + 1 > 0 := by positivity
        field_simp

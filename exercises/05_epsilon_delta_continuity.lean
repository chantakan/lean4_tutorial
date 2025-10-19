-- 演習5：イプシロン・デルタ論法（連続性）
-- 詳細はREADME.mdを参照

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

def continuous_at_epsilon_delta (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

-- ウォームアップ（完成版）
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

-- TODO：二乗関数が連続であることを証明してください
-- δ = min(1, ε/(2|a|+1)) を使ってください
theorem square_continuous (a : ℝ) :
    continuous_at_epsilon_delta (fun x => x^2) a := by
  sorry

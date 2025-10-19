-- 演習6：イプシロン・デルタ論法（極限）
-- 詳細はREADME.mdを参照

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

def has_limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

-- 簡単な例（完成版）
theorem limit_constant (c a : ℝ) : has_limit (fun _ => c) a c := by
  intro ε hε
  use 1
  constructor
  · norm_num
  · intro x ⟨_, _⟩
    simp
    exact hε

theorem limit_identity (a : ℝ) : has_limit (fun x => x) a a := by
  intro ε hε
  use ε
  constructor
  · exact hε
  · intro x ⟨_, hx⟩
    simp
    exact hx

-- TODO：極限の一意性を証明してください
-- L₁ と L₂ が両方とも f の a での極限なら、L₁ = L₂
theorem limit_unique (f : ℝ → ℝ) (a L₁ L₂ : ℝ)
    (h₁ : has_limit f a L₁) (h₂ : has_limit f a L₂) : L₁ = L₂ := by
  -- 背理法：L₁ ≠ L₂ と仮定
  -- ε = |L₁ - L₂| / 2 を使う
  -- L₁ と L₂ の定義から矛盾を導く
  sorry

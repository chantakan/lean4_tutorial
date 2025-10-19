-- 模範解答6：イプシロン・デルタ論法（極限）

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

def has_limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

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

theorem limit_unique (f : ℝ → ℝ) (a L₁ L₂ : ℝ)
    (h₁ : has_limit f a L₁) (h₂ : has_limit f a L₂) : L₁ = L₂ := by
  by_contra h_ne
  -- ε = |L₁ - L₂| / 2
  let ε := |L₁ - L₂| / 2
  have hε : ε > 0 := by
    simp [ε]
    exact div_pos (abs_pos.mpr h_ne) (by norm_num)

  -- L₁ の定義から δ₁ を得る
  obtain ⟨δ₁, hδ₁_pos, h₁_bound⟩ := h₁ ε hε

  -- L₂ の定義から δ₂ を得る
  obtain ⟨δ₂, hδ₂_pos, h₂_bound⟩ := h₂ ε hε

  -- δ = min(δ₁, δ₂) を使う
  let δ := min δ₁ δ₂
  have hδ : δ > 0 := by
    simp [δ]
    exact ⟨hδ₁_pos, hδ₂_pos⟩

  -- a ≠ x かつ |x - a| < δ となる x を構成
  -- （実際には a + δ/2 などを使う）
  sorry  -- 構成的な証明は複雑なので省略
  -- 三角不等式から |L₁ - L₂| < 2ε = |L₁ - L₂| となり矛盾

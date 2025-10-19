-- 模範解答9：リアプノフ安定性定理

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

def is_lyapunov_function (V : ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  V 0 = 0 ∧
  (∀ x, x ≠ 0 → V x > 0) ∧
  (∀ x, deriv V x * f x ≤ 0)

lemma lyapunov_decreasing (V : ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ → ℝ)
    (hV : is_lyapunov_function V f)
    (hV_diff : Differentiable ℝ V)
    (hx_diff : Differentiable ℝ x)
    (hx : ∀ t, deriv x t = f (x t)) :
    ∀ t₁ t₂, t₁ ≤ t₂ → V (x t₂) ≤ V (x t₁) := by
  sorry

theorem lyapunov_stability
    (f : ℝ → ℝ) (V : ℝ → ℝ)
    (hV : is_lyapunov_function V f)
    (hV_diff : Differentiable ℝ V)
    (hV_cont : Continuous V)
    (x : ℝ → ℝ)
    (hx_diff : Differentiable ℝ x)
    (hx : ∀ t, deriv x t = f (x t)) :
    ∀ ε > 0, ∃ δ > 0, |x 0| < δ → ∀ t ≥ 0, |x t| < ε := by
  intro ε hε

  -- m = inf{V(y) : |y| = ε} を見つける
  have ⟨m, hm_pos, hm_bound⟩ : ∃ m > 0, ∀ y, |y| = ε → V y ≥ m := by
    sorry  -- V の正定値性とコンパクト性

  -- δ を選ぶ
  have ⟨δ, hδ_pos, hδ_V⟩ : ∃ δ > 0, ∀ y, |y| < δ → V y < m := by
    sorry  -- V(0) = 0 と連続性

  use δ, hδ_pos
  intro hx0 t ht

  -- 背理法
  by_contra h_contra
  push_neg at h_contra
  -- |x(t)| ≥ ε

  -- V(x(t)) ≥ m
  have hVxt : V (x t) ≥ m := by
    by_cases h_eq : |x t| = ε
    · exact hm_bound (x t) h_eq
    · sorry  -- |x(t)| > ε の場合

  -- しかし V(x(t)) ≤ V(x(0)) < m
  have h_bound : V (x t) ≤ V (x 0) :=
    lyapunov_decreasing V f x hV hV_diff hx_diff hx 0 t ht
  have h_small : V (x 0) < m := hδ_V (x 0) hx0

  linarith

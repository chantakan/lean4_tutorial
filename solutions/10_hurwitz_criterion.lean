-- 模範解答10：フルビッツの安定判別法

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Tactic

def hurwitz_matrix (a : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    let idx := 2 * i.val - j.val + 1
    if h : idx < n then a idx else 0

def all_roots_stable (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → z.re < 0

lemma quadratic_formula (a b c : ℝ) (ha : a ≠ 0) (z : ℂ) :
    a * z^2 + b * z + c = 0 ↔
    z = ((-b : ℂ) + Complex.sqrt (b^2 - 4*a*c)) / (2*a) ∨
    z = ((-b : ℂ) - Complex.sqrt (b^2 - 4*a*c)) / (2*a) := by
  sorry

theorem hurwitz_n2 (a₀ a₁ a₂ : ℝ) (ha₂ : a₂ > 0) :
    a₁ > 0 ∧ a₀ > 0 ↔
    all_roots_stable (Polynomial.C a₂ * Polynomial.X^2 +
                      Polynomial.C a₁ * Polynomial.X +
                      Polynomial.C a₀) := by
  constructor

  · -- (⇒) a₁ > 0 ∧ a₀ > 0 なら根の実部が負
    intro ⟨ha₁, ha₀⟩
    intro z hz

    -- 根の公式を適用
    have h_formula := quadratic_formula a₂ a₁ a₀ (by linarith) z
    sorry  -- 判別式で場合分け
    -- D ≥ 0 の場合：実根、z.re = (-a₁ ± √D) / (2a₂) < 0
    -- D < 0 の場合：複素根、z.re = -a₁ / (2a₂) < 0

  · -- (⇐) 根の実部が負なら a₁ > 0 ∧ a₀ > 0
    intro h_stable

    -- ビエタの公式を使う
    -- z₁ + z₂ = -a₁/a₂
    -- z₁ · z₂ = a₀/a₂

    constructor
    · -- a₁ > 0
      -- z₁.re < 0 かつ z₂.re < 0 なら z₁ + z₂ の実部 < 0
      -- よって -a₁/a₂ < 0、つまり a₁ > 0
      sorry

    · -- a₀ > 0
      -- 両方の根が負の実部を持つなら、積の実部 > 0
      -- （複素共役の場合：|z|² > 0）
      -- よって a₀/a₂ > 0、つまり a₀ > 0
      sorry

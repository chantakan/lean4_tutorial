-- 演習10：フルビッツの安定判別法
-- 詳細はREADME.mdを参照

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Tactic

-- フルビッツ行列の定義
def hurwitz_matrix (a : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    let idx := 2 * i.val - j.val + 1
    if h : idx < n then a idx else 0

-- 多項式の根が全て負の実部を持つ
def all_roots_stable (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → z.re < 0

-- 補助補題（完成版）
lemma quadratic_formula (a b c : ℝ) (ha : a ≠ 0) (z : ℂ) :
    a * z^2 + b * z + c = 0 ↔
    z = ((-b : ℂ) + Complex.sqrt (b^2 - 4*a*c)) / (2*a) ∨
    z = ((-b : ℂ) - Complex.sqrt (b^2 - 4*a*c)) / (2*a) := by
  sorry  -- 2次方程式の解の公式

-- TODO：n=2の場合のフルビッツ判別法を証明
-- p(s) = a₂s² + a₁s + a₀ において
-- a₂ > 0, a₁ > 0, a₀ > 0 ⇔ 全ての根の実部が負
theorem hurwitz_n2 (a₀ a₁ a₂ : ℝ) (ha₂ : a₂ > 0) :
    a₁ > 0 ∧ a₀ > 0 ↔
    all_roots_stable (Polynomial.C a₂ * Polynomial.X^2 +
                      Polynomial.C a₁ * Polynomial.X +
                      Polynomial.C a₀) := by
  constructor
  · -- (⇒) a₁ > 0 ∧ a₀ > 0 なら根の実部が負
    intro ⟨ha₁, ha₀⟩
    intro z hz
    -- 根の公式を使う
    -- 判別式で場合分け
    sorry

  · -- (⇐) 根の実部が負なら a₁ > 0 ∧ a₀ > 0
    intro h_stable
    constructor
    · sorry  -- ビエタの公式：根の和 = -a₁/a₂
    · sorry  -- ビエタの公式：根の積 = a₀/a₂

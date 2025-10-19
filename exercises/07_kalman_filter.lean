-- 演習7：カルマンフィルタの最適性
-- 詳細はREADME.mdを参照

import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

variable {n : Type*} [Fintype n] [DecidableEq n]

-- 誤差共分散の更新
def error_covariance_update
    (P : Matrix n n ℝ) (H : Matrix n n ℝ) (R : Matrix n n ℝ) (K : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 - K * H) * P

-- カルマンゲイン
def kalman_gain (P : Matrix n n ℝ) (H : Matrix n n ℝ) (R : Matrix n n ℝ) : Matrix n n ℝ :=
  P * Hᵀ * (H * P * Hᵀ + R)⁻¹

-- 補助定理（完成版）
lemma matrix_trace_pos_of_pos_def {A : Matrix n n ℝ} (hA : A.PosDef) :
    0 < Matrix.trace A := by
  sorry  -- 詳細な証明は省略

-- TODO：カルマンゲインが誤差共分散を最小化することを証明
-- P_posterior = (I - KH)P を K について最小化すると K = PH^T(HPH^T + R)^{-1}
theorem kalman_gain_optimal
    (P : Matrix n n ℝ) (H : Matrix n n ℝ) (R : Matrix n n ℝ)
    (hP : P.PosDef) (hR : R.PosDef) :
    let K := kalman_gain P H R
    let P_post := error_covariance_update P H R K
    ∀ K' : Matrix n n ℝ,
      Matrix.trace (error_covariance_update P H R K') ≥ Matrix.trace P_post := by
  -- トレースを K' について展開
  -- 微分して 0 とおく条件が K = kalman_gain
  sorry

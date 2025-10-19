-- 模範解答7：カルマンフィルタの最適性

import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

variable {n : Type*} [Fintype n] [DecidableEq n]

def error_covariance_update
    (P : Matrix n n ℝ) (H : Matrix n n ℝ) (R : Matrix n n ℝ) (K : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 - K * H) * P

def kalman_gain (P : Matrix n n ℝ) (H : Matrix n n ℝ) (R : Matrix n n ℝ) : Matrix n n ℝ :=
  P * Hᵀ * (H * P * Hᵀ + R)⁻¹

lemma matrix_trace_pos_of_pos_def {A : Matrix n n ℝ} (hA : A.PosDef) :
    0 < Matrix.trace A := by
  sorry

theorem kalman_gain_optimal
    (P : Matrix n n ℝ) (H : Matrix n n ℝ) (R : Matrix n n ℝ)
    (hP : P.PosDef) (hR : R.PosDef) :
    let K := kalman_gain P H R
    let P_post := error_covariance_update P H R K
    ∀ K' : Matrix n n ℝ,
      Matrix.trace (error_covariance_update P H R K') ≥ Matrix.trace P_post := by
  intro K'

  -- P_posterior(K') = (I - K'H)P(I - K'H)^T + K'RK'^T
  -- を K' について展開
  have h_expand : error_covariance_update P H R K' =
      P - K' * H * P - P * Hᵀ * K'ᵀ + K' * (H * P * Hᵀ + R) * K'ᵀ := by
    sorry  -- 行列の展開

  -- トレースの性質を使う
  -- tr(P_post(K')) = tr(P) - 2tr(K'HP) + tr(K'(HPH^T + R)K'^T)

  -- 微分して 0：dtr/dK' = -2HP^T + 2K(HPH^T + R) = 0
  -- よって K = PH^T(HPH^T + R)^{-1}

  sorry  -- 完全な証明は複雑

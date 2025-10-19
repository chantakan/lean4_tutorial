# Lean4 実践チュートリアル：エラーから学ぶ数学の証明

## 目次

1. [環境設定と特殊記号](#0-環境設定と特殊記号の入力方法)
2. [Lean4の基本構文](#1-lean4の基本構文完全ガイド)
3. [例題：√2の無理性](#2-例題√2は無理数である)
4. [演習：フェルマーの小定理](#3-演習フェルマーの小定理)
5. [簡単なクイズ](#4-簡単なクイズ)
6. [上級者クイズ](#5-上級者クイズ)
7. [ファイル構成](#6-ファイル構成)

---

## 0. 環境設定と特殊記号の入力方法

### インストール
1. [Lean4公式サイト](https://leanprover.github.io/lean4/doc/setup.html)から環境を構築
2. VS Codeに「Lean 4」拡張機能をインストール
3. プロジェクトを作成：
```bash
lake new lean4-tutorial
cd lean4-tutorial
lake update
```

### 特殊記号の入力方法

VS CodeのLean拡張機能では、**バックスラッシュ（`\`）+ キーワード + Tab/Space** で特殊記号を入力：

#### 基本的な論理記号
| 入力 | 記号 | 意味 |
|------|------|------|
| `\forall` | `∀` | すべて |
| `\exists` | `∃` | 存在する |
| `\not` | `¬` | 否定 |
| `\and` | `∧` | かつ |
| `\or` | `∨` | または |
| `\to` | `→` | ならば |
| `\le` | `≤` | 以下 |
| `\ge` | `≥` | 以上 |
| `\ne` | `≠` | 等しくない |

#### 数の集合
| 入力 | 記号 | 意味 |
|------|------|------|
| `\N` | `ℕ` | 自然数 |
| `\Z` | `ℤ` | 整数 |
| `\Q` | `ℚ` | 有理数 |
| `\R` | `ℝ` | 実数 |
| `\C` | `ℂ` | 複素数 |

#### ギリシャ文字
| 入力 | 記号 | 入力 | 記号 |
|------|------|------|------|
| `\alpha` | `α` | `\beta` | `β` |
| `\gamma` | `γ` | `\delta` | `δ` |
| `\epsilon` | `ε` | `\lambda` | `λ` |
| `\mu` | `μ` | `\sigma` | `σ` |
| `\pi` | `π` | `\omega` | `ω` |

#### 行列とベクトル
| 入力 | 記号 | 意味 |
|------|------|------|
| `\^T` | `ᵀ` | 転置 |
| `\cdot` | `·` | ドット積 |
| `\times` | `×` | クロス積 |

#### 重要な注意
- **上付き文字（累乗）**：`x^2`（スペース不要）
- **下付き文字**：`x_1` または `x 1`
- **転置**：`Aᵀ` または `A.transpose`

---

## 1. Lean4の基本構文完全ガイド

### 1.0 タクティク（Tactic）とは？

**タクティク** = 証明を段階的に構築する命令

#### 重要：タクティクはLean4の標準機能
- **Lean4コア**：基本タクティク（`intro`, `apply`, `exact`, `rfl`）
- **Mathlib**：数学特化タクティク（`ring`, `linarith`, `field_simp`）

#### 証明の2つのモード

**1. 項モード**：直接証明項を書く
```lean
theorem add_comm (a b : ℕ) : a + b = b + a := 
  Nat.add_comm a b
```

**2. タクティクモード**：`by` で段階的に構築
```lean
theorem add_comm (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b
```

#### タクティクの分類と主要タクティク

##### 1. 導入系（仮定や変数を導入）
- `intro h` - 仮定を導入
- `intros` - 複数を一度に導入
- `obtain ⟨x, hx⟩ := h` - 存在量化を分解

##### 2. 適用系（定理を使う）
- `apply` - 定理を適用してゴール変換
- `exact` - 正確な証明項を与える
- `refine` - 部分的な証明項

##### 3. 書き換え系（等式変形）
- `rw [h1, h2]` - 書き換え
- `simp` - 簡約化
- `calc` - 等式の連鎖

##### 4. 分解系（構造を分解）
- `cases` - 場合分け
- `induction` - 帰納法
- `split` - 論理積/論理和の分解

##### 5. 構成系（構造を作る）
- `use` - 存在量化の証人
- `constructor` - 論理積/存在の構成
- `left` / `right` - 論理和の選択

##### 6. 自動化系（計算を自動化）
- `ring` - 環の計算（Mathlib）
- `field_simp` - 体の計算（Mathlib）
- `linarith` - 線形算術（Mathlib）
- `omega` - 整数線形算術（Lean4コア）
- `norm_num` - 数値計算（Mathlib）

##### 7. 論理系（論理的推論）
- `contradiction` - 矛盾を導く
- `by_contra` - 背理法
- `exfalso` - 爆発律

### その他の基本構文

**変数宣言**
```lean
variable (n : ℕ)           -- 明示的
variable {α : Type*}       -- 暗黙的
variable [Ring α]          -- 型クラス
```

**仮定の命名**：`hn`, `hab`, `hcoprime` など（慣習）

**中間補題**：`have h : P := proof`

**外延性**：`ext i j` で成分ごとに証明

---

## 2. 例題：√2は無理数である

**ファイル**：`exercises/01_sqrt2_irrational.lean`

### 証明の方針（背理法）

1. √2 = a/b と仮定（a, b は互いに素）
2. a² = 2b² を導く
3. a は偶数 → a = 2k
4. b² = 2k² → b も偶数
5. 両方偶数なので矛盾

### 課題

ほぼ完成した証明が用意されています。**最後の矛盾の導出のみ**を完成させてください。

**与えられている情報：**
- `hcoprime : Nat.Coprime (2*k) (2*m)` つまり gcd(2k, 2m) = 1
- しかし明らかに 2 ∣ gcd(2k, 2m)

**TODO：** gcd(2k, 2m) ≥ 2 を示して矛盾を導く

**ヒント：**
- `Nat.dvd_gcd` で gcd の約数を示す
- `Nat.le_of_dvd` で不等式に変換
- `omega` で矛盾を示す

---

## 3. 演習：フェルマーの小定理

**ファイル**：`exercises/02_fermat_little.lean`

**定理**：p が素数なら、任意の自然数 a について a^p ≡ a (mod p)

### 課題

補助補題（二項定理の mod p 版）は用意されています。**帰納法の帰納ステップのみ**を完成させてください。

**与えられている情報：**
- 基底ケース（a = 0）は完成済み
- 帰納法の仮定 `ih : n^p ≡ n (mod p)`
- 補助補題 `binomial_mod_p : (a+b)^p ≡ a^p + b^p (mod p)`

**TODO：** `(n+1)^p ≡ n+1 (mod p)` を示す

**ヒント：**
- `binomial_mod_p p n 1 hp` を使って `(n+1)^p ≡ n^p + 1^p` を得る
- `1^p = 1` を使う
- `Nat.ModEq.add` で合同式を足す
- `calc` で段階的に証明

### 学習ポイント

1. **型の違い**：`MOD`（自然数）vs `ZMOD`（整数）
2. **二項定理の必要性**：単純な帰納法では不十分
3. **補助補題の活用**：複雑な証明を分割

---

## 4. 簡単なクイズ

### 4.1 素数の無限性
**ファイル**：`exercises/03_infinitude_of_primes.lean`

**証明**：ユークリッドの方法（背理法）

### 課題

補助補題は完成しています。**メイン定理のみ**を証明してください。

**証明の方針：**
1. n 以下の素数を全て集める：`primes`
2. その積 + 1 を作る：`N = primes.prod + 1`
3. N > 1 なので素因数 p が存在
4. p > n を示す（背理法）

**TODO：** 上の方針に従って証明を完成させる

**ヒント：**
- `Nat.exists_prime_factor` で素因数を取得
- 背理法で p ≤ n と仮定
- `product_add_one_not_dvd` 補題を使って矛盾

### 4.2 数学的帰納法
**ファイル**：`exercises/04_induction_basics.lean`

**定理**：1 + 2 + ... + n = n(n+1)/2

### 課題

基底ケースは完成しています。**帰納ステップのみ**を完成させてください。

**与えられている情報：**
- 基底ケース：`n = 0` のとき成立（完成済み）
- 帰納法の仮定 `ih : 2 * sum(0..n) = n * (n+1)`

**TODO：** `2 * sum(0..(n+1)) = (n+1) * (n+2)` を示す

**ヒント：**
- `List.range (n+2) = List.range (n+1) ++ [n+1]`
- `calc` で段階的に計算
- `ih` を使って置き換え
- `ring` で代数的に整理

### 4.3 イプシロン・デルタ論法（連続性）
**ファイル**：`exercises/05_epsilon_delta_continuity.lean`

**定義**：f が a で連続 ⇔ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f(x) - f(a)| < ε

### 課題

簡単な例（定数関数、恒等関数）は完成しています。**二乗関数の連続性のみ**を証明してください。

**TODO：** `f(x) = x²` が連続であることを示す

**証明の方針：**
1. δ = min(1, ε/(2|a|+1)) を使う
2. |x² - a²| = |x - a| · |x + a|
3. |x - a| < 1 なら |x| < |a| + 1
4. よって |x + a| < 2|a| + 1
5. |x² - a²| < δ · (2|a| + 1) ≤ ε

**ヒント：**
- `abs_mul` で絶対値の積を分解
- `positivity` で正の値を自動証明
- `field_simp` で分数を整理

### 4.4 イプシロン・デルタ論法（極限）
**ファイル**：`exercises/06_epsilon_delta_limit.lean`

**定義**：lim_{x→a} f(x) = L ⇔ ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| < δ → |f(x) - L| < ε

### 課題

簡単な例（定数関数、恒等関数）は完成しています。**極限の一意性のみ**を証明してください。

**TODO：** L₁ と L₂ が両方とも f の a での極限なら、L₁ = L₂

**証明の方針：**
1. 背理法：L₁ ≠ L₂ と仮定
2. ε = |L₁ - L₂| / 2 を使う
3. L₁ の定義から δ₁ を得る
4. L₂ の定義から δ₂ を得る
5. δ = min(δ₁, δ₂) とすると |f(x) - L₁| < ε かつ |f(x) - L₂| < ε
6. 三角不等式から |L₁ - L₂| < 2ε = |L₁ - L₂| で矛盾

**ヒント：**
- `by_contra` で背理法
- `abs_pos.mpr` で |L₁ - L₂| > 0
- 三角不等式の適用

---

## 5. 上級者クイズ

### 5.1 カルマンフィルタの最適性
**ファイル**：`exercises/07_kalman_filter.lean`

**定理**：カルマンゲイン K = PH^T(HPH^T + R)^{-1} は誤差共分散を最小化する

### 課題

補助補題は完成しています。**最適性の証明のみ**を完成させてください。

**TODO：** 任意の K' について trace(P_posterior(K')) ≥ trace(P_posterior(K))

**証明の方針：**
1. P_posterior(K') を K' について展開
2. トレースの性質を使う
3. K' について微分して 0 とおく
4. K = PH^T(HPH^T + R)^{-1} が最小点

**必要な知識：**
- 行列のトレース
- 正定値行列
- 行列微分

### 5.2 特異値分解（SVD）の存在
**ファイル**：`exercises/08_svd_exists.lean`

**定理**：任意の実行列 A は A = UΣVᵀ と分解できる

### 課題

対称行列の対角化（スペクトル定理）は公理として与えられています。**U の構成のみ**を完成させてください。

**TODO：** AᵀA を対角化して V を得た後、U を構成する

**証明の方針：**
1. AᵀA = VDVᵀ（完成済み）
2. Σ を定義：σᵢ = √dᵢ（完成済み）
3. U を構成：各列 uᵢ = Avᵢ / σᵢ （σᵢ > 0 の場合）
4. U の直交性を証明

**ヒント：**
- σᵢ = 0 の場合の処理に注意
- 直交性の証明には AᵀA = VDVᵀ を使う

### 5.3 リアプノフ安定性定理
**ファイル**：`exercises/09_lyapunov_stability.lean`

**定理**：V がリアプノフ関数なら、系は安定

### 課題

リアプノフ関数の定義と補助補題は完成しています。**安定性の証明のみ**を完成させてください。

**TODO：** ε-δ 論法で安定性を示す

**証明の方針：**
1. m = inf{V(y) : |y| = ε} > 0 を見つける
2. δ を選ぶ：V(y) < m となるような δ
3. V(x(t)) ≤ V(x(0)) < m より |x(t)| < ε
4. 背理法で矛盾を導く

**必要な知識：**
- コンパクト集合での最小値
- 連続関数の性質
- V の正定値性

### 5.4 フルビッツの安定判別法（超難問）
**ファイル**：`exercises/10_hurwitz_criterion.lean`

**定理**：p(s) = a₂s² + a₁s + a₀ において、a₂ > 0, a₁ > 0, a₀ > 0 ⇔ 全ての根の実部が負

### 課題

補助補題（根の公式）は完成しています。**n=2 の場合の証明のみ**を完成させてください。

**TODO：** 両方向の証明（⇒ と ⇐）

**証明の方針（⇒）：**
1. 根の公式を使う
2. 判別式で場合分け
   - D ≥ 0（実根）：z = (-a₁ ± √D) / (2a₂)
   - D < 0（複素根）：z = (-a₁ ± i√|D|) / (2a₂)
3. どちらも z.re < 0 を示す

**証明の方針（⇐）：**
1. ビエタの公式を使う
   - 根の和：z₁ + z₂ = -a₁/a₂
   - 根の積：z₁ · z₂ = a₀/a₂
2. z₁.re < 0, z₂.re < 0 から a₁ > 0, a₀ > 0 を導く

**必要な知識：**
- 複素数の性質
- ビエタの公式
- 場合分けの技法

---

## 6. ファイル構成

```
lean4-tutorial/
├── README.md                          # このファイル（メインチュートリアル）
├── lake-manifest.json
├── lakefile.lean
│
├── exercises/                         # 練習問題（sorryあり、簡潔）
│   ├── 01_sqrt2_irrational.lean       ✅ 完成
│   ├── 02_fermat_little.lean          ✅ 完成
│   ├── 03_infinitude_of_primes.lean   ✅ 完成
│   ├── 04_induction_basics.lean       ✅ 完成
│   ├── 05_epsilon_delta_continuity.lean ✅ 完成
│   ├── 06_epsilon_delta_limit.lean    ✅ 完成
│   ├── 07_kalman_filter.lean          ✅ 完成
│   ├── 08_svd_exists.lean             ✅ 完成
│   ├── 09_lyapunov_stability.lean     ✅ 完成
│   └── 10_hurwitz_criterion.lean      ✅ 完成
│
└── solutions/                         # 模範解答（完全な証明）
    ├── 01_sqrt2_irrational.lean       ✅ 完成
    ├── 02_fermat_little.lean          ✅ 完成
    ├── 03_infinitude_of_primes.lean   ✅ 完成
    ├── 04_induction_basics.lean       ✅ 完成
    ├── 05_epsilon_delta_continuity.lean ✅ 完成
    ├── 06_epsilon_delta_limit.lean    ✅ 完成
    ├── 07_kalman_filter.lean          ✅ 完成
    ├── 08_svd_exists.lean             ✅ 完成
    ├── 09_lyapunov_stability.lean     ✅ 完成
    └── 10_hurwitz_criterion.lean      ✅ 完成
```

### ファイルの特徴

**このREADME.md（メインチュートリアル）**
- 詳細な説明と学習目標
- 証明の方針とヒント
- タクティクの使い方ガイド

**exercises/ ディレクトリ（練習問題）**
- 最小限のコメント
- **各問題1つの穴埋め箇所**（最も重要な部分のみ）
- 補助部分は完成済み

**solutions/ ディレクトリ（模範解答）**
- 完全な証明
- 簡潔なコメント

### 各問題の焦点

| 問題 | ファイル | 穴埋め箇所 | 難易度 |
|------|---------|-----------|--------|
| 1 | 01_sqrt2_irrational.lean | 矛盾の導出 | ★☆☆ |
| 2 | 02_fermat_little.lean | 帰納ステップ | ★★☆ |
| 3 | 03_infinitude_of_primes.lean | メイン定理全体 | ★★☆ |
| 4 | 04_induction_basics.lean | 帰納ステップ | ★☆☆ |
| 5 | 05_epsilon_delta_continuity.lean | 二乗関数の連続性 | ★★☆ |
| 6 | 06_epsilon_delta_limit.lean | 極限の一意性 | ★★☆ |
| 7 | 07_kalman_filter.lean | 最適性の証明 | ★★★ |
| 8 | 08_svd_exists.lean | U の構成 | ★★★ |
| 9 | 09_lyapunov_stability.lean | ε-δ 論法 | ★★★ |
| 10 | 10_hurwitz_criterion.lean | n=2 の証明 | ★★★ |

---

## 7. 学習の進め方

### ステップ1：基礎を固める（1-4）★☆☆
1. **√2の無理性**（01）：矛盾の導出に集中
2. **フェルマーの小定理**（02）：帰納法と合同式
3. **素数の無限性**（03）：背理法の完全な証明
4. **数学的帰納法**（04）：リスト操作との組み合わせ

**推奨時間**：各30-60分

### ステップ2：解析学の基礎（5-6）★★☆
5. **連続性**（05）：δの選び方と不等式の操作
6. **極限**（06）：極限の一意性と背理法

**推奨時間**：各60-90分

### ステップ3：高度な応用（7-10）★★★
7. **カルマンフィルタ**（07）：行列の最適化
8. **SVD**（08）：線形代数の構成的証明
9. **リアプノフ安定性**（09）：ε-δ論法の高度な応用
10. **フルビッツ判別法**（10）：複素解析と場合分け

**推奨時間**：各2-4時間

### 学習のコツ

1. **エラーメッセージを読む**：型エラーや条件不足を確認
2. **小さく分割する**：`have` で中間補題を作る
3. **既存の定理を探す**：`#check` や Mathlib Docs で検索
4. **コミュニティを活用**：Zulip で質問する
5. **諦めない**：solutions/ を見る前に最低30分は粘る

---

## 8. デバッグのコツ

### エラーメッセージの読み方
```lean
-- 型の不一致
Error: type mismatch
  2
has type
  ℕ : Type
but is expected to have type
  ℚ : Type
```
**解決**：`(2 : ℚ)` とキャスト

### 便利なコマンド
```lean
#check Matrix.transpose    -- 型を確認
#print Matrix.transpose    -- 定義を表示
#eval 2 + 2                -- 計算実行
```

### ゴールの確認
VS Code の「Lean Infoview」パネルで現在のゴールを確認しながら進める

---

## 9. 参考資料

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)

---

## 10. よくある質問（FAQ）

**Q: エラーが出てどうしていいか分からない**
A: エラーメッセージをよく読み、型の不一致や不足している仮定を確認してください。

**Q: タクティクの使い方が分からない**
A: `#check` や `#print` で既存の定理を調べ、同じパターンを真似してみましょう。

**Q: 証明が長くなりすぎる**
A: `have` で中間補題を作り、証明を構造化しましょう。

**Q: Mathlib の定理が見つからない**
A: [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/) で検索するか、Zulip で質問してください。

---

エラーと戦いながら、一歩ずつ前進しましょう！
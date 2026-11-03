import Blotto.AdaptiveComputedRegret

/-! Exact finite constant-sum saddle identities for two separately minimizing
loss learners. Pure extrema are selected from finite sets, including after a
complete training history. No minimax or continuous-game transfer is assumed. -/

namespace Blotto
open scoped BigOperators Classical

namespace FiniteSaddle

def RowLoss {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (q : Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ j, matrix i j * q j

def ColumnPayoff {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i, p i * matrix i j

def Bilinear {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ) : ℝ :=
  ∑ i, p i * RowLoss matrix q i

theorem bilinear_columns {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ) :
    Bilinear matrix p q = ∑ j, q j * ColumnPayoff matrix p j := by
  unfold Bilinear RowLoss ColumnPayoff
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rowLoss_unit {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (q : Fin m → ℝ)
    (hMatrix : ∀ i j, 0 ≤ matrix i j ∧ matrix i j ≤ 1)
    (hq : ∀ j, 0 ≤ q j) (hs : ∑ j, q j = 1) (i : Fin n) :
    0 ≤ RowLoss matrix q i ∧ RowLoss matrix q i ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hMatrix i j).1 (hq j))
  · calc
      _ ≤ ∑ j, q j := Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (hq j) (hMatrix i j).2)
      _ = 1 := hs

theorem columnLoss_unit {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ)
    (hMatrix : ∀ i j, 0 ≤ matrix i j ∧ matrix i j ≤ 1)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (j : Fin m) :
    0 ≤ 1 - ColumnPayoff matrix p j ∧ 1 - ColumnPayoff matrix p j ≤ 1 := by
  have hn : 0 ≤ ColumnPayoff matrix p j :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hMatrix i j).1)
  have hu : ColumnPayoff matrix p j ≤ 1 := by
    calc
      _ ≤ ∑ i, p i := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hp i) (hMatrix i j).2)
      _ = 1 := hs
  constructor <;> linarith

noncomputable def minimizingRow {n m : ℕ} (hn : 0 < n) (matrix : Fin n → Fin m → ℝ)
    (q : Fin m → ℝ) : Fin n :=
  Classical.choose (Finset.exists_min_image Finset.univ (RowLoss matrix q) ⟨⟨0, hn⟩, Finset.mem_univ _⟩)

noncomputable def maximizingColumn {n m : ℕ} (hm : 0 < m) (matrix : Fin n → Fin m → ℝ)
    (p : Fin n → ℝ) : Fin m :=
  Classical.choose (Finset.exists_max_image Finset.univ (ColumnPayoff matrix p) ⟨⟨0, hm⟩, Finset.mem_univ _⟩)

theorem minimizingRow_le {n m : ℕ} (hn : 0 < n) (matrix : Fin n → Fin m → ℝ)
    (q : Fin m → ℝ) (i : Fin n) : RowLoss matrix q (minimizingRow hn matrix q) ≤ RowLoss matrix q i :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ (RowLoss matrix q)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ i)

theorem column_le_maximizingColumn {n m : ℕ} (hm : 0 < m) (matrix : Fin n → Fin m → ℝ)
    (p : Fin n → ℝ) (j : Fin m) : ColumnPayoff matrix p j ≤ ColumnPayoff matrix p (maximizingColumn hm matrix p) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (ColumnPayoff matrix p)
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩)).2 j (Finset.mem_univ j)

def RowRegret {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ) (i : Fin n) : ℝ :=
  Bilinear matrix p q - RowLoss matrix q i

def ColumnRegret {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ) (j : Fin m) : ℝ :=
  ColumnPayoff matrix p j - Bilinear matrix p q

def GapAt {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ)
    (i : Fin n) (j : Fin m) : ℝ := ColumnPayoff matrix p j - RowLoss matrix q i

theorem regrets_sum {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ)
    (i : Fin n) (j : Fin m) : RowRegret matrix p q i + ColumnRegret matrix p q j = GapAt matrix p q i j := by
  unfold RowRegret ColumnRegret GapAt
  ring

theorem pure_regrets_nonnegative {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsP : ∑ i, p i = 1) (hq : ∀ j, 0 ≤ q j) (hsQ : ∑ j, q j = 1) :
    0 ≤ RowRegret matrix p q (minimizingRow hn matrix q) ∧
      0 ≤ ColumnRegret matrix p q (maximizingColumn hm matrix p) := by
  constructor
  · unfold RowRegret Bilinear
    have he : RowLoss matrix q (minimizingRow hn matrix q) ≤ ∑ i, p i * RowLoss matrix q i := by
      calc
        _ = ∑ i, p i * RowLoss matrix q (minimizingRow hn matrix q) := by rw [← Finset.sum_mul, hsP, one_mul]
        _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (minimizingRow_le hn matrix q i) (hp i))
    linarith
  · unfold ColumnRegret
    rw [bilinear_columns]
    have he : (∑ j, q j * ColumnPayoff matrix p j) ≤ ColumnPayoff matrix p (maximizingColumn hm matrix p) := by
      calc
        _ ≤ ∑ j, q j * ColumnPayoff matrix p (maximizingColumn hm matrix p) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (column_le_maximizingColumn hm matrix p j) (hq j))
        _ = _ := by rw [← Finset.sum_mul, hsQ, one_mul]
    linarith

theorem both_regrets_le_gap {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (matrix : Fin n → Fin m → ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsP : ∑ i, p i = 1) (hq : ∀ j, 0 ≤ q j) (hsQ : ∑ j, q j = 1) :
    let i := minimizingRow hn matrix q
    let j := maximizingColumn hm matrix p
    0 ≤ GapAt matrix p q i j ∧ RowRegret matrix p q i ≤ GapAt matrix p q i j ∧
      ColumnRegret matrix p q j ≤ GapAt matrix p q i j := by
  dsimp only
  have hnReg := pure_regrets_nonnegative hn hm matrix p q hp hsP hq hsQ
  have he := regrets_sum matrix p q (minimizingRow hn matrix q) (maximizingColumn hm matrix p)
  constructor
  · linarith
  · constructor <;> linarith

noncomputable def averageVector {n : ℕ} (p : ℕ → Fin n → ℝ) (T : ℕ) : Fin n → ℝ :=
  fun i => (∑ t ∈ Finset.range T, p t i) / T

theorem averageVector_nonnegative {n : ℕ} (p : ℕ → Fin n → ℝ) (T : ℕ)
    (hp : ∀ t i, 0 ≤ p t i) : ∀ i, 0 ≤ averageVector p T i := by
  intro i
  exact div_nonneg (Finset.sum_nonneg (fun t _ => hp t i)) (by positivity)

theorem averageVector_sum {n : ℕ} (p : ℕ → Fin n → ℝ) (T : ℕ) (hT : 0 < T)
    (hp : ∀ t, ∑ i, p t i = 1) : (∑ i, averageVector p T i) = 1 := by
  unfold averageVector
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_comm]
  simp_rw [hp]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hT)

def RowCumulative {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : ℕ → Fin n → ℝ)
    (q : ℕ → Fin m → ℝ) (T : ℕ) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ k, (p t k - if k = i then 1 else 0) * RowLoss matrix (q t) k

def ColumnCumulative {n m : ℕ} (matrix : Fin n → Fin m → ℝ) (p : ℕ → Fin n → ℝ)
    (q : ℕ → Fin m → ℝ) (T : ℕ) (j : Fin m) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ k, (q t k - if k = j then 1 else 0) * (1 - ColumnPayoff matrix (p t) k)

theorem cumulative_regrets_sum {n m : ℕ} (matrix : Fin n → Fin m → ℝ)
    (p : ℕ → Fin n → ℝ) (q : ℕ → Fin m → ℝ) (T : ℕ)
    (hq : ∀ t, ∑ j, q t j = 1) (i : Fin n) (j : Fin m) :
    RowCumulative matrix p q T i + ColumnCumulative matrix p q T j =
      ∑ t ∈ Finset.range T, (ColumnPayoff matrix (p t) j - RowLoss matrix (q t) i) := by
  unfold RowCumulative ColumnCumulative
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hcolumn : (∑ k, q t k * (1 - ColumnPayoff matrix (p t) k)) =
      1 - Bilinear matrix (p t) (q t) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hq t]
    rw [bilinear_columns]
  rw [hcolumn]
  change Bilinear matrix (p t) (q t) - RowLoss matrix (q t) i +
    (1 - Bilinear matrix (p t) (q t) - (1 - ColumnPayoff matrix (p t) j)) = _
  ring

theorem average_gap_identity {n m : ℕ} (matrix : Fin n → Fin m → ℝ)
    (p : ℕ → Fin n → ℝ) (q : ℕ → Fin m → ℝ) (T : ℕ)
    (hq : ∀ t, ∑ j, q t j = 1) (i : Fin n) (j : Fin m) :
    (T : ℝ) * GapAt matrix (averageVector p T) (averageVector q T) i j =
      RowCumulative matrix p q T i + ColumnCumulative matrix p q T j := by
  rw [cumulative_regrets_sum matrix p q T hq i j]
  unfold GapAt ColumnPayoff RowLoss averageVector
  simp only [div_eq_mul_inv]
  have hleft : (∑ k, ((∑ t ∈ Finset.range T, p t k) * (T : ℝ)⁻¹) * matrix k j) =
      (∑ t ∈ Finset.range T, ∑ k, p t k * matrix k j) * (T : ℝ)⁻¹ := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hright : (∑ k, matrix i k * ((∑ t ∈ Finset.range T, q t k) * (T : ℝ)⁻¹)) =
      (∑ t ∈ Finset.range T, ∑ k, matrix i k * q t k) * (T : ℝ)⁻¹ := by
    simp only [← mul_assoc]
    simp_rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hleft, hright]
  by_cases hT : T = 0
  · subst T
    simp
  · have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    rw [Finset.sum_sub_distrib]
    field_simp

end FiniteSaddle
end Blotto

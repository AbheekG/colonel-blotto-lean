import Blotto.FareyPredecessor

/-! The actual R127/retained RankUniverse resource decoder: H=4D^2 and
M=8D^2, strict predecessor of (floor(k/2)+1)/H, optional shifted distinguished
bid, and terminal bid one. All codes remain labels, including duplicate decoded
resources. Cut searches below use the already verified binary search; their
complete primitive/bit cost is not asserted here. -/

namespace Blotto.Farey

structure RankUniverse where
  order : ℕ
  order_positive : 0 < order
  shift : ℚ
  shift_nonnegative : 0 ≤ shift
  shift_small : shift < 1 / ((order : ℚ) * order)

def rankCutoff (D k : ℕ) : ℚ := ((k / 2 + 1 : ℕ) : ℚ) / rankScale D

theorem rankCutoff_valid (D : ℕ) (hD : 0 < D) (k : ℕ) (hk : k < rankCap D) :
    0 < rankCutoff D k ∧ rankCutoff D k ≤ 1 := by
  have hH : 0 < rankScale D := by unfold rankScale; positivity
  have hHq : (0 : ℚ) < rankScale D := by exact_mod_cast hH
  have hHalf : k / 2 + 1 ≤ rankScale D := by unfold rankCap at hk; omega
  unfold rankCutoff
  constructor
  · positivity
  · apply (div_le_one hHq).mpr
    exact_mod_cast hHalf

def RankUniverse.base (spec : RankUniverse) (k : ℕ) (hk : k < rankCap spec.order) : Fraction :=
  (predecessor spec.order spec.order_positive (rankCutoff spec.order k)
    (rankCutoff_valid spec.order spec.order_positive k hk)).fraction

def RankUniverse.bump (spec : RankUniverse) (k : ℕ) (base : Fraction) : ℚ :=
  if 0 < spec.shift ∧ closedCode spec.order base + 1 ≤ k ∧ base.value + spec.shift ≤ 1
    then base.value + spec.shift else base.value

def RankUniverse.decode (spec : RankUniverse) (k : ℕ) : ℚ :=
  if hk : k < rankCap spec.order then spec.bump k (spec.base k hk) else 1

theorem base_bounds (spec : RankUniverse) (k : ℕ) (hk : k < rankCap spec.order) :
    (spec.base k hk).den ≤ spec.order ∧
      (spec.base k hk).value < rankCutoff spec.order k :=
  ⟨(predecessor _ _ _ _).bounded, (predecessor _ _ _ _).strict⟩

theorem bump_bounds (spec : RankUniverse) (k : ℕ) (base : Fraction) :
    base.value ≤ spec.bump k base ∧ spec.bump k base ≤ base.value + spec.shift := by
  unfold RankUniverse.bump
  split_ifs <;> constructor <;> linarith [spec.shift_nonnegative]

theorem decode_nonnegative (spec : RankUniverse) (k : ℕ) : 0 ≤ spec.decode k := by
  unfold RankUniverse.decode
  split
  · exact (value_nonnegative _).trans (bump_bounds spec k _).1
  · norm_num

theorem decode_le_one (spec : RankUniverse) (k : ℕ) : spec.decode k ≤ 1 := by
  unfold RankUniverse.decode
  split_ifs with hk
  · unfold RankUniverse.bump
    split_ifs with hBump
    · exact hBump.2.2
    · exact (base_bounds spec k hk).2.le.trans (rankCutoff_valid _ spec.order_positive k hk).2
  · rfl

theorem rankCutoff_mono (D first second : ℕ) (hD : 0 < D) (h : first ≤ second) :
    rankCutoff D first ≤ rankCutoff D second := by
  have hDiv : first / 2 ≤ second / 2 := Nat.div_le_div_right h
  have hCast : ((first / 2 + 1 : ℕ) : ℚ) ≤ ((second / 2 + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.add_le_add_right hDiv 1
  exact div_le_div_of_nonneg_right hCast (by unfold rankScale; positivity)

theorem base_mono (spec : RankUniverse) (first second : ℕ) (h : first ≤ second)
    (hFirst : first < rankCap spec.order) (hSecond : second < rankCap spec.order) :
    (spec.base first hFirst).value ≤ (spec.base second hSecond).value :=
  predecessor_mono _ spec.order_positive _ _ _ _ (rankCutoff_mono _ _ _ spec.order_positive h)

theorem decode_mono (spec : RankUniverse) :
    MonotoneResourceCuts.MonotoneDecode (rankCap spec.order) spec.decode := by
  intro first second hOrder hSecond
  by_cases hs : second < rankCap spec.order
  · have hf : first < rankCap spec.order := hOrder.trans_lt hs
    have hBase := base_mono spec first second hOrder hf hs
    change (if hk : first < rankCap spec.order then spec.bump first (spec.base first hk) else 1) ≤
      (if hk : second < rankCap spec.order then spec.bump second (spec.base second hk) else 1)
    simp only [hf, hs, dite_true]
    unfold RankUniverse.bump
    split_ifs with hFirst hNext hNext
    · rcases lt_or_eq_of_le hBase with hLt | hEq
      · have hGap := bounded_separation spec.order (base_bounds spec first hf).1 (base_bounds spec second hs).1 hLt
        linarith [spec.shift_small]
      · rw [hEq]
    · rcases lt_or_eq_of_le hBase with hLt | hEq
      · have hGap := bounded_separation spec.order (base_bounds spec first hf).1 (base_bounds spec second hs).1 hLt
        linarith [spec.shift_small]
      · have hCodes : closedCode spec.order (spec.base first hf) = closedCode spec.order (spec.base second hs) := by
          unfold closedCode
          rw [hEq]
        have hBump : 0 < spec.shift ∧ closedCode spec.order (spec.base second hs) + 1 ≤ second ∧
            (spec.base second hs).value + spec.shift ≤ 1 :=
          ⟨hFirst.1, by rw [← hCodes]; exact hFirst.2.1.trans hOrder, by rw [← hEq]; exact hFirst.2.2⟩
        exact False.elim (hNext hBump)
    · linarith [spec.shift_nonnegative]
    · exact hBase
  · have hTerminal : second = rankCap spec.order := by omega
    rw [hTerminal]
    unfold RankUniverse.decode
    simp only [lt_self_iff_false, dite_false]
    exact decode_le_one spec first

theorem rankCutoff_zero_small (D : ℕ) (hD : 0 < D) : rankCutoff D 0 ≤ 1 / (D : ℚ) := by
  have hH : D ≤ rankScale D := by unfold rankScale; nlinarith
  have hp : (0 : ℚ) < D := by exact_mod_cast hD
  have hHQ : (D : ℚ) ≤ rankScale D := by exact_mod_cast hH
  simpa [rankCutoff] using one_div_le_one_div_of_le hp hHQ

theorem decode_zero (spec : RankUniverse) : spec.decode 0 = 0 := by
  have hCap : 0 < rankCap spec.order := by unfold rankCap rankScale; have hp := spec.order_positive; positivity
  have hBase : (spec.base 0 hCap).value = 0 :=
    predecessor_zero spec.order spec.order_positive _ _ (rankCutoff_zero_small _ spec.order_positive)
  unfold RankUniverse.decode
  simp only [hCap, dite_true]
  unfold RankUniverse.bump
  have hImpossible : ¬ (0 < spec.shift ∧ closedCode spec.order (spec.base 0 hCap) + 1 ≤ 0 ∧
    (spec.base 0 hCap).value + spec.shift ≤ 1) := by omega
  simp only [hImpossible, ite_false]
  exact hBase

theorem decode_terminal (spec : RankUniverse) : spec.decode (rankCap spec.order) = 1 := by
  simp [RankUniverse.decode]

def RankUniverse.weak (spec : RankUniverse) (threshold : ℚ) : ℕ × ℕ :=
  MonotoneResourceCuts.weak (rankCap spec.order) spec.decode threshold

def RankUniverse.strict (spec : RankUniverse) (threshold : ℚ) : ℕ × ℕ :=
  MonotoneResourceCuts.strict (rankCap spec.order) spec.decode threshold

def RankUniverse.cap (spec : RankUniverse) (budget : ℚ) : ℤ :=
  MonotoneResourceCuts.cap (rankCap spec.order) spec.decode budget

theorem cap_exact (spec : RankUniverse) (budget : ℚ) (code : ℕ) (hCode : code ≤ rankCap spec.order) :
    spec.decode code ≤ budget ↔ (code : ℤ) ≤ spec.cap budget :=
  MonotoneResourceCuts.cap_contract _ _ (decode_mono spec) budget code hCode

theorem cap_nonnegative (spec : RankUniverse) (budget : ℚ) (hBudget : 0 ≤ budget) : 0 ≤ spec.cap budget := by
  have hc := (cap_exact spec budget 0 (by omega)).mp (by simpa only [decode_zero] using hBudget)
  exact hc

theorem rankCap_word_bound (D : ℕ) (hD : 0 < D) :
    binaryWordWidth (rankCap D + 1) ≤ 6 + 2 * binaryWordWidth D := by
  have hM : 1 ≤ rankCap D := by unfold rankCap rankScale; nlinarith
  have hCap : rankCap D + 1 ≤ 2 * rankCap D := by omega
  have h1 := binaryWordWidth_mono hCap
  have h2 := binaryWordWidth_mul 2 (rankCap D)
  have h3 := binaryWordWidth_mul (8 * D) D
  have h4 := binaryWordWidth_mul 8 D
  have he : rankCap D = 8 * D * D := by unfold rankCap rankScale; ring
  have hTwo : binaryWordWidth 2 = 2 := by decide
  have hEight : binaryWordWidth 8 = 4 := by decide
  rw [hTwo] at h2
  rw [hEight] at h4
  rw [← he] at h3
  omega

end Blotto.Farey

import Blotto.GeneralPaperPhysicalResponseModelsContract

/-! Every physical decoder, reserved row prefix and rational budget-check
cursor lies in the actual full response window. Initial and terminal
prefixes are explicit. These embeddings are erased and run no validation. -/
namespace Blotto.GeneralPaperPhysicalRowPhaseCoverage
open GeneralPaperCodeAlphabet GeneralPaperPhysicalResponseStorage GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem row_peak_mono {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (n last : ℕ) (hn : n≤last) (hl : last≤m) :
    rowPeak model W a delta codes n (by omega)≤rowPeak model W a delta codes last hl := by
  induction last generalizing n with
  | zero =>
    have hz : n=0 := by omega
    subst n
    exact le_rfl
  | succ last ih =>
    by_cases he : n=last+1
    · subst n; exact le_rfl
    · exact (ih n (by omega) (by omega)).trans
        ((Nat.le_max_left ..).trans (Nat.le_add_left ..))

theorem row_local_seen {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count+1≤m) :
    rowLocal model W a delta codes count hc≤rowPeak model W a delta codes m le_rfl :=
  ((Nat.le_max_right ..).trans (Nat.le_add_left ..)).trans
    (row_peak_mono model W a delta codes (count+1) m hc le_rfl)

theorem row_peak_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) :
    rowPeak model W a delta codes m le_rfl≤window model W a delta codes B := by
  unfold window
  dsimp only
  exact (Nat.le_max_left ..).trans (((Nat.le_add_left ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..))

theorem row_local_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) (count : ℕ) (hc : count+1≤m) :
    rowLocal model W a delta codes count hc≤window model W a delta codes B :=
  (row_local_seen model W a delta codes count hc).trans (row_peak_covered model W a delta codes B)

theorem decoder_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) (j : Fin m) :
    GeneralPaperPhysicalBidStorage.window model W a delta (codes.read j)≤window model W a delta codes B := by
  have h : GeneralPaperPhysicalBidStorage.window model W a delta (codes.read j)≤
      rowLocal model W a delta codes j.val (by omega) := by
    unfold rowLocal
    exact (Nat.le_add_left ..).trans (Nat.le_add_right ..)
  exact h.trans (row_local_covered model W a delta codes B j.val (by omega))

theorem prefix_seen {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (count : ℕ) (hc : count≤m) :
    rowPrefix model W a delta codes count hc≤rowPeak model W a delta codes m le_rfl := by
  cases count with
  | zero =>
    have h : rowPrefix model W a delta codes 0 hc≤rowPeak model W a delta codes 0 hc := by
      unfold rowPeak
      exact (Nat.le_add_left ..).trans (Nat.le_add_right ..)
    exact h.trans (row_peak_mono model W a delta codes 0 m (Nat.zero_le _) le_rfl)
  | succ count =>
    have h : rowPrefix model W a delta codes (count+1) hc≤rowLocal model W a delta codes count hc := by
      unfold rowLocal
      exact ((Nat.le_add_left ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
    exact h.trans (row_local_seen model W a delta codes count hc)

theorem prefix_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) (count : ℕ) (hc : count≤m) :
    rowPrefix model W a delta codes count hc≤window model W a delta codes B :=
  (prefix_seen model W a delta codes count hc).trans (row_peak_covered model W a delta codes B)

theorem scan_peak_mono {m : ℕ} (model : RationalCostModel) (W : ℕ) (row : FixedArrayTable m ℚ)
    (n last : ℕ) (hn : n≤last) (hl : last≤m) :
    GeneralPaperRowBudgetStorage.peak model W row n (by omega)≤GeneralPaperRowBudgetStorage.peak model W row last hl := by
  induction last generalizing n with
  | zero =>
    have hz : n=0 := by omega
    subst n
    exact le_rfl
  | succ last ih =>
    by_cases he : n=last+1
    · subst n; exact le_rfl
    · exact (ih n (by omega) (by omega)).trans
        ((Nat.le_max_left ..).trans (Nat.le_add_left ..))

theorem scan_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (row : FixedArrayTable m ℚ)
    (B : ℚ) (count : ℕ) (hc : count+1≤m) :
    GeneralPaperRowBudgetStorage.localWindow model W row count hc≤GeneralPaperRowBudgetStorage.window model W row B := by
  have h := ((Nat.le_max_right ..).trans (Nat.le_add_left ..)).trans
    (scan_peak_mono model W row (count+1) m hc le_rfl)
  unfold GeneralPaperRowBudgetStorage.window
  exact h.trans ((Nat.le_max_left ..).trans (Nat.le_add_left ..))

theorem budget_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) :
    GeneralPaperRowBudgetStorage.window model (arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 B≤window model W a delta codes B := by
  unfold window
  dsimp only
  exact (Nat.le_add_left ..).trans ((Nat.le_max_right ..).trans
    (((Nat.le_add_left ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)))

theorem physical_scan_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) (count : ℕ) (hc : count+1≤m) :
    GeneralPaperRowBudgetStorage.localWindow model (arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 count hc≤window model W a delta codes B :=
  (scan_covered model _ _ B count hc).trans (budget_covered model W a delta codes B)

theorem final_check_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) :
    GeneralPaperRowBudgetStorage.finalWindow model (arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 B≤window model W a delta codes B := by
  have h : GeneralPaperRowBudgetStorage.finalWindow model (arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 B≤
      GeneralPaperRowBudgetStorage.window model (arrayWord W m)
        (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 B :=
    (Nat.le_max_right ..).trans (Nat.le_add_left ..)
  exact h.trans (budget_covered model W a delta codes B)

theorem scan_prefix_covered {m : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) (count : ℕ) (hc : count≤m) :
    GeneralPaperRowBudgetStorage.peak model (arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 count hc≤window model W a delta codes B := by
  have h := scan_peak_mono model (arrayWord W m)
    (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 count m hc le_rfl
  have hb : GeneralPaperRowBudgetStorage.peak model (arrayWord W m)
      (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 m le_rfl≤
      GeneralPaperRowBudgetStorage.window model (arrayWord W m)
        (GeneralPaperPhysicalResponseExecution.row true model W a delta codes).1 B :=
    (Nat.le_max_left ..).trans (Nat.le_add_left ..)
  exact h.trans (hb.trans (budget_covered model W a delta codes B))

end Blotto.GeneralPaperPhysicalRowPhaseCoverage

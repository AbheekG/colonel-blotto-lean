import Blotto.RationalPRGResourceBitWidth
import Blotto.RationalPRGPrograms
import Blotto.RationalExpressionBitCost
import Blotto.RationalFractionalScanCost

/-! Prices for the concrete input readers: 2v and b(2v). They include stored
input/result copies and the named multiplication calls. Input address/lookup
implementation, allocation and physical arithmetic realization are separate. -/

namespace Blotto.RationalPRGInput

def capacityReaderBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (j : Fin n) : ℕ :=
  rationalWordWidth (i.values j) + rationalWordWidth (2 : ℚ) +
    model.rat (RationalExpression.pairWidth 2 (i.values j)) + rationalWordWidth (i.lengths j)

def richInitialReaderBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (j : Fin n) : ℕ :=
  i.capacityReaderBitCost model j

def poorInitialReaderBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (j : Fin n) : ℕ :=
  i.capacityReaderBitCost model j + rationalWordWidth i.b + rationalWordWidth (i.lengths j) +
    model.rat (RationalExpression.pairWidth i.b (i.lengths j)) + rationalWordWidth (i.poorInitial j)

theorem valueReader_wordWidth {n : ℕ} (i : RationalPRGInput n) (j : Fin n) :
    rationalWordWidth (i.values j) ≤ 5 + 2 * i.inputWordWidth := by
  have hSum := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun k => rationalWordWidth (i.values k)) (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold inputWordWidth
  omega

theorem budgetReader_wordWidth {n : ℕ} (i : RationalPRGInput n) : rationalWordWidth i.b ≤ 5 + 2 * i.inputWordWidth := by
  unfold inputWordWidth
  omega

theorem capacityReader_wordWidth {n : ℕ} (i : RationalPRGInput n) (j : Fin n) :
    rationalWordWidth (i.lengths j) ≤ 5 + 2 * i.inputWordWidth := by
  have h := rationalFractionalWordBound_lattice i.latticeDenominator_pos (i.lengths_on_lattice j)
    ⟨(i.lengths_pos j).le, (i.small_fields j).trans i.b_le⟩
  have hd := i.latticeDenominator_wordWidth
  omega

theorem poorInitialReader_wordWidth {n : ℕ} (i : RationalPRGInput n) (j : Fin n) :
    rationalWordWidth (i.poorInitial j) ≤ 5 + 2 * i.inputWordWidth := by
  have hBox := i.poorNativeSystem.initial_box j
  have h := rationalFractionalWordBound_lattice i.latticeDenominator_pos (i.poorInitial_on_lattice j)
    ⟨hBox.1, hBox.2.trans ((i.small_fields j).trans i.b_le)⟩
  have hd := i.latticeDenominator_wordWidth
  omega

theorem capacityReaderBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (j : Fin n) :
    i.capacityReaderBitCost model j ≤ 4 * model.rat (5 + 2 * i.inputWordWidth) := by
  have hv := i.valueReader_wordWidth j
  have hc := i.capacityReader_wordWidth j
  have hTwo : rationalWordWidth (2 : ℚ) ≤ 5 + 2 * i.inputWordWidth := by
    have he : rationalWordWidth (2 : ℚ) = 4 := by decide
    omega
  have hV := hv.trans (model.word_le _)
  have hC := hc.trans (model.word_le _)
  have hT := hTwo.trans (model.word_le _)
  have hCall := model.monotone (show RationalExpression.pairWidth 2 (i.values j) ≤ 5 + 2 * i.inputWordWidth from max_le hTwo hv)
  unfold capacityReaderBitCost
  omega

theorem richInitialReaderBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (j : Fin n) :
    i.richInitialReaderBitCost model j ≤ 4 * model.rat (5 + 2 * i.inputWordWidth) := i.capacityReaderBitCost_bound model j

theorem poorInitialReaderBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (j : Fin n) :
    i.poorInitialReaderBitCost model j ≤ 8 * model.rat (5 + 2 * i.inputWordWidth) := by
  have hCap := i.capacityReaderBitCost_bound model j
  have hb := i.budgetReader_wordWidth
  have hc := i.capacityReader_wordWidth j
  have hr := i.poorInitialReader_wordWidth j
  have hB := hb.trans (model.word_le _)
  have hC := hc.trans (model.word_le _)
  have hR := hr.trans (model.word_le _)
  have hCall := model.monotone (show RationalExpression.pairWidth i.b (i.lengths j) ≤ 5 + 2 * i.inputWordWidth from max_le hb hc)
  unfold poorInitialReaderBitCost
  omega

end Blotto.RationalPRGInput

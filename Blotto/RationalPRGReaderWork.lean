import Blotto.RationalPRGSourceReaderPrice

/-! Concrete input derivations accumulate only over source callbacks and
initialization. Continuation readers are distinct obligations. These prices
cover rational derivation/copies, with input addressing and backend separate. -/

namespace Blotto.RationalPRGInput

def richSourceReaderWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.richNativeSystem.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge
      (fun cursor : i.richNativeSystem.PhaseCursor => i.sourceReaderCharge model cursor.1))
    R (i.richNativeSystem.samplingStart K outerBits scalarBits) choiceBits

def poorSourceReaderWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.poorNativeSystem.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge
      (fun cursor : i.poorNativeSystem.PhaseCursor => i.sourceReaderCharge model cursor.1))
    R (i.poorNativeSystem.samplingStart K outerBits scalarBits) choiceBits

theorem richSourceReaderWork_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.richSourceReaderWork model K R outerBits scalarBits choiceBits = 0 := by
  have h := i.richNativeSystem.phase.runCachedSerialSourceWork_initial_bound
    (fun value => ((i.richNativeSystem.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.richNativeSystem.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.richNativeSystem.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.richNativeSystem.PhaseCursor => i.sourceReaderCharge model cursor.1)
    (16 * model.rat (5 + 2 * i.inputWordWidth)) (fun cursor => i.sourceReaderCharge_bound model cursor.1)
    R i.richNativeSystem.start choiceBits
  have hRank : i.richNativeSystem.phase.rank i.richNativeSystem.start = 0 := i.richResource_rank_zero
  have hInitial : i.sourceReaderCharge model i.richNativeSystem.start.1 = 0 := by
    change i.pairCapacityReaderBitCost model i.richState + 0 = 0
    rw [i.pairCapacityReaderBitCost_terminal model i.richState (by rw [i.richState_active_empty]; simp)]
  rw [hRank, hInitial, Nat.mul_zero, Nat.add_zero] at h
  exact Nat.le_zero.mp h

theorem poorSourceReaderWork_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.poorSourceReaderWork model K R outerBits scalarBits choiceBits ≤ 16 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  have h := i.poorNativeSystem.phase.runCachedSerialSourceWork_bound
    (fun value => ((i.poorNativeSystem.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.poorNativeSystem.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.poorNativeSystem.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.poorNativeSystem.PhaseCursor => i.sourceReaderCharge model cursor.1)
    (16 * model.rat (5 + 2 * i.inputWordWidth)) (fun cursor => i.sourceReaderCharge_bound model cursor.1)
    R i.poorNativeSystem.start choiceBits
  have hRank : i.poorNativeSystem.phase.rank i.poorNativeSystem.start + 1 ≤ n := by
    have hp := i.poorNativeSystem.phase_rank
    have hn := i.poorNativeSystem.fields_pos
    omega
  have hBudget := Nat.mul_le_mul_left (16 * model.rat (5 + 2 * i.inputWordWidth)) hRank
  have hPrice : (16 * model.rat (5 + 2 * i.inputWordWidth)) * n = 16 * n * model.rat (5 + 2 * i.inputWordWidth) := by ring
  exact h.trans (hBudget.trans_eq hPrice)

def richPaperSourceReaderWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  i.richSourceReaderWork model K (RationalLottoResourceSystem.coinBitBudget n K)
    (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)

def poorPaperSourceReaderWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  i.poorSourceReaderWork model K (RationalLottoResourceSystem.coinBitBudget n K)
    (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)

theorem richPaperSourceReaderWork_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : i.richPaperSourceReaderWork model K bits = 0 :=
  i.richSourceReaderWork_eq_zero model K _ _ _ _

theorem poorPaperSourceReaderWork_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorPaperSourceReaderWork model K bits ≤ 16 * n * model.rat (5 + 2 * i.inputWordWidth) :=
  i.poorSourceReaderWork_bound model K _ _ _ _

def richReaderTotal {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richInitialReaderTotal model + i.richPaperSourceReaderWork model K bits

def poorReaderTotal {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorInitialReaderTotal model + i.poorPaperSourceReaderWork model K bits

theorem richReaderTotal_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richReaderTotal model K bits ≤ 8 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  rw [richReaderTotal, i.richPaperSourceReaderWork_eq_zero, Nat.add_zero]
  exact i.richInitialReaderTotal_bound model

theorem poorReaderTotal_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorReaderTotal model K bits ≤ 28 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  have hInitial := i.poorInitialReaderTotal_bound model
  have hSource := i.poorPaperSourceReaderWork_bound model K bits
  unfold poorReaderTotal
  nlinarith

end Blotto.RationalPRGInput

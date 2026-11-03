import Blotto.GeneralPaperPhysicalResponseStorage

/-! The bit-model shift constructor owns one repeated-squaring stack,
its literal integer intermediates, three rational temporaries and one
active primitive scratch reservation. The returned shift remains resident
across the source; no primitive scratch accumulates across its rounds. -/
namespace Blotto.GeneralPaperPhysicalShiftStorage
open GeneralPaperPhysicalShiftExecution GeneralPaperEncodedScalarStorage
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def powerPayload (m C : ℕ) : ℕ :=
  128*(2+binaryWordWidth C+binaryWordWidth (m+2)+(m+2)*binaryWordWidth C)

theorem power_payload (m C : ℕ) : GeneralPaperNatPowerConstructionStorage.payload C (m+2)≤powerPayload m C := by
  have h := GeneralPaperNatPowerOperands.power_width C (m+2)
  unfold GeneralPaperNatPowerConstructionStorage.payload powerPayload
  omega

def window (model : RationalCostModel) (W m qbar C : ℕ) : ℕ :=
  let A := arrayWord W (m+3)
  GeneralPaperNatPowerConstructionStorage.peak A C (m+2)+
    fields A [4,m,qbar,m+2,C^(m+2),4*m,4*m*qbar,GeneralPaperTagBudgetTransfer.shiftDenominator m qbar C]+
    rationalWordWidth (GeneralPaperTagBudgetTransfer.shiftDenominator m qbar C:ℚ)+rationalWordWidth (1:ℚ)+
    rationalWordWidth (run true model W m qbar C).1+16*model.rat (width m qbar C)+512*A

def profile (model : RationalCostModel) (W m qbar C : ℕ) : ℕ :=
  let A := arrayWord W (m+3)
  (binaryWordWidth (m+2)+1)*(12*powerPayload m C+384*A)+
    8*(natWidth m qbar C+A)+32*A+19*model.rat (width m qbar C)+512*A

theorem bounded (model : RationalCostModel) (W m qbar C : ℕ) (hC : 0<C) :
    window model W m qbar C≤profile model W m qbar C := by
  let A := arrayWord W (m+3)
  have hPower := (GeneralPaperNatPowerConstructionStorage.depth_bound A C (m+2) (m+2) hC le_rfl).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 12 (power_payload m C)) _))
  have hNat := fields_bound A (natWidth m qbar C)
    [4,m,qbar,m+2,C^(m+2),4*m,4*m*qbar,GeneralPaperTagBudgetTransfer.shiftDenominator m qbar C]
    (native_words m qbar C)
  simp only [List.length_cons,List.length_nil] at hNat
  obtain ⟨hD,hS,hOne⟩ := rational_words m qbar C
  have hD' := hD.trans (model.word_le _)
  have hS' := hS.trans (model.word_le _)
  have hOne' := hOne.trans (model.word_le _)
  unfold window profile
  dsimp only
  rw [GeneralPaperPhysicalShiftExecution.data]
  dsimp only [A] at hPower hNat
  nlinarith only [hPower,hNat,hD',hS',hOne']

theorem resident (bits : Bool) (model : RationalCostModel) (W m qbar C : ℕ) :
    rationalWordWidth (run bits model W m qbar C).1≤1+2*GeneralPaperResponsePhysicalHeights.shiftHeight m qbar C :=
  rationalWordWidth_of_height (GeneralPaperPhysicalShiftExecution.height bits model W m qbar C)

end Blotto.GeneralPaperPhysicalShiftStorage

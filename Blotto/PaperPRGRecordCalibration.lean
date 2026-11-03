import Blotto.PaperPRGDataSampler

/-! Fixed source-record calibration in the declared word profile. A word
action pays a padded load/store, one primitive operation and one control
action. Eight such actions per array slot allow both old/new reference
traffic and index/capacity control, even for a full-prefix reference copy.
Numeric rational work remains in the arithmetic ledger. State payloads and
whole-row emission have their separate constructor/metadata prices.
-/

namespace Blotto.PaperPRGRecordCalibration
set_option autoImplicit false

def wordAction (primitive : ℕ → ℕ) (W : ℕ) : ℕ := W+primitive W+1

def codeUnits : ℕ → List RealArithmeticInstruction → ℕ
  | _,[] => 1
  | size,_::rest => 8*(size+1)+codeUnits (size+1) rest

def run (primitive : ℕ → ℕ) (W : ℕ) : List RealArithmeticInstruction → Array ℚ → Array ℚ × ℕ
  | [],registers => (registers,wordAction primitive W)
  | instruction::rest,registers =>
      let later := run primitive W rest (instruction.executeRat registers)
      (later.1,8*(registers.size+1)*wordAction primitive W+later.2)

theorem run_data (primitive : ℕ → ℕ) (W : ℕ) (code : List RealArithmeticInstruction) (registers : Array ℚ) :
    (run primitive W code registers).1=RationalArithmeticProgram.run code registers := by
  induction code generalizing registers with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.executeRat registers)

theorem run_price (primitive : ℕ → ℕ) (W : ℕ) (code : List RealArithmeticInstruction) (registers : Array ℚ) :
    (run primitive W code registers).2=codeUnits registers.size code*wordAction primitive W := by
  induction code generalizing registers with
  | nil => simp only [run,codeUnits,Nat.one_mul]
  | cons instruction rest ih =>
      simp only [run,ih,RealArithmeticInstruction.executeRat_size,codeUnits]
      ring

/- Runtime fields only: pair view, rebuilt active-list head, active-state
record, endpoint/index loads, ResourceChoice, ProbabilityWords, prepared
choice and ask wrapper. Each record includes two header/control slots and
permits both reading and writing every listed field. -/
def requestLayouts : List ℕ := [4,4,2,6,6,2,2,2]
def cursorLayouts : List ℕ := [3,6,4,4]
def selectedLayouts : List ℕ := [3,4,4,2]

def layoutUnits (fields : List ℕ) : ℕ := 2*(fields.sum+2*fields.length)

def requestUnits : ℕ := 8*(5+1)+codeUnits 5 RealPairProgram.code+layoutUnits requestLayouts+layoutUnits cursorLayouts
def selectedUnits : ℕ := layoutUnits selectedLayouts+layoutUnits cursorLayouts
def returnUnits : ℕ := layoutUnits [2,2,2]+layoutUnits cursorLayouts

theorem fixed_units : codeUnits 5 RealPairProgram.code=505 ∧ requestUnits=691 ∧
    selectedUnits=92 ∧ returnUnits=74 := by decide

theorem all_branches_fit : requestUnits ≤ 1024 ∧ selectedUnits ≤ 1024 ∧ returnUnits ≤ 1024 := by decide

theorem request_profile_covers (primitive : ℕ → ℕ) (W : ℕ) (p : RationalRoundingPair) :
    8*((RationalPairProgram.inputs p).size+1)*wordAction primitive W+
      (run primitive W RealPairProgram.code (RationalPairProgram.inputs p)).2+
      (layoutUnits requestLayouts+layoutUnits cursorLayouts)*wordAction primitive W ≤
        PaperSharedControllerRecords.unitWork primitive W := by
  rw [run_price]
  have hInputs : (RationalPairProgram.inputs p).size=5 := rfl
  rw [hInputs]
  have h := Nat.mul_le_mul_right (wordAction primitive W) all_branches_fit.1
  unfold requestUnits PaperSharedControllerRecords.unitWork wordAction at *
  nlinarith only [h]

theorem selected_profile_covers (primitive : ℕ → ℕ) (W : ℕ) :
    selectedUnits*wordAction primitive W ≤ PaperSharedControllerRecords.unitWork primitive W := by
  simpa only [PaperSharedControllerRecords.unitWork,wordAction] using
    Nat.mul_le_mul_right (wordAction primitive W) all_branches_fit.2.1

theorem return_profile_covers (primitive : ℕ → ℕ) (W : ℕ) :
    returnUnits*wordAction primitive W ≤ PaperSharedControllerRecords.unitWork primitive W := by
  simpa only [PaperSharedControllerRecords.unitWork,wordAction] using
    Nat.mul_le_mul_right (wordAction primitive W) all_branches_fit.2.2

end Blotto.PaperPRGRecordCalibration

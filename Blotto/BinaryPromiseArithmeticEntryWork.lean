import Blotto.BinaryArithmeticEntryWork
import Blotto.BinaryPromiseCheckPlan

/-! Proof-only raw entry charges follow actual delayed guards and returned
sum/scaling values. Rejected guards contribute no later charge. Every concrete
checker discharges its own callback bounds; no backend premise is added. -/
namespace Blotto.BinaryPromiseArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryPromiseControlPlan (Record)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def Pays {α : Type*} (run : ℕ → Record α) (cost : ℕ → ℕ) : Prop :=
  ∀ depth,cost depth ≤ 2*listCells (denote (run depth).1.1.2)

def andThen (first : ℕ → Record Bool) (later : Unit → ℕ → Record Bool)
    (frontCost : ℕ → ℕ) (laterCost : Unit → ℕ → ℕ) (depth : ℕ) : ℕ :=
  frontCost (depth+2)+(if (first (depth+2)).1.1.1 then laterCost () (depth+2) else 0)

theorem andThen_bound (first : ℕ → Record Bool) (later : Unit → ℕ → Record Bool)
    (frontCost : ℕ → ℕ) (laterCost : Unit → ℕ → ℕ)
    (hFirst : Pays first frontCost) (hLater : ∀ u,Pays (later u) (laterCost u)) :
    Pays (BinaryPromiseControlPlan.andThenAt first later) (andThen first later frontCost laterCost) := by
  intro depth
  have hf := hFirst (depth+2)
  have hl := hLater () (depth+2)
  simp only [andThen,BinaryPromiseControlPlan.andThenAt]
  split <;> simp only [denote,listCells_append,listCells] <;> omega

theorem andThen_reject (first : ℕ → Record Bool) (later : Unit → ℕ → Record Bool)
    (frontCost : ℕ → ℕ) (laterCost : Unit → ℕ → ℕ) (depth : ℕ)
    (h : (first (depth+2)).1.1.1=false) :
    andThen first later frontCost laterCost depth = frontCost (depth+2) := by
  simp only [andThen,h,Bool.false_eq_true,ite_false,Nat.add_zero]

def opcode (op : RealArithmeticOp) (a b : SignedWord) (_depth : ℕ) : ℕ := BinaryArithmeticEntryWork.raw op a b

theorem opcode_bound (op : RealArithmeticOp) (a b : SignedWord) : Pays (BinaryPromiseControlPlan.opcodeAt op a b) (opcode op a b) := by
  intro depth
  exact BinaryArithmeticEntryWork.normalized_plan op a b depth

def comparison (a b : SignedWord) (_depth : ℕ) : ℕ := BinaryArithmeticEntryWork.comparison a b

theorem comparison_bound (a b : SignedWord) : Pays (BinaryPromiseControlPlan.comparisonAt a b) (comparison a b) := by
  intro depth
  have h := BinaryArithmeticEntryWork.comparison_bound a b
  simpa only [comparison,BinaryPromiseControlPlan.comparisonAt,BinaryQuadraticExpressionMeasured.compare,
    denote,listCells_under,listCells,Nat.add_zero] using h

def positive (word : SignedWord) (_depth : ℕ) : ℕ := BinaryArithmeticEntryWork.comparison word zero

theorem positive_bound (word : SignedWord) : Pays (BinaryPromiseControlPlan.positiveAt word) (positive word) := by
  intro depth
  have h := comparison_bound word zero (depth+2)
  simp only [positive,BinaryPromiseControlPlan.positiveAt,denote,listCells_append,listCells]
  simpa only [comparison,Nat.zero_add] using h

def equal (a b : SignedWord) : ℕ → ℕ :=
  andThen (BinaryPromiseControlPlan.comparisonAt a b) (fun _ => BinaryPromiseControlPlan.comparisonAt b a) (comparison a b) (fun _ => comparison b a)

theorem equal_bound (a b : SignedWord) : Pays (BinaryPromiseControlPlan.equalAt a b) (equal a b) :=
  andThen_bound _ _ _ _ (comparison_bound a b) (fun _ => comparison_bound b a)

def all (produce : SignedWord → ℕ → Record Bool) (cost : SignedWord → ℕ → ℕ) : List SignedWord → ℕ → ℕ
  | [],_depth => 0
  | word::rest,depth => andThen (produce word) (fun _ => BinaryPromiseControlPlan.allAt produce rest)
      (cost word) (fun _ => all produce cost rest) depth

theorem all_bound (produce : SignedWord → ℕ → Record Bool) (cost : SignedWord → ℕ → ℕ)
    (h : ∀ word,Pays (produce word) (cost word)) (words : List SignedWord) :
    Pays (BinaryPromiseControlPlan.allAt produce words) (all produce cost words) := by
  induction words with
  | nil => intro depth; simp [all,BinaryPromiseControlPlan.allAt,denote,listCells]
  | cons word rest ih => exact andThen_bound _ _ _ _ (h word) (fun _ => ih)

def sum : List SignedWord → ℕ → ℕ
  | [],_depth => 0
  | word::rest,depth => sum rest (depth+2)+opcode .add word (BinaryPromiseControlPlan.sumAt rest (depth+2)).1.1.1 (depth+2)

theorem sum_bound (words : List SignedWord) : Pays (BinaryPromiseControlPlan.sumAt words) (sum words) := by
  induction words with
  | nil => intro depth; simp [sum,BinaryPromiseControlPlan.sumAt,denote,listCells]
  | cons word rest ih =>
      intro depth
      have ht := ih (depth+2)
      have hh := opcode_bound .add word (BinaryPromiseControlPlan.sumAt rest (depth+2)).1.1.1 (depth+2)
      simp only [sum,BinaryPromiseControlPlan.sumAt,denote,listCells_append,listCells]
      omega

def scaled (twice b word : SignedWord) (depth : ℕ) : ℕ :=
  opcode .mul twice word (depth+2)+comparison (BinaryPromiseControlPlan.opcodeAt .mul twice word (depth+2)).1.1.1 b (depth+2)

theorem scaled_bound (twice b word : SignedWord) : Pays (BinaryPromiseControlPlan.scaledAt twice b word) (scaled twice b word) := by
  intro depth
  have hs := opcode_bound .mul twice word (depth+2)
  have hc := comparison_bound (BinaryPromiseControlPlan.opcodeAt .mul twice word (depth+2)).1.1.1 b (depth+2)
  simp only [scaled,BinaryPromiseControlPlan.scaledAt,denote,listCells_append,listCells]
  omega

def fields {n : ℕ} (input : Input n) (row : List SignedWord) (depth : ℕ) : ℕ :=
  let twice := BinaryPromiseControlPlan.opcodeAt .mul two input.a (depth+2)
  opcode .mul two input.a (depth+2)+all (BinaryPromiseControlPlan.scaledAt twice.1.1.1 input.b) (scaled twice.1.1.1 input.b) row (depth+2)

theorem fields_bound {n : ℕ} (input : Input n) (row : List SignedWord) : Pays (BinaryPromiseCheckPlan.fieldsAt input row) (fields input row) := by
  intro depth
  have ht := opcode_bound .mul two input.a (depth+2)
  have ha := all_bound (BinaryPromiseControlPlan.scaledAt (BinaryPromiseControlPlan.opcodeAt .mul two input.a (depth+2)).1.1.1 input.b)
    (scaled (BinaryPromiseControlPlan.opcodeAt .mul two input.a (depth+2)).1.1.1 input.b)
    (fun word => scaled_bound _ _ word) row (depth+2)
  simp only [fields,BinaryPromiseCheckPlan.fieldsAt,denote,listCells_append,listCells]
  omega

def remaining {n : ℕ} (input : Input n) (row : List SignedWord) (depth : ℕ) : ℕ :=
  let total := (BinaryPromiseControlPlan.sumAt row (depth+2)).1.1.1
  sum row (depth+2)+(andThen (BinaryPromiseControlPlan.equalAt total one) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.positiveAt input.a) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row)))) (equal total one) (fun _ => andThen (BinaryPromiseControlPlan.positiveAt input.a) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row))) (positive input.a) (fun _ => andThen (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row)) (positive input.b) (fun _ => andThen (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row) (comparison input.b input.a) (fun _ => fields input row))))) (depth+2)

theorem remaining_bound {n : ℕ} (input : Input n) (row : List SignedWord) :
    Pays (BinaryPromiseCheckPlan.remainingAt input row) (remaining input row) := by
  intro depth
  let total := (BinaryPromiseControlPlan.sumAt row (depth+2)).1.1.1
  have h3 := andThen_bound (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row) (comparison input.b input.a) (fun _ => fields input row)
    (comparison_bound input.b input.a) (fun _ => fields_bound input row)
  have h2 := andThen_bound (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row)) (positive input.b) (fun _ => andThen (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row) (comparison input.b input.a) (fun _ => fields input row))
    (positive_bound input.b) (fun _ => h3)
  have h1 := andThen_bound (BinaryPromiseControlPlan.positiveAt input.a) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row))) (positive input.a) (fun _ => andThen (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row)) (positive input.b) (fun _ => andThen (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row) (comparison input.b input.a) (fun _ => fields input row)))
    (positive_bound input.a) (fun _ => h2)
  have h0 := andThen_bound (BinaryPromiseControlPlan.equalAt total one) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.positiveAt input.a) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row)))) (equal total one) (fun _ => andThen (BinaryPromiseControlPlan.positiveAt input.a) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row))) (positive input.a) (fun _ => andThen (BinaryPromiseControlPlan.positiveAt input.b) (fun _ => BinaryPromiseControlPlan.andThenAt (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row)) (positive input.b) (fun _ => andThen (BinaryPromiseControlPlan.comparisonAt input.b input.a) (fun _ => BinaryPromiseCheckPlan.fieldsAt input row) (comparison input.b input.a) (fun _ => fields input row))))
    (equal_bound total one) (fun _ => h1)
  have hs := sum_bound row (depth+2)
  have hl := h0 (depth+2)
  dsimp only [total] at hl
  simp only [remaining,BinaryPromiseCheckPlan.remainingAt,denote,listCells_append,listCells]
  omega

def checkRows {n : ℕ} (input : Input n) (rows : List SignedWord) (depth : ℕ) : ℕ :=
  andThen (BinaryPromiseControlPlan.allAt BinaryPromiseControlPlan.positiveAt rows) (fun _ => BinaryPromiseCheckPlan.remainingAt input rows)
    (all BinaryPromiseControlPlan.positiveAt positive rows) (fun _ => remaining input rows) (depth+2)

theorem checkRows_bound {n : ℕ} (input : Input n) (rows : List SignedWord) :
    Pays (BinaryPromiseCheckPlan.checkRowsAt input rows) (checkRows input rows) := by
  intro depth
  have h := andThen_bound (BinaryPromiseControlPlan.allAt BinaryPromiseControlPlan.positiveAt rows) (fun _ => BinaryPromiseCheckPlan.remainingAt input rows)
    (all BinaryPromiseControlPlan.positiveAt positive rows) (fun _ => remaining input rows)
    (all_bound _ _ positive_bound rows) (fun _ => remaining_bound input rows) (depth+2)
  simp only [checkRows,BinaryPromiseCheckPlan.checkRowsAt,denote,listCells_append,listCells]
  omega

theorem emitted_bound {n : ℕ} (input : Input n) (rows : List SignedWord) :
    checkRows input rows 0 ≤ 2*listCells (BinaryPromiseCheckPlan.checkRows input rows).1.1.2 := by
  have h := checkRows_bound input rows 0
  simpa only [BinaryPromiseCheckPlan.checkRows,BinaryNumericalReadbackPlan.finish_record,BinaryNumericalReadbackPlan.view] using h

end Blotto.BinaryPromiseArithmeticEntryWork

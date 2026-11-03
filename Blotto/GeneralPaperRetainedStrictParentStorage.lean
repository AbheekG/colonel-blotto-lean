import Blotto.GeneralPaperSourceEnclosingOwnerReachedRates
import Blotto.GeneralPaperScoreEntryStorageRates

/-! Literal strict-preparation parent. The field-list container borrows
the full original matrix counted by the enclosing resident owner. Original
own/opposing/budget scalars, the single division scratch and every native
child/primitive/partial/return field coexist. Full traversal work sizes only
encoded counters; matrix/DP/scan/maximum child scratch remains separate. -/
namespace Blotto.GeneralPaperRetainedStrictParentStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def metadataCap (W m K S depth F : ℕ) : ℕ := m+K+S+depth+F+64*(m+2)*arrayWord W (m+K+S)+1
def controls {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : List ℕ :=
  let matrix := GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S
  let table := GeneralPaperRetainedTransferPreparation.dp true model W S matrix.1.data.toList
  let selected := GeneralPaperRetainedTransferPreparation.threshold true model W table.1 (opposing/own)
  let maximum := GeneralPaperStoredScoreMaximum.run true model W hK matrix.1
  let a := model.rat (RationalExpression.pairWidth opposing own)
  let b := model.rat (rationalWordWidth (opposing/own))
  let result := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  let A := arrayWord W (m+K+S)
  [m,K,S,depth,matrix.2,table.2,selected.2,maximum.2,a,b,a+b,result.2,64*(m+1)*A,64*A,
    matrix.2+table.2,matrix.2+table.2+selected.2,matrix.2+table.2+selected.2+maximum.2,
    matrix.2+table.2+selected.2+maximum.2+a]
def window {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : ℕ :=
  let matrix := GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S
  listFootprint W (fun _ => 0) matrix.1.data.toList+
    rationalWordWidth own+rationalWordWidth opposing+rationalWordWidth (opposing/own)+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) opposing own+
    fields W (controls model W depth S hK columns values own opposing)+192*W
def profile (model : RationalCostModel) (W m K S depth R F : ℕ) : ℕ :=
  2*m*W+3*R+2*model.rat R+18*(natBits (metadataCap W m K S depth F)+W)+256*W

theorem controls_length {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) :
    (controls model W depth S hK columns values own opposing).length=18 := rfl

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth S R F : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (hOwn : rationalWordWidth own≤R) (hOpposing : rationalWordWidth opposing≤R) (hBudget : rationalWordWidth (opposing/own)≤R)
    (hTotal : (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).2≤F) :
    window model W depth S hK columns values own opposing≤profile model W m K S depth R F := by
  let matrix := GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S
  let table := GeneralPaperRetainedTransferPreparation.dp true model W S matrix.1.data.toList
  let selected := GeneralPaperRetainedTransferPreparation.threshold true model W table.1 (opposing/own)
  let maximum := GeneralPaperStoredScoreMaximum.run true model W hK matrix.1
  let a := model.rat (RationalExpression.pairWidth opposing own)
  let b := model.rat (rationalWordWidth (opposing/own))
  let result := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  let A := arrayWord W (m+K+S)
  have hNative : matrix.2+table.2+selected.2+maximum.2+(a+b)+64*(m+1)*A+64*A≤F := hTotal
  have hList := list_bound W 0 (fun _ => 0) matrix.1.data.toList (fun _ _ => Nat.le_refl _)
  have hLen : matrix.1.data.toList.length=m := by rw [Array.length_toList,matrix.1.size]
  rw [hLen] at hList
  have hListBound : listFootprint W (fun _ => 0) matrix.1.data.toList≤2*m*W+32*W := by
    nlinarith only [hList]
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun x y => x/y)
    opposing own R hOpposing hOwn hBudget
  have hf := fields_bound W (natBits (metadataCap W m K S depth F)) (controls model W depth S hK columns values own opposing) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    change z∈[m,K,S,depth,matrix.2,table.2,selected.2,maximum.2,a,b,a+b,result.2,64*(m+1)*A,64*A,
      matrix.2+table.2,matrix.2+table.2+selected.2,matrix.2+table.2+selected.2+maximum.2,
      matrix.2+table.2+selected.2+maximum.2+a] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    change result.2≤F at hTotal
    dsimp only [A] at hNative
    dsimp only [A] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  rw [controls_length] at hf
  unfold window profile
  dsimp only
  dsimp only [matrix] at hListBound
  omega

end Blotto.GeneralPaperRetainedStrictParentStorage

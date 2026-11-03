import Blotto.GeneralPaperPhysicalScoreMatrix

/-! Read the top label score from each retained field once, then sum those
constructed integers once. No score quotient or strict DP is replayed for
the maximum-score zero guard. Local indices and the result write are priced. -/
namespace Blotto.GeneralPaperStoredScoreMaximum
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000

def values {m K : ℕ} (bits : Bool) (W : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) :
    FixedArrayTable m ℕ×ℕ :=
  let top : Fin K := ⟨K-1,by omega⟩
  PaperIndexedArrayConstruction.run (index bits) (address bits W m) (fun j => (((matrix.read j).read top).1,64*address bits W m))

theorem values_data {m K : ℕ} (bits : Bool) (W : ℕ) (hK : 0<K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) :
    (values bits W hK matrix).1=FixedArrayTable.ofFn (fun j => ((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1) := by
  unfold values
  rw [PaperIndexedArrayConstruction.run_data]
  rfl

def run {m K : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (hK : 0<K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) : ℕ×ℕ :=
  let loaded := values bits W hK matrix
  let total := GeneralPaperValueWeightSum.scan bits model W loaded.1 m le_rfl
  let price := if bits then model.rat else fun _ => 1
  (total.1,loaded.2+total.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) K 1+32*address bits W m)

theorem data {m K : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (hK : 0<K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) :
    (run bits model W hK matrix).1=∑ j,((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1 := by
  change (GeneralPaperValueWeightSum.scan bits model W _ m le_rfl).1=_
  rw [GeneralPaperValueWeightSum.total,values_data]
  simp only [FixedArrayTable.read_ofFn]

theorem actual_data {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m) (S : ℕ)
    (hK : 0<K) (hCap : S<2^depth) :
    (run bits model W hK (GeneralPaperPhysicalScoreMatrix.run bits model W depth columns v S).1).1=
      GeneralPaperScoreMaximum.maximum v S := by
  rw [data,GeneralPaperPhysicalScoreMatrix.data bits model W depth columns v S hK hCap]
  simp only [FixedArrayTable.read_ofFn,GeneralPaperScoreMaximum.score_top,GeneralPaperScoreMaximum.maximum]

theorem arithmetic_work {m K : ℕ} (model : RationalCostModel) (hK : 0<K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) : (run false model 1 hK matrix).2≤256*(m+1) := by
  have hLoad := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 64
    (fun j => (((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1,64))
    (by decide) (fun _ _ => le_rfl) (fun _ => le_rfl)
  have hSum := GeneralPaperValueWeightSum.arithmetic_work model (values false 1 hK matrix).1 m le_rfl
  change (values false 1 hK matrix).2≤_ at hLoad
  change (values false 1 hK matrix).2+(GeneralPaperValueWeightSum.scan false model 1 (values false 1 hK matrix).1 m le_rfl).2+
    GeneralPaperNaturalPrimitivePrice.binary (fun _ => 1) (fun a b => a-b) K 1+32*1≤_
  simp only [GeneralPaperNaturalPrimitivePrice.binary]
  nlinarith only [hLoad,hSum]

theorem bit_work {m K : ℕ} (model : RationalCostModel) (W S : ℕ) (hK : 0<K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hBound : (∑ j,((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1)≤S) :
    (run true model W hK matrix).2≤m*(2*model.rat (1+binaryWordWidth S)+256*arrayWord W m)+
      160*arrayWord W m+2*model.rat (1+binaryWordWidth K) := by
  have hLoad := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) (64*arrayWord W m)
    (fun j => (((matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1,64*arrayWord W m))
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m) (fun _ => le_rfl)
  have hTotal : (GeneralPaperValueWeightSum.scan true model W (values true W hK matrix).1 m le_rfl).1≤S := by
    rw [GeneralPaperValueWeightSum.total,values_data]
    simpa only [FixedArrayTable.read_ofFn] using hBound
  have hSum := GeneralPaperValueWeightSum.bit_work model W S (values true W hK matrix).1 hTotal m le_rfl
  have hTop := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b) K 1 K le_rfl
    (by omega) (Nat.sub_le K 1)
  change (values true W hK matrix).2≤_ at hLoad
  change (values true W hK matrix).2+(GeneralPaperValueWeightSum.scan true model W (values true W hK matrix).1 m le_rfl).2+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) K 1+32*arrayWord W m≤_
  nlinarith only [hLoad,hSum,hTop]

end Blotto.GeneralPaperStoredScoreMaximum

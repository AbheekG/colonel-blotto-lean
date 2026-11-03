import Blotto.GeneralPaperUnsignedCellInputPrice

/-! Both sign copies of each unsigned CDF position. The doubled count and
closed native annotation are formed once; each actual branch is priced.
-/
namespace Blotto.GeneralPaperSignedCellPositionsPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {n : ℕ} (price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) (i : Fin (2*n)) : ℕ × ℕ :=
  let common := GeneralPaperIntegerWordPrice.compare price i.val n
  if h : i.val<n then (summary.read ⟨i.val,h⟩,common+64*W) else
    let j := i.val-n
    let value := summary.read ⟨j,by have := i.isLt; omega⟩
    (U+value,common+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) i.val n+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) U value+64*W)

def header (price : ℕ → ℕ) (n : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 n+
    GeneralPaperClosedArrayCounterPrice.run price 62 (2*n) 18

def run {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    (FixedArrayTable (2*n) ℕ × ℕ) × ℕ :=
  let count := 2*n
  let filled := PaperIndexedArrayConstruction.run (n:=count) index (if bits then arrayWord W count else W) (element price W U summary)
  ((filled.1,62*count+18),filled.2+header price n+64*W)

theorem element_data {n : ℕ} (price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) (i : Fin (2*n)) :
    (element price W U summary i).1=
      if h : i.val<n then summary.read ⟨i.val,h⟩ else U+summary.read ⟨i.val-n,by have := i.isLt; omega⟩ := by
  unfold element
  split <;> rfl

theorem data {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    (run bits index price W U summary).1=GeneralPaperSignedPartition.positions U summary := by
  apply Prod.ext
  · unfold run GeneralPaperSignedPartition.positions
    dsimp only
    rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
    congr 1
    funext i
    exact element_data price W U summary i
  · exact (GeneralPaperSignedPartition.positions_work U summary).symm

theorem codes {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hSummary : ∀ r,summary.read r<U) (i : Fin (2*n)) : (run bits index price W U summary).1.1.read i<2*U := by
  unfold run
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,element_data]
  split
  · rename_i hi
    have h := hSummary ⟨i.val,hi⟩
    omega
  · have h := hSummary ⟨i.val-n,by have := i.isLt; omega⟩
    omega

theorem element_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hSummary : ∀ r,summary.read r<U) (i : Fin (2*n)) :
    (element price W U summary i).2≤5*price (width (2*n) (2*U))+64*W := by
  let N := magnitude (2*n) (2*U)
  let L := width (2*n) (2*U)
  have hW := GeneralPaperSignedCutOperands.word_bound (2*n) (2*U)
  have w (x : ℕ) (hx : x≤N) : 1+binaryWordWidth x≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans hW
  have hi := i.isLt
  have hc := GeneralPaperIntegerWordPrice.compare_le price hMono i.val n L
    (w _ (by dsimp [N,magnitude]; omega)) (w _ (by dsimp [N,magnitude]; omega))
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hr : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b N ha hb hr).trans (Nat.mul_le_mul_left 2 (hMono hW))
  unfold element
  split
  · change GeneralPaperIntegerWordPrice.compare price i.val n+64*W≤5*price L+64*W
    omega
  · rename_i hn
    let j : Fin n := ⟨i.val-n,by omega⟩
    have hv := hSummary j
    have hs := p (fun a b => a-b) i.val n
      (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
    have ha := p (fun a b => a+b) U (summary.read j)
      (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
    change GeneralPaperIntegerWordPrice.compare price i.val n+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) i.val n+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) U (summary.read j)+64*W≤5*price L+64*W
    omega

theorem header_work (price : ℕ → ℕ) (hMono : Monotone price) (n U : ℕ) : header price n≤6*price (width (2*n) (2*U)) := by
  have hw := GeneralPaperSignedCutOperands.word_bound (2*n) (2*U)
  have ha := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 n (magnitude (2*n) (2*U))
    (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono hw))
  have hb := GeneralPaperClosedArrayCounterPrice.work price hMono 62 (2*n) 18 (2*U) (by omega) (by omega)
  unfold header
  omega

def profile (price : ℕ → ℕ) (W n U : ℕ) : ℕ :=
  (2*n)*(5*price (width (2*n) (2*U))+64*W)+44*(2*n+1)*arrayWord W (2*n)+6*price (width (2*n) (2*U))+64*W

def arithmeticProfile (n : ℕ) : ℕ := (2*n)*69+44*(2*n+1)+70

theorem bit_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hSummary : ∀ r,summary.read r<U) : (run true (fun w => w) price W U summary).2≤profile price W n U := by
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W (2*n))
    (5*price (width (2*n) (2*U))+64*W) (element price W U summary)
    (GeneralPaperSummaryArrayControls.array_word_positive W (2*n)) (GeneralPaperSummaryArrayControls.array_index W (2*n))
    (element_work price hMono W U summary hSummary)
  exact Nat.add_le_add_right (Nat.add_le_add hA (header_work price hMono n U)) _

theorem arithmetic_work {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 U summary).2≤arithmeticProfile n := by
  have hEntry (i : Fin (2*n)) : (element (fun _ => 1) 1 U summary i).2≤69 := by
    unfold element
    split <;> simp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary] <;> omega
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 69 (element (fun _ => 1) 1 U summary)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) hEntry
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 U summary).2=
      (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (element (fun _ => 1) 1 U summary)).2+70 := by
    unfold run header
    dsimp only
    simp only [Bool.false_eq_true,ite_false,GeneralPaperClosedArrayCounterPrice.run,GeneralPaperNaturalPrimitivePrice.binary]
  rw [hCost]
  unfold arithmeticProfile
  omega

end Blotto.GeneralPaperSignedCellPositionsPrice

import Blotto.GeneralPaperClosedArrayCounterPrice

/-! Unsigned cell extras retain every projected signed-summary successor
and every cached option code. Guard/index/code operations and the one native
closed counter construction are priced; source annotations are preserved.
-/
namespace Blotto.GeneralPaperUnsignedCellInputPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {n m : ℕ} (price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (i : Fin (n+m)) : ℕ × ℕ :=
  let common := GeneralPaperIntegerWordPrice.compare price i.val n
  if h : i.val<n then
    let projected := GeneralPaperCataloguePointExecution.project price W U (summary.read ⟨i.val,h⟩)
    (projected.1+1,common+projected.2+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) projected.1 1+64*W)
  else
    let j := i.val-n
    (options.read ⟨j,by have := i.isLt; omega⟩,
      common+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) i.val n+64*W)

def run {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) : (FixedArrayTable (n+m) ℕ × ℕ) × ℕ :=
  let count := n+m
  let filled := PaperIndexedArrayConstruction.run (n:=count) index (if bits then arrayWord W count else W)
    (element price W U summary options)
  ((filled.1,62*count+18),filled.2+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) n m+
    GeneralPaperClosedArrayCounterPrice.run price 62 count 18+64*W)

theorem element_data {n m : ℕ} (price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (options : FixedArrayTable m ℕ) (i : Fin (n+m)) :
    (element price W U summary options i).1=
      if h : i.val<n then GeneralPaperSignedUpdatePlan.project U (summary.read ⟨i.val,h⟩)+1
      else options.read ⟨i.val-n,by have := i.isLt; omega⟩ := by
  unfold element
  split
  · dsimp only
    rw [GeneralPaperCataloguePointExecution.project_data]
  · rfl

theorem data {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (run bits index price W U summary options).1=GeneralPaperUnsignedPartition.extras U summary options := by
  apply Prod.ext
  · unfold run GeneralPaperUnsignedPartition.extras
    dsimp only
    rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
    congr 1
    funext i
    exact element_data price W U summary options i
  · exact (GeneralPaperUnsignedPartition.extras_work U summary options).symm

theorem codes {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hSummary : ∀ r,summary.read r<2*U) (hOptions : ∀ r,options.read r<U) (i : Fin (n+m)) :
    (run bits index price W U summary options).1.1.read i≤U := by
  unfold run
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,element_data]
  split
  · rename_i hi
    have h := GeneralPaperUnsignedPartition.project_bound U _ (hSummary ⟨i.val,hi⟩)
    omega
  · exact (hOptions _).le

theorem element_work {n m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (hSummary : ∀ r,summary.read r<2*U) (i : Fin (n+m)) :
    (element price W U summary options i).2≤6*price (width (n+m) (2*U))+96*W := by
  let N := magnitude (n+m) (2*U)
  let L := width (n+m) (2*U)
  have hW := GeneralPaperSignedCutOperands.word_bound (n+m) (2*U)
  have w (x : ℕ) (hx : x≤N) : 1+binaryWordWidth x≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans hW
  have hi := i.isLt
  have hc := GeneralPaperIntegerWordPrice.compare_le price hMono i.val n L
    (w _ (by dsimp [N,magnitude]; omega)) (w _ (by dsimp [N,magnitude]; omega))
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hr : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b N ha hb hr).trans (Nat.mul_le_mul_left 2 (hMono hW))
  have hLocal : GeneralPaperCataloguePointOperands.width U≤L := by
    have h := binaryWordWidth_mono (show U+1≤2*U+1 by omega)
    dsimp [L,width,GeneralPaperCataloguePointOperands.width]
    omega
  unfold element
  split
  · rename_i hin
    let found := GeneralPaperCataloguePointExecution.project price W U (summary.read ⟨i.val,hin⟩)
    have hp := (GeneralPaperCataloguePointOperands.project_work price hMono W U _ (hSummary ⟨i.val,hin⟩)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (hMono hLocal)) (32*W))
    have hb : found.1<U := by
      rw [GeneralPaperCataloguePointExecution.project_data]
      exact GeneralPaperUnsignedPartition.project_bound U _ (hSummary ⟨i.val,hin⟩)
    have hs := p (fun a b => a+b) found.1 1
      (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
    change GeneralPaperIntegerWordPrice.compare price i.val n+found.2+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) found.1 1+64*W≤6*price L+96*W
    change found.2≤_ at hp
    omega
  · have hs := p (fun a b => a-b) i.val n
      (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
    change GeneralPaperIntegerWordPrice.compare price i.val n+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) i.val n+64*W≤6*price L+96*W
    omega

def profile (price : ℕ → ℕ) (W n m U : ℕ) : ℕ :=
  let count := n+m
  count*(6*price (width count (2*U))+96*W)+44*(count+1)*arrayWord W count+6*price (width count (2*U))+64*W

def arithmeticProfile (n m : ℕ) : ℕ := (n+m)*102+44*(n+m+1)+70

theorem header_work (price : ℕ → ℕ) (hMono : Monotone price) (n m U : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) n m+
      GeneralPaperClosedArrayCounterPrice.run price 62 (n+m) 18≤6*price (width (n+m) (2*U)) := by
  have hw := GeneralPaperSignedCutOperands.word_bound (n+m) (2*U)
  have ha := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) n m (magnitude (n+m) (2*U))
    (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono hw))
  have hb := GeneralPaperClosedArrayCounterPrice.work price hMono 62 (n+m) 18 (2*U) (by omega) (by omega)
  omega

theorem bit_work {n m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (hSummary : ∀ r,summary.read r<2*U) :
    (run true (fun w => w) price W U summary options).2≤profile price W n m U := by
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W (n+m))
    (6*price (width (n+m) (2*U))+96*W) (element price W U summary options)
    (GeneralPaperSummaryArrayControls.array_word_positive W (n+m)) (GeneralPaperSummaryArrayControls.array_index W (n+m))
    (element_work price hMono W U summary options hSummary)
  have hH := header_work price hMono n m U
  have h := Nat.add_le_add_right (Nat.add_le_add hA hH) (64*W)
  have hCost : (run true (fun w => w) price W U summary options).2=
      (PaperIndexedArrayConstruction.run (fun w => w) (arrayWord W (n+m)) (element price W U summary options)).2+
      (GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) n m+
        GeneralPaperClosedArrayCounterPrice.run price 62 (n+m) 18)+64*W := by
    simp only [run,ite_true,Nat.add_assoc]
  rw [hCost]
  exact h.trans_eq (by unfold profile; ring)

theorem arithmetic_work {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 U summary options).2≤arithmeticProfile n m := by
  have hEntry (i : Fin (n+m)) : (element (fun _ => 1) 1 U summary options i).2≤102 := by
    unfold element
    split
    · dsimp only
      unfold GeneralPaperCataloguePointExecution.project
      dsimp only
      split <;> simp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary] <;> omega
    · simp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary]; omega
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 102 (element (fun _ => 1) 1 U summary options)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) hEntry
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 U summary options).2=
      (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (element (fun _ => 1) 1 U summary options)).2+70 := by
    unfold run
    dsimp only
    simp only [Bool.false_eq_true,ite_false,GeneralPaperClosedArrayCounterPrice.run,GeneralPaperNaturalPrimitivePrice.binary]
  rw [hCost]
  unfold arithmeticProfile
  omega

theorem every_prefix {n m : ℕ} (index price : ℕ → ℕ) (W A U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (count : ℕ) (hCount : count≤n+m) :
    (PaperIndexedArrayConstruction.fill index A (element price W U summary options) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperUnsignedCellInputPrice

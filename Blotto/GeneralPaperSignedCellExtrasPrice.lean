import Blotto.GeneralPaperSignedCellPositionsPrice

/-! Both sign copies of cached bid codes and the actual sign boundary.
The doubled slot threshold is retained once and passed to every callback.
Native output ordering, duplicates and the complete source counter agree.
-/
namespace Blotto.GeneralPaperSignedCellExtrasPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {m : ℕ} (price : ℕ → ℕ) (W U twice : ℕ) (hTwice : twice=2*m)
    (options : FixedArrayTable m ℕ) (i : Fin (twice+1)) : ℕ × ℕ :=
  let first := GeneralPaperIntegerWordPrice.compare price i.val m
  if h : i.val<m then (options.read ⟨i.val,h⟩,first+64*W) else
    let second := GeneralPaperIntegerWordPrice.compare price i.val twice
    if h' : i.val<twice then
      let j := i.val-m
      let value := options.read ⟨j,by omega⟩
      (U+value,first+second+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) i.val m+
        GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) U value+64*W)
    else (U,first+second+64*W)

def header (price : ℕ → ℕ) (m : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 m+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (2*m) 1+
    GeneralPaperClosedArrayCounterPrice.run price 66 (2*m+1) 18

def run {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (options : FixedArrayTable m ℕ) :
    (FixedArrayTable (2*m+1) ℕ × ℕ) × ℕ :=
  let twice := 2*m
  let count := twice+1
  let filled := PaperIndexedArrayConstruction.run (n:=count) index (if bits then arrayWord W count else W)
    (element price W U twice rfl options)
  ((filled.1,66*count+18),filled.2+header price m+64*W)

theorem element_data {m : ℕ} (price : ℕ → ℕ) (W U twice : ℕ) (hTwice : twice=2*m)
    (options : FixedArrayTable m ℕ) (i : Fin (twice+1)) :
    (element price W U twice hTwice options i).1=
      if h : i.val<m then options.read ⟨i.val,h⟩
      else if h' : i.val<2*m then U+options.read ⟨i.val-m,by omega⟩ else U := by
  subst twice
  unfold element
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (options : FixedArrayTable m ℕ) :
    (run bits index price W U options).1=GeneralPaperSignedPartition.extras U options := by
  apply Prod.ext
  · unfold run GeneralPaperSignedPartition.extras
    dsimp only
    rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
    congr 1
    funext i
    exact element_data price W U (2*m) rfl options i
  · exact (GeneralPaperSignedPartition.extras_work U options).symm

theorem codes {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (options : FixedArrayTable m ℕ)
    (hOptions : ∀ r,options.read r<U) (i : Fin (2*m+1)) : (run bits index price W U options).1.1.read i≤2*U := by
  unfold run
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,element_data]
  split
  · rename_i hi
    have h := hOptions ⟨i.val,hi⟩
    omega
  · split
    · have h := hOptions ⟨i.val-m,by omega⟩
      omega
    · omega

theorem element_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ) (options : FixedArrayTable m ℕ)
    (hOptions : ∀ r,options.read r<U) (i : Fin (2*m+1)) :
    (element price W U (2*m) rfl options i).2≤6*price (width (2*m+1) (2*U))+64*W := by
  let N := magnitude (2*m+1) (2*U)
  let L := width (2*m+1) (2*U)
  have hW := GeneralPaperSignedCutOperands.word_bound (2*m+1) (2*U)
  have w (x : ℕ) (hx : x≤N) : 1+binaryWordWidth x≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans hW
  have hi := i.isLt
  have hf := GeneralPaperIntegerWordPrice.compare_le price hMono i.val m L
    (w _ (by dsimp [N,magnitude]; omega)) (w _ (by dsimp [N,magnitude]; omega))
  have hs := GeneralPaperIntegerWordPrice.compare_le price hMono i.val (2*m) L
    (w _ (by dsimp [N,magnitude]; omega)) (w _ (by dsimp [N,magnitude]; omega))
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hr : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b N ha hb hr).trans (Nat.mul_le_mul_left 2 (hMono hW))
  unfold element
  split
  · change GeneralPaperIntegerWordPrice.compare price i.val m+64*W≤6*price L+64*W
    omega
  · dsimp only
    split
    · rename_i hOut hIn
      let j : Fin m := ⟨i.val-m,by omega⟩
      have hv := hOptions j
      have hSub := p (fun a b => a-b) i.val m
        (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
      have hAdd := p (fun a b => a+b) U (options.read j)
        (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega) (by dsimp [N,magnitude]; omega)
      change GeneralPaperIntegerWordPrice.compare price i.val m+GeneralPaperIntegerWordPrice.compare price i.val (2*m)+
        GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) i.val m+
        GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) U (options.read j)+64*W≤6*price L+64*W
      omega
    · change GeneralPaperIntegerWordPrice.compare price i.val m+GeneralPaperIntegerWordPrice.compare price i.val (2*m)+64*W≤6*price L+64*W
      omega

theorem header_work (price : ℕ → ℕ) (hMono : Monotone price) (m U : ℕ) : header price m≤8*price (width (2*m+1) (2*U)) := by
  have hw := GeneralPaperSignedCutOperands.word_bound (2*m+1) (2*U)
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤magnitude (2*m+1) (2*U)) (hb : b≤magnitude (2*m+1) (2*U))
      (hc : op a b≤magnitude (2*m+1) (2*U)) : GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price (width (2*m+1) (2*U)) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b (magnitude (2*m+1) (2*U)) ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hw))
  have ha := p (fun a b => a*b) 2 m (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  have hb := p (fun a b => a+b) (2*m) 1 (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  have hc := GeneralPaperClosedArrayCounterPrice.work price hMono 66 (2*m+1) 18 (2*U) (by omega) (by omega)
  unfold header
  omega

def profile (price : ℕ → ℕ) (W m U : ℕ) : ℕ :=
  (2*m+1)*(6*price (width (2*m+1) (2*U))+64*W)+44*(2*m+2)*arrayWord W (2*m+1)+8*price (width (2*m+1) (2*U))+64*W

def arithmeticProfile (m : ℕ) : ℕ := (2*m+1)*70+44*(2*m+2)+72

theorem bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ) (options : FixedArrayTable m ℕ)
    (hOptions : ∀ r,options.read r<U) : (run true (fun w => w) price W U options).2≤profile price W m U := by
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W (2*m+1))
    (6*price (width (2*m+1) (2*U))+64*W) (element price W U (2*m) rfl options)
    (GeneralPaperSummaryArrayControls.array_word_positive W (2*m+1)) (GeneralPaperSummaryArrayControls.array_index W (2*m+1))
    (element_work price hMono W U options hOptions)
  change _≤(2*m+1)*(6*price (width (2*m+1) (2*U))+64*W)+44*(2*m+2)*arrayWord W (2*m+1) at hA
  exact Nat.add_le_add_right (Nat.add_le_add hA (header_work price hMono m U)) _

theorem arithmetic_work {m : ℕ} (U : ℕ) (options : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 U options).2≤arithmeticProfile m := by
  have hEntry (i : Fin (2*m+1)) : (element (fun _ => 1) 1 U (2*m) rfl options i).2≤70 := by
    unfold element
    split
    · simp only [GeneralPaperIntegerWordPrice.compare]; omega
    · dsimp only
      split <;> simp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary] <;> omega
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 70 (element (fun _ => 1) 1 U (2*m) rfl options)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) hEntry
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 U options).2=
      (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (element (fun _ => 1) 1 U (2*m) rfl options)).2+72 := by
    unfold run header
    dsimp only
    simp only [Bool.false_eq_true,ite_false,GeneralPaperClosedArrayCounterPrice.run,GeneralPaperNaturalPrimitivePrice.binary]
  rw [hCost]
  unfold arithmeticProfile
  omega

end Blotto.GeneralPaperSignedCellExtrasPrice

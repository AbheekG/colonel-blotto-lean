import Blotto.GeneralPaperValueRoundArray

/-! Sum the returned short integer weights once. The row is borrowed;
all addition operands are bounded from the actual complete native total.
This loop never recombines original rational values or denominators. -/
namespace Blotto.GeneralPaperValueWeightSum
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def scan {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) :
    (count : ℕ) → count≤n → ℕ × ℕ
  | 0,_ => (0,64*address bits W n)
  | count+1,hc =>
    let previous := scan bits model W values count (by omega)
    let value := values.read ⟨count,by omega⟩
    let A := address bits W n
    let primitive := if bits then model.rat else fun _ => 1
    (previous.1+value,previous.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) previous.1 value+
      PaperIndexedArrayConstruction.stepWork (index bits) A count+64*A)

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : (scan bits model W values count hc).1=∑ i : Fin count,values.read ⟨i.val,by omega⟩ := by
  induction count with
  | zero => simp only [scan,Finset.univ_eq_empty,Finset.sum_empty]
  | succ count ih =>
    rw [scan]
    dsimp only
    rw [ih (by omega),Fin.sum_univ_castSucc]
    rfl

theorem total {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) :
    (scan bits model W values n le_rfl).1=∑ j,values.read j := data bits model W values n le_rfl

theorem prefix_mono {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ)
    (i j : ℕ) (hij : i≤j) (hj : j≤n) :
    (scan bits model W values i (by omega)).1≤(scan bits model W values j hj).1 := by
  induction j generalizing i with
  | zero =>
    have hi : i=0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i=j+1
    · subst i; exact le_rfl
    · exact (ih i (by omega) (by omega)).trans (Nat.le_add_right ..)

theorem item_le_total {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℕ) (j : Fin n) :
    values.read j≤(scan bits model W values n le_rfl).1 := by
  rw [total]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem bit_work {n : ℕ} (model : RationalCostModel) (W B : ℕ) (values : FixedArrayTable n ℕ)
    (hB : (scan true model W values n le_rfl).1≤B) (count : ℕ) (hc : count≤n) :
    (scan true model W values count hc).2≤count*(2*model.rat (1+binaryWordWidth B)+128*arrayWord W n)+64*arrayWord W n := by
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
  induction count with
  | zero => simp only [scan,address,ite_true,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
    have hp := (prefix_mono true model W values count n (by omega) le_rfl).trans hB
    have hq := (item_le_total true model W values ⟨count,by omega⟩).trans hB
    have hs : (scan true model W values count (by omega)).1+values.read ⟨count,by omega⟩≤B :=
      (prefix_mono true model W values (count+1) n hc le_rfl).trans hB
    have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
      _ _ B hp hq hs
    have hi := GeneralPaperSummaryArrayControls.array_index W n count (by omega)
    have hPrev := ih (by omega)
    rw [scan]
    dsimp only
    simp only [address,index,ite_true,PaperIndexedArrayConstruction.stepWork]
    nlinarith only [hPrev,hAdd,hi,hA]

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (values : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) :
    (scan false model 1 values count hc).2≤108*count+64 := by
  induction count with
  | zero => simp only [scan,address,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.zero_add,Nat.mul_one,le_refl]
  | succ count ih =>
    have h := ih (by omega)
    rw [scan]
    dsimp only
    simp only [address,index,Bool.false_eq_true,ite_false,GeneralPaperNaturalPrimitivePrice.binary,
      PaperIndexedArrayConstruction.stepWork,Nat.mul_one]
    nlinarith only [h]

end Blotto.GeneralPaperValueWeightSum

import Blotto.PlayerSpecificBitRatioSortContract

/-! Actual construction of a rational input table from its input-coordinate
reader. Each coordinate is read/copied once; measured control words and all
native array/return overhead are priced. -/
namespace Blotto.PlayerSpecificInputArrayExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificBitRatioSortBudget
set_option autoImplicit false
set_option maxHeartbeats 2000000

def callback {N : ℕ} (model : RationalCostModel) (A : ℕ) (input : Fin N → ℚ) (j : Fin N) : ℚ×ℕ :=
  let q:=input j
  (q,price model (copyRow [q])+12*A)
def run {N : ℕ} (model : RationalCostModel) (input : Fin N → ℚ) : FixedArrayTable N ℚ×ℕ :=
  let measured:=PlayerSpecificWidthExecution.run model (N+1)
  let A:=PlayerSpecificBitRatioSortExecution.address model measured.1
  let table:=PaperIndexedArrayConstruction.run model.rat A (callback model A input)
  (table.1,measured.2+table.2+64*(N+1)*A)

theorem value {N : ℕ} (model : RationalCostModel) (input : Fin N → ℚ) :
    (run model input).1=FixedArrayTable.ofFn input := by
  simp only [run,PaperIndexedArrayConstruction.run_data]
  rfl

theorem callback_cost {N : ℕ} (model : RationalCostModel) (A H : ℕ) (input : Fin N → ℚ)
    (hi : ∀ j,RationalHeight (input j) H) (hA : A≤64*model.rat (width N H)) (j : Fin N) :
    (callback model A input j).2≤1000*model.rat (width N H) := by
  have hp:=price_bound model (width N H) (by unfold width; omega) _ (copyRow_fits _ [input j]
    (fun q hq => (rationalWordWidth_of_height ((cons_height (hi j) (nil_height _)) q hq)).trans (by unfold width; omega))
    (by simp; unfold width; omega))
  rw [copyRow_length] at hp
  simp only [List.length_cons,List.length_nil] at hp
  simp only [callback]
  nlinarith only [hp,hA]

theorem source_cost {N : ℕ} (model : RationalCostModel) (H : ℕ) (input : Fin N → ℚ)
    (hi : ∀ j,RationalHeight (input j) H) :
    (run model input).2≤10000*(N+1)*model.rat (width N H) := by
  have hm:=measured_bounds model N H
  have htable:=GeneralPaperControlArrayPrice.indexed_work model.rat
    (PlayerSpecificBitRatioSortExecution.address model (PlayerSpecificWidthExecution.run model (N+1)).1)
    (1000*model.rat (width N H)) (callback model _ input) hm.1 hm.2.2
    (callback_cost model _ H input hi hm.2.1)
  have ha:=Nat.mul_le_mul_left (44*(N+1)) hm.2.1
  have hp : (PaperIndexedArrayConstruction.run model.rat
      (PlayerSpecificBitRatioSortExecution.address model (PlayerSpecificWidthExecution.run model (N+1)).1)
      (callback model _ input)).2≤4000*(N+1)*model.rat (width N H) := htable.trans (by nlinarith only [ha])
  have hmeasure:=measurement_cost model N H
  have hframe:=Nat.mul_le_mul_left (64*(N+1)) hm.2.1
  simp only [run]
  nlinarith only [hp,hmeasure,hframe]

end Blotto.PlayerSpecificInputArrayExecution

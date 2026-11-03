import Blotto.GeneralPaperFloorSearchPrice
import Blotto.GeneralPaperProfitGridRound

/-! Both queries borrow the prepared arrays and depth. Leaf scaling, cuts,
native annotation updates and reference/control operations are executed once.
The cost projection is erased analysis, not another grid traversal. -/
namespace Blotto.GeneralPaperProfitGridRoundExecution
open GeneralPaperProfitGridPrepare
set_option autoImplicit false
set_option maxHeartbeats 5000000

def merge {q w B : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ)
    (grid : Prepared q w B) (numerator : ℕ) : GeneralPaperFloorSearch.Result grid.size × ℕ :=
  let found := GeneralPaperFloorSearchPrice.run bits primitive W grid.depth grid.numerators grid.nonempty (numerator+1)
  (⟨found.1.label,found.1.work+8⟩,found.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) numerator 1+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) found.1.work 8+64*W)

def leaf {q w B : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ)
    (grid : Prepared q w B) (numerator : ℕ) : GeneralPaperFloorSearch.Result grid.size × ℕ :=
  let found := GeneralPaperFloorSearchPrice.run bits primitive W grid.depth grid.leafNumerators grid.nonempty
    (numerator*grid.profitDenominator+1)
  (⟨found.1.label,found.1.work+16⟩,found.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) numerator grid.profitDenominator+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (numerator*grid.profitDenominator) 1+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) found.1.work 16+64*W)

theorem merge_data {q w B : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ)
    (grid : Prepared q w B) (numerator : ℕ) :
    (merge bits primitive W grid numerator).1=GeneralPaperProfitGridRound.merge grid numerator := by
  simp only [merge,GeneralPaperFloorSearchPrice.data bits primitive W grid.depth grid.numerators grid.nonempty
    (numerator+1) grid.depthCap,GeneralPaperProfitGridRound.merge]

theorem leaf_data {q w B : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ)
    (grid : Prepared q w B) (numerator : ℕ) :
    (leaf bits primitive W grid numerator).1=GeneralPaperProfitGridRound.leaf grid numerator := by
  simp only [leaf,GeneralPaperFloorSearchPrice.data bits primitive W grid.depth grid.leafNumerators grid.nonempty
    (numerator*grid.profitDenominator+1) grid.depthCap,GeneralPaperProfitGridRound.leaf]

theorem merge_arithmetic_work {q w B : ℕ} (grid : Prepared q w B) (numerator : ℕ) :
    (merge false (fun _ => 1) 1 grid numerator).2≤512*(grid.depth+1)^2+206 := by
  have h := GeneralPaperFloorSearchPrice.arithmetic_work grid.depth grid.numerators grid.nonempty (numerator+1)
  change (GeneralPaperFloorSearchPrice.run false (fun _ => 1) 1 grid.depth grid.numerators grid.nonempty (numerator+1)).2+2+2+64≤_
  omega

theorem leaf_arithmetic_work {q w B : ℕ} (grid : Prepared q w B) (numerator : ℕ) :
    (leaf false (fun _ => 1) 1 grid numerator).2≤512*(grid.depth+1)^2+208 := by
  have h := GeneralPaperFloorSearchPrice.arithmetic_work grid.depth grid.leafNumerators grid.nonempty (numerator*grid.profitDenominator+1)
  change (GeneralPaperFloorSearchPrice.run false (fun _ => 1) 1 grid.depth grid.leafNumerators grid.nonempty
    (numerator*grid.profitDenominator+1)).2+2+2+2+64≤_
  omega

end Blotto.GeneralPaperProfitGridRoundExecution

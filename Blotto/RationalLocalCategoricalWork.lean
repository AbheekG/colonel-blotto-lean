import Blotto.RationalCategoricalCallbackWork
import Blotto.RationalGroupProgramHeight

/-! Concrete local continuations inherit their categorical callback prices.
The nine-slot uniform/three-variable and 81-slot gluing branches are covered.
Descriptor preparation, interpolation/output, Boolean control and the four-
variable small continuation remain separate obligations. -/

namespace Blotto.RationalUniformGroupSpec

theorem categoricalBitWork_bound {m : ℕ} (i : RationalUniformGroupSpec m)
    (model : RationalCostModel) (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (hm : m = 2 ∨ m = 3)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    ((i.program hm K scalarBits).machine).cachedCallbackWork (categoricalCallbackBitCost model)
      N bits (.state (i.program hm K scalarBits).start) pos hpos ≤
      747 * model.rat (categoricalRequestWidth 9 (expressionHeightBudget s 18)) := by
  exact (i.lottery hm).choiceCallbackBitWork_bound model 0 _ (h.lottery hs hm)
    K scalarBits N bits pos hpos

theorem categoricalArithmeticWork_bound {m : ℕ} (i : RationalUniformGroupSpec m)
    (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (hm : m = 2 ∨ m = 3)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    ((i.program hm K scalarBits).machine).cachedCallbackWork categoricalCallbackArithmeticWork
      N bits (.state (i.program hm K scalarBits).start) pos hpos ≤ 180 := by
  exact (i.lottery hm).choiceCallbackArithmeticWork_bound 0 _ (h.lottery hs hm) K scalarBits N bits pos hpos

end Blotto.RationalUniformGroupSpec
namespace Blotto.RationalMixedGroupSpec

theorem threeCategoricalBitWork_bound (i : RationalMixedGroupSpec 2) (model : RationalCostModel)
    (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (hm : 2 = 2 ∨ 2 = 3)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    ((i.program hm K outerBits scalarBits).machine).cachedCallbackWork (categoricalCallbackBitCost model)
      N bits (.state (i.program hm K outerBits scalarBits).start) pos hpos ≤
      747 * model.rat (categoricalRequestWidth 9 (expressionHeightBudget s 18)) := by
  exact i.threeInput.segmentLottery.choiceCallbackBitWork_bound model 0 _
    (RationalThreeSpecCode.descriptor_height i.threeInput s hs h.three_environment) K scalarBits N bits pos hpos

theorem threeCategoricalArithmeticWork_bound (i : RationalMixedGroupSpec 2)
    (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (hm : 2 = 2 ∨ 2 = 3)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    ((i.program hm K outerBits scalarBits).machine).cachedCallbackWork categoricalCallbackArithmeticWork
      N bits (.state (i.program hm K outerBits scalarBits).start) pos hpos ≤ 180 := by
  exact i.threeInput.segmentLottery.choiceCallbackArithmeticWork_bound 0 _
    (RationalThreeSpecCode.descriptor_height i.threeInput s hs h.three_environment) K scalarBits N bits pos hpos

end Blotto.RationalMixedGroupSpec
namespace Blotto.RationalFourInput

theorem gluingCategoricalBitWork_bound (i : RationalFourInput) (model : RationalCostModel)
    (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.gluingMachine hcase K scalarBits).cachedCallbackWork (categoricalCallbackBitCost model)
      N bits (.state (i.gluingDescriptor hcase).start) pos hpos ≤
      53379 * model.rat (categoricalRequestWidth 81 (expressionHeightBudget s 36)) := by
  exact (i.gluingDescriptor hcase).choiceCallbackBitWork_bound model 0 _ (h.gluingDescriptor hs hcase)
    K scalarBits N bits pos hpos

theorem gluingCategoricalArithmeticWork_bound (i : RationalFourInput)
    (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (i.gluingMachine hcase K scalarBits).cachedCallbackWork categoricalCallbackArithmeticWork
      N bits (.state (i.gluingDescriptor hcase).start) pos hpos ≤ 13284 := by
  exact (i.gluingDescriptor hcase).choiceCallbackArithmeticWork_bound 0 _ (h.gluingDescriptor hs hcase)
    K scalarBits N bits pos hpos

end Blotto.RationalFourInput

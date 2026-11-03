import Blotto.RoundingTree
import Blotto.MidpointSegments

/-! Resource lotteries preserve a uniform terminal CDF error through their
exact branch weights. The bound does not grow with the tree height. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

namespace RoundingTree

theorem eval_CDFClose {n m : ℕ} (T : RoundingTree n) (ideal approximate : Allocation n → Mixed m)
    {δ : ℝ} (h : T.ForLeaves (fun r => CDFClose (approximate r) (ideal r) δ)) :
    CDFClose (T.eval approximate) (T.eval ideal) δ := by
  induction T with
  | leaf r => exact h
  | fork p hp a b ha hb =>
    change CDFClose (binaryLaw p hp (a.eval approximate) (b.eval approximate))
      (binaryLaw p hp (a.eval ideal) (b.eval ideal)) δ
    apply probabilityMixture_CDFClose
    intro i
    fin_cases i
    · exact ha h.1
    · exact hb h.2

end RoundingTree
end Blotto

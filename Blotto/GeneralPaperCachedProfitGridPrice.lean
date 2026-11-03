import Blotto.GeneralPaperProfitGridQueryOperands
import Blotto.GeneralPaperNativeProfitOperands

/-! Actual retained profit parameters discharge all query operands. Leaf
profits and even unused merge pairs are covered without a DP validity pass.
The prepared-grid identity is a proof, not a construction at query time. -/
namespace Blotto.GeneralPaperCachedProfitGridPrice
open GeneralPaperProfitGridPrepare
set_option autoImplicit false
set_option maxHeartbeats 6000000

def profile (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  4096*((prepare p.qProf p.width p.exponent).depth+1)*
    (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))

theorem leaf_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (p : GeneralPaperProfitParameters.Parameters) (hp : p=GeneralPaperProfitParameters.parameters m lambda k Qv)
    (grid : Prepared p.qProf p.width p.exponent) (hGrid : grid=prepare p.qProf p.width p.exponent)
    (numerator : ℕ) (hNum : numerator≤2*p.qProf) :
    (GeneralPaperProfitGridRoundExecution.leaf true primitive W grid numerator).2≤profile primitive W m lambda k Qv := by
  subst grid; subst p
  have h := GeneralPaperProfitGridQueryOperands.leaf_operands
    (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
    (GeneralPaperProfitParameters.parameters m lambda k Qv).width
    (GeneralPaperProfitParameters.parameters m lambda k Qv).exponent numerator hNum
  have hWork := GeneralPaperProfitGridRoundPrice.leaf_work primitive hMono W _ _ numerator h.1 h.2.1 h.2.2.1 h.2.2.2
  have hPrice := hMono (GeneralPaperProfitGridQueryOperands.source_word m lambda k Qv)
  exact hWork.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hPrice W))

theorem merge_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (p : GeneralPaperProfitParameters.Parameters) (hp : p=GeneralPaperProfitParameters.parameters m lambda k Qv)
    (grid : Prepared p.qProf p.width p.exponent) (hGrid : grid=prepare p.qProf p.width p.exponent)
    (i j : Fin grid.size) :
    (GeneralPaperProfitGridRoundExecution.merge true primitive W grid (grid.numerators.read i+grid.numerators.read j)).2≤
      profile primitive W m lambda k Qv := by
  subst grid; subst p
  have h := GeneralPaperProfitGridQueryOperands.merge_operands _ _ _ i j
  have hWork := GeneralPaperProfitGridRoundPrice.merge_work primitive hMono W _ _ _ h.1 h.2
  have hPrice := hMono (GeneralPaperProfitGridQueryOperands.source_word m lambda k Qv)
  exact hWork.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hPrice W))

theorem native_profit_bound (m lambda k Qv weight positive negative : ℕ) (hWeight : weight≤Qv)
    (hPositive : positive≤(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*weight*
      ((GeneralPaperSourceParameters.prepare k).meshDenominator+positive-negative)≤
      2*(GeneralPaperProfitParameters.parameters m lambda k Qv).qProf := by
  have h := GeneralPaperNativeProfitOperands.profit_bound (GeneralPaperTrajectoryParameters.prepare lambda k).rows
    Qv (GeneralPaperSourceParameters.prepare k).meshDenominator weight positive negative hWeight hPositive
  rw [GeneralPaperProfitParameters.qProf_spec]
  exact h.trans_eq (by ring)

end Blotto.GeneralPaperCachedProfitGridPrice

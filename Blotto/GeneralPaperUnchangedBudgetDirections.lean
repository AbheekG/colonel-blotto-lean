import Blotto.GeneralPaperSourcePairRun

/-! The actual unmodified defender faces a weakly smaller budget in its
own unit normalization. The classifier's unchanged case is exact equality.
-/
namespace Blotto.GeneralPaperUnchangedBudgetDirections
open GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem none_rich (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=none) :
    b≤((opposingBudget m k b false/ownBudget m k b false:ℚ):ℝ) := by
  have he := GeneralPaperProxyClassifierPaths.unchanged m k b hb hModify
  simp only [ownBudget,opposingBudget,Bool.false_eq_true,ite_false,div_one,he,le_refl]

theorem none_poor (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=none) :
    1/b≤((opposingBudget m k b true/ownBudget m k b true:ℚ):ℝ) := by
  have he := GeneralPaperProxyClassifierPaths.unchanged m k b hb hModify
  simp only [ownBudget,opposingBudget,ite_true,Rat.cast_div,Rat.cast_one,he,le_refl]

theorem modify_rich (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    1/b≤((opposingBudget m k b true/ownBudget m k b true:ℚ):ℝ) := by
  have hd := (GeneralPaperProxyClassifierPaths.rich_direction m k b hb hModify).1
  have hp : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value := by
    exact_mod_cast (GeneralPaperProxyClassifier.proxy_unit m k b hb).1
  simpa only [ownBudget,opposingBudget,ite_true,Rat.cast_div,Rat.cast_one] using one_div_le_one_div_of_le hp hd.le

theorem modify_poor (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    b≤((opposingBudget m k b false/ownBudget m k b false:ℚ):ℝ) := by
  have hd := (GeneralPaperProxyClassifierPaths.poor_direction m k b hb hModify).2
  simpa only [ownBudget,opposingBudget,Bool.false_eq_true,ite_false,div_one] using hd.le

end Blotto.GeneralPaperUnchangedBudgetDirections

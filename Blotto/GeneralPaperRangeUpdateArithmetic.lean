import Blotto.GeneralPaperRangeUpdateExecution

/-! The complete unit-arithmetic traversal price is linear in its actual
visit count. Native visit geometry then gives a linear-height price. Only
selected recursive calls/parent recomputations execute, and all work/visit
metadata and reference/control operations are included.
-/
namespace Blotto.GeneralPaperRangeUpdateArithmetic
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalGeometry
open GeneralPaperRangeUpdateExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def nodeProfile (m lambda k Qv : ℕ) : ℕ :=
  4194304*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2+1024

theorem guard_work (start span a b : ℚ) : guardCost (fun _ => 1) 1 start span a b=68 := rfl

theorem split_work (height : ℕ) (start span : ℚ) : splitCost (fun _ => 1) 1 height start span=70 := rfl

theorem raise_work (amount : ℕ) {height : ℕ} (n : Node height) : raiseCost (fun _ => 1) 1 amount n=66 := rfl

theorem metadata_work {height : ℕ} (left right : GeneralPaperIntervalUpdate.Result height)
    (joined : GeneralPaperDyadicMultiply.Result) : metadataCost (fun _ => 1) left right joined=10 := rfl

theorem combine (lp rp pp lv rv P K : ℕ) (hl : lp≤lv*K) (hr : rp≤rv*K)
    (hp : pp≤P) (hK : P+344≤K) : lp+rp+pp+68+68+70+10+128≤(1+lv+rv)*K := by
  nlinarith

theorem visited_work (price : ℕ → ℕ) (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ) :
    (run false price 1 c lo hi amount height n start span).2≤
      (run false price 1 c lo hi amount height n start span).1.visits*nodeProfile m lambda k Qv := by
  have hK : 1024≤nodeProfile m lambda k Qv := by unfold nodeProfile; omega
  induction height generalizing start span with
  | zero =>
    by_cases hD : Disjoint start span lo hi
    · conv_lhs => rw [run.eq_def,ite_eq_left hD]
      conv_rhs => rw [run.eq_def,ite_eq_left hD]
      change 132≤1*nodeProfile m lambda k Qv
      omega
    · by_cases hC : Covered start span lo hi
      · conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        change 266≤1*nodeProfile m lambda k Qv
        omega
      · conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        change 200≤1*nodeProfile m lambda k Qv
        omega
  | succ height ih =>
    by_cases hD : Disjoint start span lo hi
    · conv_lhs => rw [run.eq_def,ite_eq_left hD]
      conv_rhs => rw [run.eq_def,ite_eq_left hD]
      change 132≤1*nodeProfile m lambda k Qv
      omega
    · by_cases hC : Covered start span lo hi
      · conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_left hC]
        change 266≤1*nodeProfile m lambda k Qv
        omega
      · let left := run false price 1 c lo hi amount height (leftChild n) start (span/2)
        let right := run false price 1 c lo hi amount height (rightChild n) (start+span/2) (span/2)
        have hl := ih (leftChild n) start (span/2)
        have hr := ih (rightChild n) (start+span/2) (span/2)
        have hp := GeneralPaperParentCachePrice.arithmetic_work m lambda k Qv c hc left.1.node right.1.node
        change left.2≤left.1.visits*nodeProfile m lambda k Qv at hl
        change right.2≤right.1.visits*nodeProfile m lambda k Qv at hr
        conv_lhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        conv_rhs => rw [run.eq_def,ite_eq_right hD,ite_eq_right hC]
        simp only [Bool.false_eq_true,ite_false,guard_work,split_work,metadata_work,parent,Nat.mul_one]
        exact combine left.2 right.2 (GeneralPaperParentCachePrice.arithmetic c left.1.node right.1.node).2
          left.1.visits right.1.visits (4194304*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2)
          (nodeProfile m lambda k Qv) hl hr hp (by unfold nodeProfile; omega)

theorem linear_work (price : ℕ → ℕ) (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ) (hSpan : 0<span)
    (hValid : Valid lambda k n)
    (hOutput : GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run c.powers lo hi amount height n start span).node) :
    (run false price 1 c lo hi amount height n start span).2≤(1+4*height)*nodeProfile m lambda k Qv := by
  have hw := visited_work price m lambda k Qv c hc lo hi amount height n start span
  rw [GeneralPaperRangeUpdateExecution.data false price 1 m lambda k Qv c hc lo hi amount height n start span hValid hOutput] at hw
  exact hw.trans (Nat.mul_le_mul_right _ (GeneralPaperIntervalUpdate.visits_linear c.powers lo hi amount height n start span hSpan))

theorem same_data (price : ℕ → ℕ) (W m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi : ℚ) (amount height : ℕ) (n : Node height) (start span : ℚ) (hValid : Valid lambda k n)
    (hOutput : GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run c.powers lo hi amount height n start span).node) :
    (run true price W c lo hi amount height n start span).1=(run false price 1 c lo hi amount height n start span).1 := by
  rw [GeneralPaperRangeUpdateExecution.data true price W m lambda k Qv c hc lo hi amount height n start span hValid hOutput,
    GeneralPaperRangeUpdateExecution.data false price 1 m lambda k Qv c hc lo hi amount height n start span hValid hOutput]

end Blotto.GeneralPaperRangeUpdateArithmetic

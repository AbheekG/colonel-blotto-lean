import Blotto.PlayerSpecificAlgebraicCandidates

/-! Priced rational-factor matching against an actual retained interval.
All comparisons, enclosing controls and input/option copies are executed. -/
namespace Blotto.PlayerSpecificCandidateLookup
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 2000000

def frame (roots : Data) (node : Interval) : Trace :=
  copyRow roots++PlayerSpecificSplitExecution.copyInterval node++[.control roots.length]

def run (model : RationalCostModel) : Data → Interval → Option ℚ×ℕ
  | [],node => (none,price model (frame [] node)+price model [.control 0])
  | q::qs,node =>
    let low:=PlayerSpecificRationalTrace.compare q node.lo
    let high:=PlayerSpecificRationalTrace.compare q node.hi
    let priorPrice:=price model (frame (q::qs) node)+price model low.2+price model high.2
    if !low.1 && high.1 then
      (some q,priorPrice+price model (copyRow [q])+price model [.control 1])
    else
      let rest:=run model qs node
      (rest.1,priorPrice+rest.2+price model (copyRow rest.1.toList)+price model [.control 0])

theorem tests (q : ℚ) (node : Interval) :
    (!(PlayerSpecificRationalTrace.compare q node.lo).1 && (PlayerSpecificRationalTrace.compare q node.hi).1)=
      PlayerSpecificAlgebraicCandidates.inside node q := by
  apply Bool.eq_iff_iff.mpr
  simp [PlayerSpecificRationalTrace.compare,PlayerSpecificAlgebraicCandidates.inside,not_le]

theorem value (model : RationalCostModel) (roots : Data) (node : Interval) :
    (run model roots node).1=PlayerSpecificAlgebraicCandidates.lookup roots node := by
  induction roots with
  | nil => rfl
  | cons q qs ih =>
    rw [run,tests]
    simp only [PlayerSpecificAlgebraicCandidates.lookup,List.find?_cons]
    cases ht : PlayerSpecificAlgebraicCandidates.inside node q
    · simp only [Bool.false_eq_true,ite_false]
      exact ih
    · simp only [ite_true]

theorem option_height (model : RationalCostModel) (roots : Data) (node : Interval) (H : ℕ)
    (hH : HasHeight roots H) : HasHeight (run model roots node).1.toList H := by
  cases he : (run model roots node).1 with
  | none => exact nil_height H
  | some q =>
    have hm:=List.mem_of_find?_eq_some ((value model roots node).symm.trans he)
    exact cons_height (hH q hm) (nil_height H)

theorem frame_cost (model : RationalCostModel) (roots : Data) (node : Interval) (H W : ℕ)
    (hH : HasHeight roots H) (hlen : roots.length≤3)
    (hlo : RationalHeight node.lo H) (hhi : RationalHeight node.hi H)
    (hl : node.loValue≤5) (hh : node.hiValue≤5) (hHW : 1+2*H≤W) (hW : 32≤W) :
    price model (frame roots node)≤100*model.rat W := by
  have hr:=PlayerSpecificExtendedCopyCost.row_cost model roots H W hH (by omega) hHW hW
  have hn:=PlayerSpecificSplitTraceCost.copyInterval_cost model node H W hlo hhi hl hh hHW (by omega)
  have hc:=event_price model W (by omega) (.control roots.length) ((control_width _).trans (by omega))
  change price model [.control roots.length]≤3*model.rat W at hc
  simp only [frame,price_append]
  nlinarith only [hr,hn,hc]

theorem run_cost (model : RationalCostModel) (roots : Data) (node : Interval) (H W : ℕ)
    (hH : HasHeight roots H) (hlen : roots.length≤3)
    (hlo : RationalHeight node.lo H) (hhi : RationalHeight node.hi H)
    (hl : node.loValue≤5) (hh : node.hiValue≤5) (hHW : 1+2*H≤W) (hW : 32≤W) :
    (run model roots node).2≤200*(roots.length+1)*model.rat W := by
  induction roots with
  | nil =>
    have hf:=frame_cost model [] node H W hH hlen hlo hhi hl hh hHW hW
    have hc:=event_price model W (by omega) (.control 0) ((control_width 0).trans (by omega))
    change price model [.control 0]≤3*model.rat W at hc
    simp only [run,List.length_nil]
    nlinarith only [hf,hc]
  | cons q qs ih =>
    have hf:=frame_cost model (q::qs) node H W hH hlen hlo hhi hl hh hHW hW
    have hqw: rationalWordWidth q≤W := (rationalWordWidth_of_height (head_height hH)).trans hHW
    have hlw: rationalWordWidth node.lo≤W := (rationalWordWidth_of_height hlo).trans hHW
    have hhw: rationalWordWidth node.hi≤W := (rationalWordWidth_of_height hhi).trans hHW
    have hlow:=price_bound model W (by omega) _ (compare_fits W q node.lo hqw hlw (by omega))
    have hhigh:=price_bound model W (by omega) _ (compare_fits W q node.hi hqw hhw (by omega))
    rw [compare_length] at hlow hhigh
    have hzero:=event_price model W (by omega) (.control 0) ((control_width 0).trans (by omega))
    have hone:=event_price model W (by omega) (.control 1) ((control_width 1).trans (by omega))
    change price model [.control 0]≤3*model.rat W at hzero
    change price model [.control 1]≤3*model.rat W at hone
    rw [run]
    dsimp only
    split
    · have hcopy:=PlayerSpecificExtendedCopyCost.row_cost model [q] H W
        (cons_height (head_height hH) (nil_height H)) (by simp) hHW hW
      simp only [List.length_cons]
      nlinarith only [hf,hlow,hhigh,hcopy,hone]
    · have ht:=ih (tail_height hH) (by simp only [List.length_cons] at hlen; omega)
      have hcopy:=PlayerSpecificExtendedCopyCost.row_cost model (run model qs node).1.toList H W
        (option_height model qs node H (tail_height hH)) (by cases (run model qs node).1 <;> simp) hHW hW
      simp only [List.length_cons]
      nlinarith only [hf,hlow,hhigh,ht,hcopy,hzero]

end Blotto.PlayerSpecificCandidateLookup

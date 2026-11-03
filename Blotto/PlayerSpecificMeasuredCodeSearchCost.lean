import Blotto.PlayerSpecificOutputFloorPredicateSourceCost

/-! Uniform source work for the actual one-branch measured code search.
The bound charges only visited predicate calls, both natural midpoint
operations, all node controls, and returned code/visit words. -/
namespace Blotto.PlayerSpecificMeasuredCodeSearchCost
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def width (C : ℕ) : ℕ := binaryWordWidth (C+2)+3
def work (model : RationalCostModel) (C fuel A : ℕ) : ℕ :=
  fuel*(A+150*model.rat (width C))+9*model.rat (width C)

theorem word_width (C n : ℕ) (hn : n≤C+2) : 1+binaryWordWidth n≤width C := by
  have h:=binaryWordWidth_mono hn
  unfold width
  omega

theorem cost (model : RationalCostModel) (C A fuel : ℕ) (predicate : ℕ→Bool×ℕ)
    (lo hi : ℕ) (hlo : lo≤hi) (hhi : hi≤C+1) (hfuel : fuel≤C+2)
    (hpredicate : ∀ code≤C,(predicate code).2≤A) :
    (PlayerSpecificMeasuredCodeSearch.run model fuel predicate lo hi).2≤work model C fuel A := by
  let W:=width C
  let R:=model.rat W
  have hW : 1≤W := by dsimp [W,width]; omega
  have wordBound (n : ℕ) (hn : n≤C+2) : binaryWordWidth n≤W := by
    have h:=word_width C n hn
    dsimp only [W] at *
    omega
  induction fuel generalizing lo hi with
  | zero =>
    have hw : ∀ word∈[lo,hi,0],binaryWordWidth word≤W := by
      intro word hword
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hword
      rcases hword with hw|hw|hw
      · simpa only [hw] using wordBound lo (by omega)
      · simpa only [hw] using wordBound hi (by omega)
      · simpa only [hw] using wordBound 0 (by omega)
    have hc := PlayerSpecificAlgebraicCallerFrame.controls_cost model [lo,hi,0] W hw hW
    change price model ([lo,hi,0].map Event.control)≤_ at hc
    have hc' : price model [.control lo,.control hi,.control 0]≤9*R := by
      simpa only [List.map_cons,List.map_nil,List.length_cons,List.length_nil,
        Nat.reduceAdd,Nat.reduceMul] using hc
    simpa only [PlayerSpecificMeasuredCodeSearch.run,work,Nat.zero_mul,Nat.zero_add] using hc'
  | succ fuel ih =>
    by_cases h : lo<hi
    · let mid:=lo+(hi-lo)/2
      let succMid:=mid+1
      let tested:=predicate mid
      let next:=if tested.1 then PlayerSpecificMeasuredCodeSearch.run model fuel predicate lo mid
        else PlayerSpecificMeasuredCodeSearch.run model fuel predicate succMid hi
      have hmlo : lo≤mid := by dsimp only [mid]; omega
      have hmhi : mid<hi := by dsimp only [mid]; omega
      have hmidC : mid≤C := by omega
      have hsucc : succMid≤hi := by dsimp only [succMid]; omega
      have hnext : next.2≤work model C fuel A := by
        dsimp only [next]
        split
        · exact ih lo mid hmlo (by omega) (by omega)
        · exact ih succMid hi hsucc hhi (by omega)
      have hnextCode : next.1.1≤C+1 := by
        dsimp only [next]
        split
        · exact (PlayerSpecificMeasuredCodeSearch.range model fuel predicate lo mid hmlo).2.trans (by omega)
        · exact (PlayerSpecificMeasuredCodeSearch.range model fuel predicate succMid hi hsucc).2.trans hhi
      have hnextVisits : next.1.2≤fuel := by
        dsimp only [next]
        split <;> exact PlayerSpecificMeasuredCodeSearch.visits model fuel predicate _ _
      have hmidCost := PlayerSpecificNaturalExecution.binary_cost model
        (fun a b=>a+(b-a)/2) lo hi W
        (word_width C lo (by omega)) (word_width C hi (by omega))
        (by change 1+binaryWordWidth mid≤W; exact word_width C mid (by omega))
      have hsuccCost := PlayerSpecificNaturalExecution.binary_cost model
        (fun a b=>a+b) mid 1 W
        (word_width C mid (by omega)) (word_width C 1 (by omega))
        (by change 1+binaryWordWidth succMid≤W; exact word_width C succMid (by omega))
      have hp := hpredicate mid hmidC
      have hp' : tested.2≤A := by simpa only [tested] using hp
      have hw : ∀ word∈[fuel,lo,hi,mid,succMid,next.1.1,next.1.2],binaryWordWidth word≤W := by
        intro word hword
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hword
        rcases hword with hw|hw|hw|hw|hw|hw|hw
        · simpa only [hw] using wordBound fuel (by omega)
        · simpa only [hw] using wordBound lo (by omega)
        · simpa only [hw] using wordBound hi (by omega)
        · simpa only [hw] using wordBound mid (by omega)
        · simpa only [hw] using wordBound succMid (by omega)
        · simpa only [hw] using wordBound next.1.1 (by omega)
        · simpa only [hw] using wordBound next.1.2 (by omega)
      have hcontrol := PlayerSpecificAlgebraicCallerFrame.controls_cost model
        [fuel,lo,hi,mid,succMid,next.1.1,next.1.2] W hw hW
      have hcontrol' : price model [.control fuel,.control lo,.control hi,
          .control mid,.control succMid,.control next.1.1,.control next.1.2]≤21*R := by
        change price model ([fuel,lo,hi,mid,succMid,next.1.1,next.1.2].map Event.control)≤_
        simpa only [List.map_cons,List.map_nil,List.length_cons,List.length_nil,
          Nat.reduceAdd,Nat.reduceMul] using hcontrol
      have hstep : (PlayerSpecificNaturalExecution.binary model (fun a b=>a+(b-a)/2) lo hi).2+
          (PlayerSpecificNaturalExecution.binary model (fun a b=>a+b) mid 1).2+
          tested.2+price model [.control fuel,.control lo,.control hi,
            .control mid,.control succMid,.control next.1.1,.control next.1.2]≤A+150*R := by
        omega
      simp only [PlayerSpecificMeasuredCodeSearch.run,h,ite_true,
        PlayerSpecificNaturalExecution.binary_value]
      change (PlayerSpecificNaturalExecution.binary model (fun a b=>a+(b-a)/2) lo hi).2+
        (PlayerSpecificNaturalExecution.binary model (fun a b=>a+b) mid 1).2+
        tested.2+next.2+price model [.control fuel,.control lo,.control hi,
          .control mid,.control succMid,.control next.1.1,.control next.1.2]≤_
      change _≤(fuel+1)*(A+150*R)+9*R
      change next.2≤fuel*(A+150*R)+9*R at hnext
      rw [Nat.succ_mul]
      omega
    · have hw : ∀ word∈[fuel,lo,hi],binaryWordWidth word≤W := by
        intro word hword
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hword
        rcases hword with hw|hw|hw
        · simpa only [hw] using wordBound fuel (by omega)
        · simpa only [hw] using wordBound lo (by omega)
        · simpa only [hw] using wordBound hi (by omega)
      have hc:=PlayerSpecificAlgebraicCallerFrame.controls_cost model [fuel,lo,hi] W hw hW
      have hc' : price model [.control fuel,.control lo,.control hi]≤9*R := by
        change price model ([fuel,lo,hi].map Event.control)≤_
        simpa only [List.map_cons,List.map_nil,List.length_cons,List.length_nil,
          Nat.reduceAdd,Nat.reduceMul] using hc
      simp only [PlayerSpecificMeasuredCodeSearch.run,h,ite_false]
      change price model [.control fuel,.control lo,.control hi]≤_
      have htail : 9*R≤work model C (fuel+1) A := by
        dsimp only [work,R,W]
        omega
      exact hc'.trans htail

end Blotto.PlayerSpecificMeasuredCodeSearchCost

import Blotto.PlayerSpecificFiniteDrawMeasuredSourceCost

/-! A priced lower-bound search evaluates exactly one measured predicate
per visited node and recurses only through its selected half interval.
Natural midpoint and successor arithmetic, controls, and return words are
included. Its first projection is the existing native code search. -/
namespace Blotto.PlayerSpecificMeasuredCodeSearch
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) :
    ℕ → (ℕ → Bool×ℕ) → ℕ → ℕ → (ℕ×ℕ)×ℕ
  | 0, _, lo, hi =>
      ((lo,0),price model [.control lo,.control hi,.control 0])
  | fuel+1, predicate, lo, hi =>
      if lo<hi then
        let midpoint:=PlayerSpecificNaturalExecution.binary model
          (fun a b => a+(b-a)/2) lo hi
        let successor:=PlayerSpecificNaturalExecution.binary model
          (fun a b => a+b) midpoint.1 1
        let tested:=predicate midpoint.1
        let next:=if tested.1 then run model fuel predicate lo midpoint.1
          else run model fuel predicate successor.1 hi
        ((next.1.1,next.1.2+1),midpoint.2+successor.2+tested.2+next.2+
          price model [.control fuel,.control lo,.control hi,
            .control midpoint.1,.control successor.1,.control next.1.1,.control next.1.2])
      else ((lo,0),price model [.control fuel,.control lo,.control hi])

theorem value (model : RationalCostModel) (fuel : ℕ) (predicate : ℕ → Bool×ℕ)
    (lo hi : ℕ) :
    (run model fuel predicate lo hi).1 =
      MonotoneCodeSearch.search fuel (fun code => (predicate code).1) lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,MonotoneCodeSearch.search]
    by_cases h : lo<hi
    · simp only [h,ite_true,PlayerSpecificNaturalExecution.binary_value]
      by_cases hp : (predicate (lo+(hi-lo)/2)).1
      · simp only [hp,ite_true,ih]
      · simp only [hp,Bool.false_eq_true,ite_false,ih]
    · simp only [h,ite_false]

theorem visits (model : RationalCostModel) (fuel : ℕ) (predicate : ℕ → Bool×ℕ)
    (lo hi : ℕ) : (run model fuel predicate lo hi).1.2≤fuel := by
  rw [value]
  exact MonotoneCodeSearch.search_visits fuel (fun code => (predicate code).1) lo hi

theorem range (model : RationalCostModel) (fuel : ℕ) (predicate : ℕ → Bool×ℕ)
    (lo hi : ℕ) (hlo : lo≤hi) :
    lo≤(run model fuel predicate lo hi).1.1 ∧
      (run model fuel predicate lo hi).1.1≤hi := by
  induction fuel generalizing lo hi with
  | zero => simp only [run]; exact ⟨le_rfl,hlo⟩
  | succ fuel ih =>
    by_cases h : lo<hi
    · let mid:=lo+(hi-lo)/2
      have hmlo : lo≤mid := by dsimp only [mid]; omega
      have hmhi : mid<hi := by dsimp only [mid]; omega
      simp only [run,h,ite_true,PlayerSpecificNaturalExecution.binary_value]
      by_cases hp : (predicate mid).1
      · simp only [mid,hp,ite_true]
        have ht:=ih lo mid hmlo
        exact ⟨ht.1,ht.2.trans hmhi.le⟩
      · simp only [mid,hp,Bool.false_eq_true,ite_false]
        have ht:=ih (mid+1) hi (by omega)
        exact ⟨(hmlo.trans (Nat.le_succ mid)).trans ht.1,ht.2⟩
    · simp only [run,h,ite_false]
      exact ⟨le_rfl,hlo⟩

end Blotto.PlayerSpecificMeasuredCodeSearch

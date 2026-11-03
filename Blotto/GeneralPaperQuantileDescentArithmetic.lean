import Blotto.GeneralPaperQuantileDescentControls

/-! Complete unit arithmetic descent, including control and return prices.
The bound is uniform in the data values; the implementation still follows
the actual selected branch and only calls the right mass on that branch.
-/
namespace Blotto.GeneralPaperQuantileDescentArithmetic
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperQuantileDescentExecution GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem finish_work (bit : Bool) (child : GeneralPaperQuantileDescent.Result)
    (s : GeneralPaperQuantileStepPrice.Step) (rightWork : ℕ) :
    (finish (fun _ => 1) 1 bit child s rightWork).2=140 := by rfl

theorem advance_work (height ancestor level : ℕ) : advance (fun _ => 1) 1 height ancestor level=134 := by rfl

theorem work (m lambda k Qv digits j : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (total : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number) :
    (run false (fun _ => 1) 1 c digits j total height node ancestor storedMass storedPrefix).2≤
      8388608*(height+1)*(measure m lambda k Qv+1)^2 := by
  let M := measure m lambda k Qv
  induction height generalizing ancestor storedMass storedPrefix with
  | zero =>
    change 64+1≤8388608*(0+1)*(M+1)^2
    nlinarith only [Nat.zero_le M]
  | succ height ih =>
    let s := step false (fun _ => 1) 1 c digits j ancestor node total storedMass storedPrefix
    have hs := GeneralPaperQuantileStepPrice.arithmetic_work m lambda k Qv digits j ancestor c hc hDigits node total storedMass storedPrefix
    change s.2≤4194304*(M+1)^2 at hs
    rw [run]
    dsimp only
    split
    · rw [finish_work,advance_work]
      have hi := ih (leftChild node) (ancestor+offset node) s.1.left.number storedPrefix
      change s.2+134+_+140≤8388608*(height+1+1)*(M+1)^2
      nlinarith only [hs,hi,Nat.zero_le M]
    · let r := right false (fun _ => 1) 1 c ancestor node storedMass
      rw [finish_work,advance_work]
      have hr := GeneralPaperQuantileChildPrice.arithmetic_work true m lambda k Qv c hc ancestor node storedMass
      change r.2≤2097152*(M+1)^2 at hr
      have hi := ih (rightChild node) (ancestor+offset node) r.1.number s.1.through.number
      change s.2+134+r.2+_+140≤8388608*(height+1+1)*(M+1)^2
      nlinarith only [hs,hr,hi,Nat.zero_le M]

end Blotto.GeneralPaperQuantileDescentArithmetic

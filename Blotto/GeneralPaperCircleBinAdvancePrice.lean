import Blotto.GeneralPaperCircleBinAdvance

/-! Literal operand/result-write bit prices for the bin cursor. Only
reached advances are charged. The magnitude cap below is an erased proof
bound, not a native input or capacity oracle. -/
namespace Blotto.GeneralPaperCircleBinAdvancePrice
open GeneralPaperCircleBinAdvance
set_option autoImplicit false
set_option maxHeartbeats 3500000

def copies (price : ℕ → ℕ) (a next : ℕ) : ℕ :=
  price (GeneralPaperNaturalPrimitivePrice.word a)+price (GeneralPaperNaturalPrimitivePrice.word next)+
    price (GeneralPaperNaturalPrimitivePrice.word 0)+price (GeneralPaperNaturalPrimitivePrice.word 4)

def extra (price : ℕ → ℕ) (width fuel a next : ℕ) (child : Result) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) a 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) next width+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) (fuel+1) 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) child.advances 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) child.work 12

def run (price : ℕ → ℕ) (W width position : ℕ) : ℕ → ℕ → ℕ → Result × ℕ
  | 0,a,next => (⟨a,next,0,4⟩,16*W+copies price a next)
  | fuel+1,a,next =>
    let test := GeneralPaperIntegerWordPrice.compare price next position
    if next<position then
      let child := run price W width position fuel (a+1) (next+width)
      (⟨child.1.bin,child.1.next,child.1.advances+1,child.1.work+12⟩,
        child.2+test+extra price width fuel a next child.1+64*W)
    else (⟨a,next,0,4⟩,32*W+test+copies price a next)

theorem data (price : ℕ → ℕ) (W width position fuel a next : ℕ) :
    (run price W width position fuel a next).1=GeneralPaperCircleBinAdvance.run width position fuel a next := by
  induction fuel generalizing a next with
  | zero => rfl
  | succ fuel ih =>
    rw [run,GeneralPaperCircleBinAdvance.run]
    split
    · dsimp only
      rw [ih]
    · rfl

theorem bounded_work (price : ℕ → ℕ) (hMono : Monotone price) (W width position fuel a next M : ℕ)
    (hM : 16≤M) (hA : a+fuel+1≤M) (hNext : next+width*fuel≤M) (hPosition : position≤M)
    (hWidth : width≤M) (hCounter : 12*fuel+4≤M) :
    (run price W width position fuel a next).2≤
      ((run price W width position fuel a next).1.advances+1)*(128*W+32*price (1+binaryWordWidth M)) := by
  let P := price (1+binaryWordWidth M)
  have copy_le (b c : ℕ) (hb : b≤M) (hc : c≤M) : copies price b c≤4*P := by
    have bound (x : ℕ) (hx : x≤M) : price (GeneralPaperNaturalPrimitivePrice.word x)≤P :=
      hMono (Nat.add_le_add_left (binaryWordWidth_mono hx) 1)
    have h1 := bound b hb
    have h2 := bound c hc
    have h3 := bound 0 (Nat.zero_le _)
    have h4 := bound 4 (by omega)
    unfold copies
    omega
  induction fuel generalizing a next with
  | zero =>
    have hc := copy_le a next (by omega) (by simpa only [Nat.mul_zero,Nat.add_zero] using hNext)
    change 16*W+copies price a next≤(0+1)*(128*W+32*P)
    omega
  | succ fuel ih =>
    have hn : next≤M := by omega
    have hTest := GeneralPaperIntegerWordPrice.compare_le price hMono next position (1+binaryWordWidth M)
      (Nat.add_le_add_left (binaryWordWidth_mono hn) 1) (Nat.add_le_add_left (binaryWordWidth_mono hPosition) 1)
    change GeneralPaperIntegerWordPrice.compare price next position≤P at hTest
    by_cases hs:next<position
    · have hAn : a+1+fuel+1≤M := by omega
      have hNn : next+width+width*fuel≤M := by nlinarith only [hNext]
      have hCn : 12*fuel+4≤M := by omega
      have hi := ih (a+1) (next+width) hAn hNn hCn
      let child := (run price W width position fuel (a+1) (next+width)).1
      have hAdv : child.advances≤fuel := by
        dsimp only [child]
        rw [data]
        exact advances_le _ _ _ _ _
      have hWork : child.work=12*child.advances+4 := by
        dsimp only [child]
        rw [data]
        exact work_eq _ _ _ _ _
      have hb := GeneralPaperNaturalPrimitivePrice.binary_le price hMono
      have h1 := hb (fun a b => a+b) a 1 M (by omega) (by omega) (by omega)
      have h2 := hb (fun a b => a+b) next width M hn hWidth (by nlinarith only [hNext])
      have h3 := hb (fun a b => a-b) (fuel+1) 1 M (by omega) (by omega) (by omega)
      have h4 := hb (fun a b => a+b) child.advances 1 M (by omega) (by omega) (by omega)
      have h5 := hb (fun a b => a+b) child.work 12 M (by omega) (by omega) (by omega)
      have hExtra : extra price width fuel a next child≤10*P := by unfold extra;omega
      rw [run,ite_eq_left hs]
      dsimp only
      change (run price W width position fuel (a+1) (next+width)).2+
        GeneralPaperIntegerWordPrice.compare price next position+extra price width fuel a next child+64*W≤
          (child.advances+1+1)*(128*W+32*P)
      change (run price W width position fuel (a+1) (next+width)).2≤(child.advances+1)*(128*W+32*P) at hi
      nlinarith only [hi,hTest,hExtra]
    · have hc := copy_le a next (by omega) hn
      rw [run,ite_eq_right hs]
      change 32*W+GeneralPaperIntegerWordPrice.compare price next position+copies price a next≤(0+1)*(128*W+32*P)
      omega

end Blotto.GeneralPaperCircleBinAdvancePrice

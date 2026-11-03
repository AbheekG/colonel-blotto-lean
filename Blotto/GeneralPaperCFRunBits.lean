import Blotto.GeneralPaperCFAdvanceBits

/-! Full native CF loop with priced division, continuants, tests and loop
control. Summing native work differences retains the actual amortized
quotient-depth bound, instead of paying a full-width division at each step.
-/
namespace Blotto.GeneralPaperCFRunBits
open GeneralPaperRegularCFLoop GeneralPaperCFOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000

def run (primitive : ℕ → ℕ) (W D divisionFuel : ℕ) : ℕ → State → State × ℕ
  | 0,s => (s,16*W)
  | fuel+1,s =>
    let next := GeneralPaperCFAdvanceBits.advance primitive W D divisionFuel s
    if next.1.2 then
      let later := run primitive W D divisionFuel fuel next.1.1
      (later.1,next.2+later.2+24*W)
    else (next.1.1,next.2+24*W)

theorem data (primitive : ℕ → ℕ) (W D divisionFuel fuel : ℕ) (s : State) :
    (run primitive W D divisionFuel fuel s).1=GeneralPaperRegularCFLoop.run D divisionFuel fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [run,GeneralPaperRegularCFLoop.run]
    dsimp only
    rw [GeneralPaperCFAdvanceBits.data]
    split
    · dsimp only
      rw [ih]
    · rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D lambda fuel N M : ℕ)
    (s : State) (h : Valid lambda N M s) (hN : N<2^lambda) (hM : M<2^lambda) :
    let F := W+primitive (GeneralPaperCFOperandPrice.width lambda D)
    (run primitive W D (lambda+2) fuel s).2+4096*s.work*F≤
      4096*((GeneralPaperRegularCFLoop.run D (lambda+2) fuel s).work+1)*F := by
  let F := W+primitive (GeneralPaperCFOperandPrice.width lambda D)
  induction fuel generalizing s with
  | zero =>
    change 16*W+4096*s.work*F≤4096*(s.work+1)*F
    dsimp only [F]
    nlinarith
  | succ fuel ih =>
    have ha := GeneralPaperCFAdvanceBits.work primitive hMono W D lambda N M s h hN hM
    dsimp only at ha
    have hi := ih (GeneralPaperRegularCFLoop.advance D (lambda+2) s).1 (advance_valid D lambda N M s h)
    rw [run,GeneralPaperRegularCFLoop.run]
    dsimp only
    rw [GeneralPaperCFAdvanceBits.data]
    change _+4096*s.work*F≤_
    change (GeneralPaperCFAdvanceBits.advance primitive W D (lambda+2) s).2+32*W+4096*s.work*F≤
      4096*(GeneralPaperRegularCFLoop.advance D (lambda+2) s).1.work*F at ha
    split
    · dsimp only
      change (GeneralPaperCFAdvanceBits.advance primitive W D (lambda+2) s).2+
        (run primitive W D (lambda+2) fuel (GeneralPaperRegularCFLoop.advance D (lambda+2) s).1).2+
        24*W+4096*s.work*F≤4096*((GeneralPaperRegularCFLoop.run D (lambda+2) fuel
          (GeneralPaperRegularCFLoop.advance D (lambda+2) s).1).work+1)*F
      change (run primitive W D (lambda+2) fuel (GeneralPaperRegularCFLoop.advance D (lambda+2) s).1).2+
        4096*(GeneralPaperRegularCFLoop.advance D (lambda+2) s).1.work*F≤
        4096*((GeneralPaperRegularCFLoop.run D (lambda+2) fuel (GeneralPaperRegularCFLoop.advance D (lambda+2) s).1).work+1)*F at hi
      omega
    · change (GeneralPaperCFAdvanceBits.advance primitive W D (lambda+2) s).2+24*W+4096*s.work*F≤
        4096*((GeneralPaperRegularCFLoop.advance D (lambda+2) s).1.work+1)*F
      nlinarith only [ha]

end Blotto.GeneralPaperCFRunBits

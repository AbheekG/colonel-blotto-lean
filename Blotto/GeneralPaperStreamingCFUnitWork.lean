import Blotto.GeneralPaperStreamingPreparedClassifier

/-! Unit source-operation budgets for the same streaming data program.
Fixed per-step allowances include arithmetic, guards and register writes.
They are independent of bit encodings and the analytical bit-price fields.
Amortizing the actual quotient depths retains O(lambda) real-RAM work.
-/
namespace Blotto.GeneralPaperStreamingCFUnitWork
open GeneralPaperRegularCFLoop GeneralPaperQuotientTraversal
set_option autoImplicit false
set_option maxHeartbeats 8000000

def upCost (n scale : ℕ) : ℕ → ℕ
  | 0 => 8
  | fuel+1 => if n<scale then 8 else upCost n (2*scale) fuel+16

theorem up_work (n a fuel : ℕ) :
    upCost n a fuel≤16*((GeneralPaperNaturalGrowingQuotient.run n a fuel).depth+1) := by
  induction fuel generalizing a with
  | zero => change 8≤16*(0+1); omega
  | succ fuel ih =>
    rw [upCost,GeneralPaperNaturalGrowingQuotient.run]
    split
    · change 8≤16*(0+1); omega
    · have hh := ih (2*a)
      dsimp only
      split <;> dsimp only <;> omega

def downCost (scale : ℕ) : ℕ → (ℕ × ℕ) → ℕ
  | 0,_ => 8
  | remaining+1,qr =>
    let smaller := scale/2
    downCost smaller remaining (restore smaller qr)+24

theorem down_work (scale remaining : ℕ) (qr : ℕ × ℕ) : downCost scale remaining qr=24*remaining+8 := by
  induction remaining generalizing scale qr with
  | zero => rfl
  | succ remaining ih => rw [downCost,ih]; omega

def divisionCost (n a fuel : ℕ) : ℕ :=
  let top := up n a fuel 0
  upCost n a fuel+downCost top.scale top.depth (0,n)+64

theorem division_work (n a fuel : ℕ) :
    divisionCost n a fuel≤128*((GeneralPaperConstructedNatDivision.run n a fuel).depth+1) := by
  have hu := up_work n a fuel
  have hd := down_work (up n a fuel 0).scale (up n a fuel 0).depth (0,n)
  have ht := (up_data n a fuel 0).2
  have he := congrArg GeneralPaperGrowingQuotient.Result.depth (GeneralPaperNaturalGrowingQuotient.data n a fuel)
  change (GeneralPaperNaturalGrowingQuotient.run n a fuel).depth=(GeneralPaperConstructedNatDivision.run n a fuel).depth at he
  change (up n a fuel 0).depth=0+(GeneralPaperNaturalGrowingQuotient.run n a fuel).depth at ht
  unfold divisionCost
  dsimp only
  omega

def advanceCost (divisionFuel : ℕ) (s : State) : ℕ :=
  if s.denominator=0 then 64 else divisionCost s.numerator s.denominator divisionFuel+128

theorem advance_work (D divisionFuel : ℕ) (s : State) :
    advanceCost divisionFuel s+32+4096*s.work≤
      4096*(GeneralPaperRegularCFLoop.advance D divisionFuel s).1.work := by
  by_cases hz : s.denominator=0
  · rw [advanceCost,ite_eq_left hz,GeneralPaperRegularCFLoop.advance,ite_eq_left hz]
    dsimp only
    omega
  · have hd := division_work s.numerator s.denominator divisionFuel
    have hw := GeneralPaperConstructedNatDivision.work_depth s.numerator s.denominator divisionFuel
    rw [advanceCost,ite_eq_right hz,GeneralPaperCFAdvanceBits.native_work D divisionFuel s hz,hw]
    omega

def loopCost (D divisionFuel : ℕ) : ℕ → State → ℕ
  | 0,_ => 16
  | fuel+1,s =>
    let next := GeneralPaperStreamingCFRegisters.advance D divisionFuel s
    advanceCost divisionFuel s+24+
      if next.2 then loopCost D divisionFuel fuel next.1 else 0

theorem loop_work (D divisionFuel fuel : ℕ) (s : State) :
    loopCost D divisionFuel fuel s+4096*s.work≤4096*((run D divisionFuel fuel s).work+1) := by
  induction fuel generalizing s with
  | zero => change 16+4096*s.work≤4096*(s.work+1); omega
  | succ fuel ih =>
    have ha := advance_work D divisionFuel s
    have hi := ih (GeneralPaperRegularCFLoop.advance D divisionFuel s).1
    rw [loopCost,GeneralPaperStreamingCFRegisters.advance_data,run]
    split
    · omega
    · omega

def queryCost (D C t lambda : ℕ) : ℕ :=
  loopCost D (lambda+2) (2*lambda+4) (initial C t)+128

theorem query_work (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    queryCost D C t lambda≤1048576*(lambda+3) := by
  have hw := loop_work D (lambda+2) (2*lambda+4) (initial C t)
  have hb := GeneralPaperCFPrefixCounters.prefix_bounds D C t lambda (2*lambda+4) hD hC ht hPower (by omega)
  have hbWork := hb.2.2.2
  change (run D (lambda+2) (2*lambda+4) (initial C t)).work≤170*lambda+338 at hbWork
  change loopCost D (lambda+2) (2*lambda+4) (initial C t)+4096*0≤_ at hw
  unfold queryCost
  omega

end Blotto.GeneralPaperStreamingCFUnitWork

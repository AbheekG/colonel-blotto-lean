import Blotto.GeneralPaperStreamingNatDivision

/-! Streamed adaptive division inside the actual CF advance, with its
complete operation ledger. Prices are analytical fields of the source model;
register-space reservations for the data program are established separately.
The entire native state, selected fraction and work annotation are preserved.
-/
namespace Blotto.GeneralPaperStreamingCFAdvance
open GeneralPaperRegularCFLoop GeneralPaperCFOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def finish (D : ℕ) (s : State) (divided : GeneralPaperConstructedNatDivision.Result) : State × Bool :=
  let numerator := divided.quotient*s.previousNum+s.olderNum
  let denominator := divided.quotient*s.previousDen+s.olderDen
  let charged : State := ⟨s.denominator,divided.remainder,s.previousNum,s.previousDen,numerator,denominator,
    s.selected,s.steps+1,s.quotientDepth+divided.depth,s.zeroChecks,s.work+divided.work+48⟩
  if hd : 0<denominator then
    if denominator≤D then ({charged with selected := some ⟨numerator,denominator,hd⟩},true)
    else (charged,false)
  else (charged,false)

theorem finish_work (D : ℕ) (s : State) (divided : GeneralPaperConstructedNatDivision.Result) :
    (finish D s divided).1.work=s.work+divided.work+48 := by
  unfold finish
  dsimp only
  split
  · split <;> rfl
  · rfl

def advance (model : RationalCostModel) (W D divisionFuel : ℕ) (s : State) : (State × Bool) × ℕ :=
  let test := GeneralPaperIntegerWordPrice.compare model.rat s.denominator 0
  if s.denominator=0 then
    (({s with zeroChecks := s.zeroChecks+1,work := s.work+12},false),64*W+test)
  else
    let divided := GeneralPaperStreamingNatDivision.priced model W s.numerator s.denominator divisionFuel
    (finish D s divided.1,divided.2+128*W+test+
      GeneralPaperCFOperandPrice.rawWork model.rat divided.1.quotient s+
      GeneralPaperCFOperandPrice.checks model.rat D (divided.1.quotient*s.previousDen+s.olderDen))

theorem data (model : RationalCostModel) (W D divisionFuel : ℕ) (s : State) :
    (advance model W D divisionFuel s).1=GeneralPaperRegularCFLoop.advance D divisionFuel s := by
  rw [advance,GeneralPaperRegularCFLoop.advance]
  split
  · rfl
  · dsimp only
    rw [GeneralPaperStreamingNatDivision.priced_data]
    rfl

theorem native_work (D divisionFuel : ℕ) (s : State) (hd : s.denominator≠0) :
    (GeneralPaperRegularCFLoop.advance D divisionFuel s).1.work=
      s.work+(GeneralPaperConstructedNatDivision.run s.numerator s.denominator divisionFuel).work+48 := by
  change (if s.denominator=0 then _ else finish D s (GeneralPaperConstructedNatDivision.run s.numerator s.denominator divisionFuel)).1.work=_
  rw [ite_eq_right hd,finish_work]

theorem work (model : RationalCostModel) (W D lambda N M : ℕ)
    (s : State) (h : Valid lambda N M s) (hN : N<2^lambda) (hM : M<2^lambda) :
    let F := W+model.rat (GeneralPaperCFOperandPrice.width lambda D)
    (advance model W D (lambda+2) s).2+32*W+4096*s.work*F≤
      4096*(GeneralPaperRegularCFLoop.advance D (lambda+2) s).1.work*F := by
  let P := model.rat (GeneralPaperCFOperandPrice.width lambda D)
  let F := W+P
  have ht := GeneralPaperCFOperandPrice.zero_work model.rat model.monotone lambda D s h.pair
  by_cases hz : s.denominator=0
  · rw [advance,ite_eq_left hz,GeneralPaperRegularCFLoop.advance,ite_eq_left hz]
    dsimp only
    change 64*W+GeneralPaperIntegerWordPrice.compare model.rat s.denominator 0+32*W+4096*s.work*F≤4096*(s.work+12)*F
    change GeneralPaperIntegerWordPrice.compare model.rat s.denominator 0≤P at ht
    dsimp only [F]
    nlinarith only [ht]
  · have hd : 0<s.denominator := by omega
    have hc := GeneralPaperStreamingNatDivision.priced_work model W s.numerator s.denominator (lambda+2) hd
    have hWidth : GeneralPaperQuotientRegisterSpace.operandWord s.numerator s.denominator≤GeneralPaperCFOperandPrice.width lambda D :=
      (GeneralPaperGrowingQuotientBits.magnitude_width s.numerator s.denominator).trans
        (GeneralPaperCFOperandPrice.division_width lambda D s h.pair)
    have hPrice := model.monotone hWidth
    have hdCost := hc.trans (Nat.mul_le_mul_left
      (1024*((GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).depth+1)) (Nat.add_le_add_left hPrice W))
    have hr := GeneralPaperCFOperandPrice.raw_work model.rat model.monotone D lambda N M s h hN hM hd
    have hp := raw_products D lambda N M s h hd
    have hChecks := GeneralPaperCFOperandPrice.checks_work model.rat model.monotone lambda D
      ((GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).quotient*s.previousDen+s.olderDen)
      (hp.2.2.2.2.trans_lt hM)
    have hw := GeneralPaperConstructedNatDivision.work_depth s.numerator s.denominator (lambda+2)
    rw [native_work D (lambda+2) s hz]
    rw [advance,ite_eq_right hz]
    dsimp only
    rw [GeneralPaperStreamingNatDivision.priced_data]
    change (GeneralPaperStreamingNatDivision.priced model W s.numerator s.denominator (lambda+2)).2+128*W+
      GeneralPaperIntegerWordPrice.compare model.rat s.denominator 0+
      GeneralPaperCFOperandPrice.rawWork model.rat (GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).quotient s+
      GeneralPaperCFOperandPrice.checks model.rat D
        ((GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).quotient*s.previousDen+s.olderDen)+
      32*W+4096*s.work*F≤4096*(s.work+(GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).work+48)*F
    change _≤1024*((GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).depth+1)*F at hdCost
    change _≤8*P at hr
    change _≤2*P at hChecks
    change _≤P at ht
    rw [hw]
    have hWF : W≤F := Nat.le_add_right _ _
    have hPF : P≤F := Nat.le_add_left _ _
    nlinarith only [hdCost,hr,hChecks,ht,hWF,hPF,
      Nat.zero_le ((GeneralPaperConstructedNatDivision.run s.numerator s.denominator (lambda+2)).depth*F)]

end Blotto.GeneralPaperStreamingCFAdvance

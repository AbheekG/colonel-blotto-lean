import Blotto.GeneralPaperStreamingCFRegisters

/-! Simultaneous CF source-register space. One current and one replacement
state, the retained fraction, the streamed division phases/result and all
raw arithmetic scratch are reserved. Primitive scratch is bounded by its
bit-operation allowance under the paper convention. The peak is a ghost
maximum, not a stored history or a compiler/allocator-space claim.
-/
namespace Blotto.GeneralPaperStreamingCFSpace
open GeneralPaperRegularCFLoop GeneralPaperCFOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000

def selectedFootprint (W : ℕ) : Option Farey.Fraction → ℕ
  | none => W
  | some f => binaryWordWidth f.num+binaryWordWidth f.den+W

def footprint (W : ℕ) (s : State) : ℕ :=
  binaryWordWidth s.numerator+binaryWordWidth s.denominator+
  binaryWordWidth s.olderNum+binaryWordWidth s.olderDen+
  binaryWordWidth s.previousNum+binaryWordWidth s.previousDen+
  selectedFootprint W s.selected+binaryWordWidth s.steps+
  binaryWordWidth s.quotientDepth+binaryWordWidth s.zeroChecks+binaryWordWidth s.work+16*W

structure Small (W : ℕ) (s : State) : Prop where
  steps : binaryWordWidth s.steps≤W
  depth : binaryWordWidth s.quotientDepth≤W
  zeros : binaryWordWidth s.zeroChecks≤W
  work : binaryWordWidth s.work≤W

theorem state_space (W lambda N M : ℕ) (s : State) (h : Valid lambda N M s)
    (hN : N<2^lambda) (hM : M<2^lambda) (hc : Small W s) :
    footprint W s≤8*(lambda+1)+21*W := by
  have hp := previous lambda N M s h
  have hn := GeneralPaperCFOperandPrice.small_word lambda s.numerator h.pair.1
  have hd := GeneralPaperCFOperandPrice.small_word lambda s.denominator h.pair.2
  have hon := GeneralPaperCFOperandPrice.small_word lambda s.olderNum (h.olderNum.trans_lt hN)
  have hod := GeneralPaperCFOperandPrice.small_word lambda s.olderDen (h.olderDen.trans_lt hM)
  have hpn := GeneralPaperCFOperandPrice.small_word lambda s.previousNum (hp.1.trans_lt hN)
  have hpd := GeneralPaperCFOperandPrice.small_word lambda s.previousDen (hp.2.trans_lt hM)
  have hs : selectedFootprint W s.selected≤2*(lambda+1)+W := by
    cases he : s.selected with
    | none => simp only [selectedFootprint]; omega
    | some f =>
      have hf := h.selected f he
      have hfn := GeneralPaperCFOperandPrice.small_word lambda f.num (hf.1.trans_lt hN)
      have hfd := GeneralPaperCFOperandPrice.small_word lambda f.den (hf.2.trans_lt hM)
      simp only [selectedFootprint]
      omega
  have hcs := hc.steps
  have hcd := hc.depth
  have hcz := hc.zeros
  have hcw := hc.work
  unfold footprint
  omega

theorem prefix_small (W D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hPower : 8*C=2^lambda) (hFuel : fuel≤2*lambda+4) (hW : GeneralPaperCFControlWords.width lambda≤W) :
    Small W (run D (lambda+2) fuel (initial C t)) := by
  let s := run D (lambda+2) fuel (initial C t)
  have hb := GeneralPaperCFControlWords.prefix_words D C t lambda fuel hD hC ht hPower hFuel
  have hs := binaryWordWidth_mono (Nat.le_add_right s.steps 1)
  have hd := binaryWordWidth_mono (show s.quotientDepth≤s.quotientDepth+lambda+2 by omega)
  have hz := binaryWordWidth_mono (Nat.le_add_right s.zeroChecks 1)
  have hw := binaryWordWidth_mono (Nat.le_add_right s.work 512)
  change Small W s
  change binaryWordWidth (s.steps+1)≤_ ∧ binaryWordWidth (s.quotientDepth+lambda+2)≤_ ∧
    binaryWordWidth (s.zeroChecks+1)≤_ ∧ binaryWordWidth (s.work+512)≤_ at hb
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem advanced_small (W D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hPower : 8*C=2^lambda) (hFuel : fuel≤2*lambda+4) (hW : GeneralPaperCFControlWords.width lambda≤W) :
    Small W (GeneralPaperRegularCFLoop.advance D (lambda+2) (run D (lambda+2) fuel (initial C t))).1 := by
  let s := (GeneralPaperRegularCFLoop.advance D (lambda+2) (run D (lambda+2) fuel (initial C t))).1
  have hb := GeneralPaperCFControlWords.returned_advance D C t lambda fuel hD hC ht hPower hFuel
  have hs := binaryWordWidth_mono (Nat.le_add_right s.steps 1)
  have hd := binaryWordWidth_mono (Nat.le_add_right s.quotientDepth 1)
  have hz := binaryWordWidth_mono (Nat.le_add_right s.zeroChecks 1)
  have hw := binaryWordWidth_mono (Nat.le_add_right s.work 64)
  change Small W s
  change binaryWordWidth (s.steps+1)≤_ ∧ binaryWordWidth (s.quotientDepth+1)≤_ ∧
    binaryWordWidth (s.zeroChecks+1)≤_ ∧ binaryWordWidth (s.work+64)≤_ at hb
  refine ⟨?_,?_,?_,?_⟩ <;> omega

def advanceWindow (model : RationalCostModel) (W D lambda : ℕ) (s : State) : ℕ :=
  footprint W s+footprint W (GeneralPaperStreamingCFRegisters.advance D (lambda+2) s).1+64*W+
  GeneralPaperIntegerWordPrice.compare model.rat s.denominator 0+
  if s.denominator=0 then 0 else
    GeneralPaperQuotientPhaseSpace.reservation model W s.numerator s.denominator+
    GeneralPaperStreamingNatDivision.footprint W (GeneralPaperStreamingNatDivision.run s.numerator s.denominator (lambda+2))+16*W+
    GeneralPaperCFOperandPrice.rawWork model.rat
      (GeneralPaperStreamingNatDivision.run s.numerator s.denominator (lambda+2)).quotient s+
    GeneralPaperCFOperandPrice.checks model.rat D
      ((GeneralPaperStreamingNatDivision.run s.numerator s.denominator (lambda+2)).quotient*s.previousDen+s.olderDen)

theorem next_in_window (model : RationalCostModel) (W D lambda : ℕ) (s : State) :
    footprint W (GeneralPaperStreamingCFRegisters.advance D (lambda+2) s).1≤advanceWindow model W D lambda s := by
  unfold advanceWindow
  omega

theorem advance_space (model : RationalCostModel) (W D lambda N M : ℕ) (s : State)
    (h : Valid lambda N M s) (hN : N<2^lambda) (hM : M<2^lambda)
    (hc : Small W s) (hn : Small W (GeneralPaperRegularCFLoop.advance D (lambda+2) s).1)
    (hW : GeneralPaperCFControlWords.width lambda≤W) :
    advanceWindow model W D lambda s≤512*(W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  let L := GeneralPaperCFOperandPrice.width lambda D
  let P := model.rat L
  have h0 := state_space W lambda N M s h hN hM hc
  have h1 := state_space W lambda N M _ (advance_valid D lambda N M s h) hN hM hn
  have hP : lambda+1≤P := (show lambda+1≤L by dsimp [L,GeneralPaperCFOperandPrice.width]; omega).trans (model.word_le L)
  have ht := GeneralPaperCFOperandPrice.zero_work model.rat model.monotone lambda D s h.pair
  change _≤P at ht
  unfold advanceWindow
  rw [GeneralPaperStreamingCFRegisters.advance_data]
  change _≤512*(W+P)
  split
  · omega
  · rename_i hd
    have hDivision := GeneralPaperStreamingNatDivision.reservation model W s.numerator s.denominator (lambda+2)
      (by omega) (GeneralPaperStreamingDivisionSpace.counter_word lambda (lambda+2) (by omega) |>.trans hW)
    have hWidth : GeneralPaperQuotientRegisterSpace.operandWord s.numerator s.denominator≤L :=
      (GeneralPaperGrowingQuotientBits.magnitude_width s.numerator s.denominator).trans
        (GeneralPaperCFOperandPrice.division_width lambda D s h.pair)
    have hDiv := hDivision.trans (Nat.mul_le_mul_left 256 (Nat.add_le_add_left (model.monotone hWidth) W))
    have hr := GeneralPaperCFOperandPrice.raw_work model.rat model.monotone D lambda N M s h hN hM (by omega)
    have hp := raw_products D lambda N M s h (by omega)
    have hChecks := GeneralPaperCFOperandPrice.checks_work model.rat model.monotone lambda D _ (hp.2.2.2.2.trans_lt hM)
    rw [GeneralPaperStreamingNatDivision.data]
    change _≤256*(W+P) at hDiv
    rw [GeneralPaperStreamingNatDivision.data] at hDiv
    change _≤8*P at hr
    change _≤2*P at hChecks
    omega

theorem reached_state (W D C t lambda : ℕ) (c : GeneralPaperStreamingCFRegisters.Configuration)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda)
    (hW : GeneralPaperCFControlWords.width lambda≤W)
    (hr : GeneralPaperStreamingCFRegisters.Reach D (lambda+2) (2*lambda+4) (initial C t) c) :
    footprint W c.state≤8*(lambda+1)+21*W := by
  obtain ⟨n,hn,hs⟩ := GeneralPaperStreamingCFRegisters.reached_prefix D (lambda+2) (2*lambda+4) (initial C t) c hr
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  rw [hs]
  exact state_space W lambda (2*t+1) (2*C) _
    (midpoint_all_prefixes D C t lambda n hC ht hPower) hp.1 hp.2
    (prefix_small W D C t lambda n hD hC ht hPower (by omega) hW)

theorem reached_window (model : RationalCostModel) (W D C t lambda : ℕ) (c : GeneralPaperStreamingCFRegisters.Configuration)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda)
    (hW : GeneralPaperCFControlWords.width lambda≤W)
    (hr : GeneralPaperStreamingCFRegisters.Reach D (lambda+2) (2*lambda+4) (initial C t) c) :
    advanceWindow model W D lambda c.state≤512*(W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  obtain ⟨n,hn,hs⟩ := GeneralPaperStreamingCFRegisters.reached_prefix D (lambda+2) (2*lambda+4) (initial C t) c hr
  have hp := GeneralPaperRegularCFFuel.midpoint_pair_bound C t lambda hC ht hPower
  rw [hs]
  exact advance_space model W D lambda (2*t+1) (2*C) _
    (midpoint_all_prefixes D C t lambda n hC ht hPower) hp.1 hp.2
    (prefix_small W D C t lambda n hD hC ht hPower (by omega) hW)
    (advanced_small W D C t lambda n hD hC ht hPower (by omega) hW) hW

def peak (model : RationalCostModel) (W D lambda : ℕ) : ℕ → State → ℕ
  | 0,s => footprint W s
  | fuel+1,s =>
    let next := GeneralPaperStreamingCFRegisters.advance D (lambda+2) s
    max (advanceWindow model W D lambda s)
      (if next.2 then peak model W D lambda fuel next.1 else footprint W next.1)

theorem peak_bound (model : RationalCostModel) (W D C t lambda : ℕ)
    (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda)
    (hW : GeneralPaperCFControlWords.width lambda≤W) (c : GeneralPaperStreamingCFRegisters.Configuration)
    (hr : GeneralPaperStreamingCFRegisters.Reach D (lambda+2) (2*lambda+4) (initial C t) c) :
    peak model W D lambda c.remaining c.state≤512*(W+model.rat (GeneralPaperCFOperandPrice.width lambda D)) := by
  obtain ⟨fuel,s⟩ := c
  induction fuel generalizing s with
  | zero =>
    have hs := reached_state W D C t lambda ⟨0,s⟩ hD hC ht hPower hW hr
    have hP : lambda+1≤model.rat (GeneralPaperCFOperandPrice.width lambda D) :=
      (show lambda+1≤GeneralPaperCFOperandPrice.width lambda D by unfold GeneralPaperCFOperandPrice.width; omega).trans
        (model.word_le (GeneralPaperCFOperandPrice.width lambda D))
    change footprint W s≤8*(lambda+1)+21*W at hs
    change footprint W s≤_
    omega
  | succ fuel ih =>
    have hw := reached_window model W D C t lambda ⟨fuel+1,s⟩ hD hC ht hPower hW hr
    rw [peak]
    dsimp only
    by_cases hb : (GeneralPaperStreamingCFRegisters.advance D (lambda+2) s).2=true
    · rw [ite_eq_left hb]
      have hStep : GeneralPaperStreamingCFRegisters.step D (lambda+2) ⟨fuel+1,s⟩=
          .inr ⟨fuel,(GeneralPaperStreamingCFRegisters.advance D (lambda+2) s).1⟩ := by
        simp only [GeneralPaperStreamingCFRegisters.step,ite_eq_left hb]
      exact max_le hw (ih _ (.more _ _ hr hStep))
    · rw [ite_eq_right hb]
      exact max_le hw ((next_in_window model W D lambda s).trans hw)

end Blotto.GeneralPaperStreamingCFSpace

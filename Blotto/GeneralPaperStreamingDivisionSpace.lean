import Blotto.GeneralPaperQuotientStoppedStates

/-! Calibrate the fixed-register quotient's operation and register-space
reservations at the actual CF word and operand sizes. These are primitive
division contracts; the whole CF-query replacement is a later join.
-/
namespace Blotto.GeneralPaperStreamingDivisionSpace
open GeneralPaperQuotientRegisters GeneralPaperQuotientRegisterBounds GeneralPaperQuotientRegisterSpace
open GeneralPaperQuotientPhaseSpace
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem counter_word (lambda fuel : ℕ) (hf : fuel≤lambda+2) :
    counterWord fuel≤GeneralPaperCFControlWords.width lambda := by
  have hF : fuel+1≤4*(lambda+1) := by omega
  have hm := binaryWordWidth_mono hF
  have hp := binaryWordWidth_mul 4 (lambda+1)
  have h4 : binaryWordWidth 4=3 := by decide
  unfold counterWord GeneralPaperCFControlWords.width
  omega

theorem operand_word (lambda n a : ℕ) (hn : n<2^lambda) (ha : a<2^lambda) :
    GeneralPaperQuotientRegisterSpace.operandWord n a≤32+8*lambda := by
  have hm := GeneralPaperGrowingQuotientBits.magnitude_width n a
  have hnW := GeneralPaperCFOperandPrice.small_word lambda n hn
  have haW := GeneralPaperCFOperandPrice.small_word lambda a ha
  change GeneralPaperQuotientRegisterSpace.operandWord n a≤GeneralPaperGrowingQuotientBits.width n a at hm
  unfold GeneralPaperGrowingQuotientBits.width at hm
  omega

theorem calibrated_counter (m k lambda fuel : ℕ) (h : GeneralPaperClassifierCFWords.QueryWidth m k lambda)
    (hf : fuel≤lambda+2) : counterWord fuel≤GeneralPaperPrecallControlWord.word m k :=
  (counter_word lambda fuel hf).trans (GeneralPaperClassifierCFWords.calibrated m k lambda h)

theorem reservation_bound (model : RationalCostModel) (W lambda n a : ℕ)
    (hn : n<2^lambda) (ha : a<2^lambda) :
    reservation model W n a≤128*(W+model.rat (32+8*lambda)) :=
  Nat.mul_le_mul_left 128 (Nat.add_le_add_left (model.monotone (operand_word lambda n a hn ha)) W)

theorem work_bound (model : RationalCostModel) (W lambda n a fuel : ℕ) (ha : 0<a)
    (hnW : n<2^lambda) (haW : a<2^lambda) :
    GeneralPaperStreamingQuotientWork.cost model W n a fuel≤
      512*((GeneralPaperConstructedNatDivision.run n a fuel).depth+1)*(W+model.rat (32+8*lambda)) := by
  have hw := GeneralPaperStreamingQuotientWork.work model W n a fuel ha
  have hd := congrArg GeneralPaperGrowingQuotient.Result.depth (GeneralPaperStreamingQuotient.rational_data n a fuel)
  change (GeneralPaperStreamingQuotient.run n a fuel).depth=(GeneralPaperConstructedNatDivision.run n a fuel).depth at hd
  rw [hd] at hw
  exact hw.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone (operand_word lambda n a hnW haW)) W))

theorem actual_up_window (model : RationalCostModel) (m k lambda n a fuel : ℕ)
    (h : GeneralPaperClassifierCFWords.QueryWidth m k lambda) (hf : fuel≤lambda+2)
    (ha : 0<a) (hnW : n<2^lambda) (haW : a<2^lambda) (s next : UpState)
    (hr : UpReach n a fuel s) (hs : upStep n s=some next) :
    upWindow model (GeneralPaperPrecallControlWord.word m k) n a s next+16*GeneralPaperPrecallControlWord.word m k≤
      128*(GeneralPaperPrecallControlWord.word m k+model.rat (32+8*lambda)) :=
  (reachable_up_window model _ n a fuel ha (calibrated_counter m k lambda fuel h hf) s next hr hs).trans
    (reservation_bound model _ lambda n a hnW haW)

theorem actual_down_window (model : RationalCostModel) (m k lambda n a fuel : ℕ)
    (h : GeneralPaperClassifierCFWords.QueryWidth m k lambda) (hf : fuel≤lambda+2)
    (ha : 0<a) (hnW : n<2^lambda) (haW : a<2^lambda) (s next : DownState)
    (hr : DownReach n a fuel s) (hs : downStep s=some next) :
    downWindow model (GeneralPaperPrecallControlWord.word m k) n a s next+
      topFootprint (GeneralPaperPrecallControlWord.word m k) (GeneralPaperQuotientTraversal.up n a fuel 0)+
      16*GeneralPaperPrecallControlWord.word m k≤
      128*(GeneralPaperPrecallControlWord.word m k+model.rat (32+8*lambda)) :=
  (reachable_down_window model _ n a fuel ha (calibrated_counter m k lambda fuel h hf) s next hr hs).trans
    (reservation_bound model _ lambda n a hnW haW)

end Blotto.GeneralPaperStreamingDivisionSpace

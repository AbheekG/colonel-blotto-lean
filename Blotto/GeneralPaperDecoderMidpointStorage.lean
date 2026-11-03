import Blotto.GeneralPaperCodeSplitStorage

/-! Decoder CF callback at its actual derived control word. Retain the
streaming query's caller/register/filter windows and the entire native
fraction/work/step/depth return, with primitive scratch separately priced. -/
namespace Blotto.GeneralPaperDecoderMidpointStorage
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def window (model : RationalCostModel) (W : ℕ) (closed : Bool) (a : Alphabet) (bucket : ℕ) : ℕ :=
  let A := controlWord W a.lambda
  GeneralPaperStreamingQuerySpace.peak model A closed a.D a.C bucket a.lambda+
    GeneralPaperStreamingQuerySpace.resultFootprint A (GeneralPaperDecoderMidpointPrice.run true model W closed a bucket).1+
      (GeneralPaperDecoderMidpointPrice.run true model W closed a bucket).2+128*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  4194304*(a.lambda+3)*(controlWord W a.lambda+model.rat (operandWidth a.lambda))

theorem bounded (model : RationalCostModel) (W : ℕ) (closed : Bool) (a : Alphabet) (bucket : ℕ) (hb : bucket<a.C) :
    window model W closed a bucket≤profile model W a := by
  let A := controlWord W a.lambda
  let F := A+model.rat (operandWidth a.lambda)
  have hpeak := GeneralPaperStreamingQuerySpace.peak_bound model A a.D a.C bucket a.lambda closed
    a.orderPositive a.scalePositive hb a.dyadic (cf_control W a.lambda)
  have hp := model.monotone (cf_width a)
  have hcf := hpeak.trans (Nat.mul_le_mul_left 1024 (Nat.add_le_add_left hp A))
  have hr := GeneralPaperClassifierConstructionStorage.query_return model A a.D a.C bucket a.lambda closed
  change GeneralPaperStreamingQuerySpace.resultFootprint A
    (GeneralPaperDecoderMidpointPrice.run true model W closed a bucket).1≤_ at hr
  have hwork := GeneralPaperDecoderMidpointPrice.bit_work model W closed a bucket hb
  have hWF : W≤F := by dsimp [F,A,controlWord]; omega
  change GeneralPaperStreamingQuerySpace.peak model A closed a.D a.C bucket a.lambda≤1024*F at hcf
  change (GeneralPaperDecoderMidpointPrice.run true model W closed a bucket).2≤2097152*(a.lambda+3)*F at hwork
  unfold window profile
  change _≤4194304*(a.lambda+3)*F
  nlinarith only [hcf,hr,hwork,hWF,Nat.zero_le (a.lambda*F)]

end Blotto.GeneralPaperDecoderMidpointStorage

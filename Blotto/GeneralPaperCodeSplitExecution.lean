import Blotto.GeneralPaperDecoderControls

/-! Exact code split with a streaming bit implementation and the existing
arithmetic-only constructed quotient in the unit model. No unit integer
division is assumed. Fuel construction and the native return annotation
are priced explicitly, and no source parameters are reconstructed.
-/
namespace Blotto.GeneralPaperCodeSplitExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (bits : Bool) (model : RationalCostModel) (W code lambda : ℕ) : GeneralPaperCodeSplit.Result × ℕ :=
  let fuel := lambda+1
  if bits then
    let found := GeneralPaperStreamingNatDivision.priced model (GeneralPaperDecoderControls.controlWord W lambda) code 4 fuel
    (⟨found.1.quotient,found.1.remainder,found.1.work+12⟩,found.2+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) lambda 1+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) found.1.work 12+96*W)
  else
    let found := GeneralPaperConstructedNatDivisionBits.run (fun _ => 1) 1 code 4 fuel
    (⟨found.1.quotient,found.1.remainder,found.1.work+12⟩,found.2+100)

theorem data (bits : Bool) (model : RationalCostModel) (W code lambda : ℕ) :
    (run bits model W code lambda).1=GeneralPaperCodeSplit.run code lambda := by
  cases bits
  · simp only [run,Bool.false_eq_true,ite_false,GeneralPaperConstructedNatDivisionBits.data,GeneralPaperCodeSplit.run]
  · simp only [run,ite_true,GeneralPaperStreamingNatDivision.priced_data,GeneralPaperCodeSplit.run]

theorem same_data (model : RationalCostModel) (W code lambda : ℕ) :
    (run true model W code lambda).1=(run false model 1 code lambda).1 := by rw [data,data]

end Blotto.GeneralPaperCodeSplitExecution

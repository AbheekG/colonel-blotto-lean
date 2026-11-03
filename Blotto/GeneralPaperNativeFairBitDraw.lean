import Blotto.GeneralPaperStoredCircleBitDraw

/-! Full bit-priced finite-fair-input draw. The fresh buffer, decoder,
selected shift, sweep/choice array, rational bids/name restoration and
original-budget output writes all use their actual operand prices. -/
namespace Blotto.GeneralPaperNativeFairBitDraw
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) : GeneralPaperNativeFairSampler.Result n :=
  let buffer := GeneralPaperNativeFreshBuffer.run model.rat A fresh
  let selected := GeneralPaperNativeDyadicBlocks.run model.rat A R L T S hT hS buffer.1.1
  let sampled := GeneralPaperStoredCircleBitDraw.original model A o hR c prepared selected.row selected.shift
  ⟨sampled.1,buffer.1.2,selected.reads,buffer.2+selected.work+sampled.2+64*A⟩

theorem data {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) :
    (run A R L T S hT hS model o hR c prepared fresh).output=
      (GeneralPaperNativeFairSampler.run model.rat A R L T S hT hS model o hR c prepared fresh).output := by
  dsimp only [run,GeneralPaperNativeFairSampler.run]
  rw [GeneralPaperStoredCircleBitDraw.original_data]

theorem fresh_reads {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) : (run A R L T S hT hS model o hR c prepared fresh).freshReads=Nat.log2 (T*S) := by
  dsimp only [run]
  rw [GeneralPaperNativeFreshBuffer.run_reads,hT,hS,←pow_add,Nat.log2_two_pow]

end Blotto.GeneralPaperNativeFairBitDraw

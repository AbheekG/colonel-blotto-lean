import Blotto.GeneralPaperNativeFreshBuffer

/-! One complete fresh-bit draw from a retained original-circle table.
Fresh bits materialize once, two disjoint blocks decode once, and one whole
row/shift allocation is evaluated. Preparation/source/compiler never rerun. -/
namespace Blotto.GeneralPaperNativeFairSampler
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result (n : ℕ) where
  output : FixedArrayTable n ℚ
  freshReads : ℕ
  bufferReads : ℕ
  work : ℕ

def run {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) : Result n :=
  let buffer := GeneralPaperNativeFreshBuffer.run primitive A fresh
  let selected := GeneralPaperNativeDyadicBlocks.run primitive A R L T S hT hS buffer.1.1
  let sampled := GeneralPaperOriginalCirclePreparation.draw model o hR c prepared selected.row selected.shift
  ⟨sampled.1,buffer.1.2,selected.reads,buffer.2+selected.work+sampled.2+64*A⟩

theorem data {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) :
    (run primitive A R L T S hT hS model o hR c prepared fresh).output=
      (GeneralPaperOriginalCirclePreparation.draw model o hR c prepared
        (Fin.cast hT.symm (bitIndex R (firstBitBlock R L fresh)))
        (Fin.cast hS.symm (bitIndex L (secondBitBlock R L fresh)))).1 := by
  dsimp only [run]
  rw [GeneralPaperNativeFreshBuffer.run_data,GeneralPaperNativeDyadicBlocks.row_data,GeneralPaperNativeDyadicBlocks.shift_data]

theorem fresh_reads {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) :
    (run primitive A R L T S hT hS model o hR c prepared fresh).freshReads=R+L :=
  GeneralPaperNativeFreshBuffer.run_reads primitive A fresh

theorem buffer_reads {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) :
    (run primitive A R L T S hT hS model o hR c prepared fresh).bufferReads=R+L :=
  GeneralPaperNativeDyadicBlocks.reads primitive A R L T S hT hS _

theorem logarithmic_bits {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (fresh : Fin (R+L) → Bool) :
    (run primitive A R L T S hT hS model o hR c prepared fresh).freshReads=Nat.log2 (T*S) := by
  rw [fresh_reads,hT,hS,←pow_add,Nat.log2_two_pow]

end Blotto.GeneralPaperNativeFairSampler

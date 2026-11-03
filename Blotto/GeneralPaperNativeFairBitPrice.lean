import Blotto.GeneralPaperStoredCircleBitPrice

/-! Complete local operand-sensitive bit profile of the actual cached
finite-fair-input draw. Reference/height conditions are erased properties
to be discharged by the final global calibration, not runtime oracles. -/
namespace Blotto.GeneralPaperNativeFairBitPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def profile (model : RationalCostModel) (A Rb Lb R W S C H n g : ℕ) : ℕ :=
  GeneralPaperNativeFreshBufferBits.profile model.rat A (Rb+Lb)+
    GeneralPaperNativeDyadicBlocksBits.profile model.rat A Rb Lb+
    GeneralPaperNamedCircleBitPrice.drawProfile model A R W S C H n g+128*A

theorem original_work {n K : ℕ} (model : RationalCostModel) (A Rb Lb T S C H : ℕ) (hA : 1≤A)
    (hT : T=2^Rb) (hS : S=2^Lb) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (c : ℚ)
    (price index : ℕ → ℕ) (Ap : ℕ) (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified)) (hc : RationalHeight c C)
    (hCapacity : 1+binaryWordWidth (2*n+o.representatives+2)≤A) (hRowAddress : binaryWordWidth (T+1)≤A)
    (_hBitAddress : binaryWordWidth (Rb+Lb+1)≤A) (fresh : Fin (Rb+Lb) → Bool) :
    (GeneralPaperNativeFairBitDraw.run A Rb Lb T S hT hS model o hR c
      (GeneralPaperOriginalCirclePreparation.run price index Ap o hm columns).1 fresh).work≤
      profile model A Rb Lb o.representatives o.classified.lightWeight S C H n o.classified.light.size := by
  let buffer := GeneralPaperNativeFreshBuffer.run model.rat A fresh
  let selected := GeneralPaperNativeDyadicBlocks.run model.rat A Rb Lb T S hT hS buffer.1.1
  have hf := GeneralPaperNativeFreshBufferBits.work model.rat model.monotone A fresh
  have hd := GeneralPaperNativeDyadicBlocksBits.work model.rat model.monotone A Rb Lb T S hT hS buffer.1.1
  have ho := GeneralPaperStoredCircleBitPrice.original_work model A C H hA o hm hR hW (hS ▸ Nat.two_pow_pos Lb) c price index Ap
    columns hColumns hConserved hBijective hc hCapacity hRowAddress selected.row selected.shift
  change buffer.2≤_ at hf
  change selected.work≤_ at hd
  change buffer.2+selected.work+
    (GeneralPaperStoredCircleBitDraw.original model A o hR c
      (GeneralPaperOriginalCirclePreparation.run price index Ap o hm columns).1 selected.row selected.shift).2+64*A≤_
  unfold profile
  omega

end Blotto.GeneralPaperNativeFairBitPrice

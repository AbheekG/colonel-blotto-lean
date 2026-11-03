import Blotto.GeneralPaperNativeFairSamplerLaw

/-! Complete local arithmetic price for fresh-bit buffer construction,
decoding and one cached whole-allocation draw. The previously proved
circle preparation is reused and is not charged again per draw. -/
namespace Blotto.GeneralPaperNativeFairSamplerPrice
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem arithmetic_work {n K : ℕ} (price index : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K))
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (c : ℚ)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (fresh : Fin (R+L) → Bool) :
    (GeneralPaperNativeFairSampler.run (fun _ => 1) 1 R L T S hT hS model o hR c
      (GeneralPaperOriginalCirclePreparation.run price index A o hm columns).1 fresh).work≤
      144*(R+L)+258+1024*(binaryWordWidth (o.representatives*o.classified.lightWeight)+1)+
        24*o.representatives+816*(n+1)+64 := by
  let buffer := GeneralPaperNativeFreshBuffer.run (fun _ => 1) 1 fresh
  let selected := GeneralPaperNativeDyadicBlocks.run (fun _ => 1) 1 R L T S hT hS buffer.1.1
  have hf := GeneralPaperNativeFreshBuffer.arithmetic_work 1 fresh
  have hd := GeneralPaperNativeDyadicBlocks.arithmetic_work 1 R L T S hT hS buffer.1.1
  have hw := GeneralPaperOriginalDrawBounds.arithmetic_draw_work price index A model o hm columns hR hW
    (hS ▸ Nat.two_pow_pos L) c hConserved hBijective selected.row selected.shift
  change buffer.2≤_ at hf
  change selected.work≤_ at hd
  change buffer.2+selected.work+
    (GeneralPaperOriginalCirclePreparation.draw model o hR c
      (GeneralPaperOriginalCirclePreparation.run price index A o hm columns).1 selected.row selected.shift).2+64*1≤_
  nlinarith only [hf,hd,hw]

end Blotto.GeneralPaperNativeFairSamplerPrice

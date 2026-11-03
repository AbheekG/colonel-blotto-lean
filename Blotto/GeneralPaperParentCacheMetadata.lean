import Blotto.GeneralPaperTreeEpochPreparation

/-! Complete native parent-cache annotations derive their own counter cap.
Three additions form the returned work value. Bounds and operand words are
analysis only and never replay a child, power query or sum.
-/
namespace Blotto.GeneralPaperParentCacheMetadata
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def cap (p columns : ℕ) : ℕ := (columns+4)*(40*(p+1)+256)

theorem native_bound (lambda k leftOffset rightOffset : ℕ) (leftMass rightMass : GeneralPaperDyadicFloat.Number) :
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    (GeneralPaperCachedMassJoin.recompute prepared leftOffset leftMass rightOffset rightMass).work≤
      cap prepared.format.fractionalBits prepared.format.columns := by
  have hl := GeneralPaperPreparedPowers.query_work lambda k leftOffset
  have hr := GeneralPaperPreparedPowers.query_work lambda k rightOffset
  have hj := GeneralPaperCachedMassJoin.recompute_work (GeneralPaperPreparedPowers.prepare lambda k)
    leftOffset rightOffset leftMass rightMass
  unfold cap
  nlinarith only [hl,hr,hj,Nat.zero_le ((GeneralPaperPreparedPowers.prepare lambda k).format.columns*
    (GeneralPaperPreparedPowers.prepare lambda k).format.fractionalBits)]

theorem word_bound (p columns : ℕ) : 1+binaryWordWidth (cap p columns)≤128+16*(p+columns+1) := by
  have hm := binaryWordWidth_mul (columns+4) (40*(p+1)+256)
  have hp := binaryWordWidth_mul 40 (p+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (40*(p+1)) 256
  have hc := GeneralPaperInitializerControlCounters.word_le_self (columns+4)
  have hs := GeneralPaperInitializerControlCounters.word_le_self (p+1)
  have h40 : binaryWordWidth 40=6 := by decide
  have h256 : binaryWordWidth 256=9 := by decide
  unfold cap
  omega

theorem operand_width (m lambda k Qv : ℕ) :
    1+binaryWordWidth (cap (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
      (GeneralPaperPowerPrecision.prepare lambda k).columns)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hw := word_bound (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits (GeneralPaperPowerPrecision.prepare lambda k).columns
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  have hc := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).columns
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

def cost (price : ℕ → ℕ) (left right sum : ℕ) : ℕ :=
  GeneralPaperPowerTableBounds.metadataCost price left right sum+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (left+right+sum) 24

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (left right sum cap L : ℕ)
    (hCap : left+right+sum+24≤cap) (hWidth : 1+binaryWordWidth cap≤L) : cost price left right sum≤6*price L := by
  have hm := GeneralPaperPowerTableBounds.metadata_work price hMono left right sum cap L (by omega) hWidth
  have ha := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) (left+right+sum) 24 cap
    (by omega) (by omega) hCap).trans (Nat.mul_le_mul_left 2 (hMono hWidth))
  unfold cost
  omega

theorem arithmetic_cost (left right sum : ℕ) : cost (fun _ => 1) left right sum=6 := rfl

end Blotto.GeneralPaperParentCacheMetadata

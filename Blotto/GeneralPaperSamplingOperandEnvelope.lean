import Blotto.GeneralPaperClosedBitSampling

/-! Separate short control prices from the final original-budget products.
This prevents charging the long original ratio on every circle-bin step.
All envelopes are erased analysis of the already checked native profile. -/
namespace Blotto.GeneralPaperSamplingOperandEnvelope
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def controlSize (A Rb Lb R W S : ℕ) : ℕ :=
  1+A+Rb+Lb+binaryWordWidth R+binaryWordWidth W+binaryWordWidth S

theorem word_add (a b : ℕ) : binaryWordWidth (a+b)≤binaryWordWidth a+binaryWordWidth b :=
  GeneralPaperReferenceScaling.word_add a b

theorem decoder_width (Rb Lb : ℕ) :
    GeneralPaperNativeFairIndexBits.width (Rb+Lb) Rb≤3*(Rb+Lb)+6 ∧
      GeneralPaperNativeFairIndexBits.width (Rb+Lb) Lb≤3*(Rb+Lb)+6 := by
  have hr := word_add (Rb+Lb) (2^Rb+2)
  have hs := word_add (Rb+Lb) (2^Lb+2)
  have hr' := word_add (2^Rb) 2
  have hs' := word_add (2^Lb) 2
  have hN : binaryWordWidth (Rb+Lb)≤Rb+Lb+1 := by
    unfold binaryWordWidth
    have h := Nat.log2_le_self (Rb+Lb)
    omega
  have hpR : binaryWordWidth (2^Rb)=Rb+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  have hpS : binaryWordWidth (2^Lb)=Lb+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  rw [hpR,show binaryWordWidth 2=2 by decide] at hr'
  rw [hpS,show binaryWordWidth 2=2 by decide] at hs'
  unfold GeneralPaperNativeFairIndexBits.width GeneralPaperNativeFairIndexBits.magnitude
  have h2 : binaryWordWidth 2=2 := by decide
  rw [←Nat.add_assoc] at hr hs
  constructor <;> omega

theorem sweep_width (R W : ℕ) :
    GeneralPaperCircleSweepBitBounds.width R W≤2*binaryWordWidth R+2*binaryWordWidth W+9 := by
  have h0 := binaryWordWidth_mul 64 (R*W+R+W+1)
  have h1 := word_add (R*W+R+W) 1
  have h2 := word_add (R*W+R) W
  have h3 := word_add (R*W) R
  have h4 := binaryWordWidth_mul R W
  rw [show binaryWordWidth 64=7 by decide] at h0
  unfold GeneralPaperCircleSweepBitBounds.width GeneralPaperCircleSweepBitBounds.magnitude
  have hOne : binaryWordWidth 1=1 := by decide
  omega

theorem short_widths (A Rb Lb R W S : ℕ) :
    let L := controlSize A Rb Lb R W S
    GeneralPaperNativeFreshBufferBits.width (Rb+Lb)≤64*L ∧
      GeneralPaperNativeFairIndexBits.width (Rb+Lb) Rb≤64*L ∧
      GeneralPaperNativeFairIndexBits.width (Rb+Lb) Lb≤64*L ∧
      1+binaryWordWidth (Rb+Lb+2)≤64*L ∧
      GeneralPaperNativeShiftPrice.width (R*W) S≤64*L ∧
      GeneralPaperCircleSweepBitBounds.width R W≤64*L := by
  have hd := decoder_width Rb Lb
  have hn : binaryWordWidth (Rb+Lb+2)≤Rb+Lb+3 := by
    unfold binaryWordWidth
    have h := Nat.log2_le_self (Rb+Lb+2)
    omega
  have hShift := GeneralPaperNativeShiftPrice.width_bound (R*W) S
  have hProduct := binaryWordWidth_mul R W
  have hSweep := sweep_width R W
  unfold controlSize GeneralPaperNativeFreshBufferBits.width
  omega

theorem combined_profile {n : ℕ} (model : RationalCostModel) (A Rb k B H : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n)
    (hg : o.classified.light.size≤n) (hh : o.classified.heavy.size≤n) :
    let L := controlSize A Rb (k+6) o.representatives o.classified.lightWeight (GeneralPaperNativeSelectedSecurity.count k)
    GeneralPaperClosedBitSampling.profile model A Rb k B H o≤
      65536*(n+o.representatives+1)*L*model.rat (64*L)+
        6*n*model.rat (8*(B+H+L)) := by
  let R := o.representatives
  let W := o.classified.lightWeight
  let S := GeneralPaperNativeSelectedSecurity.count k
  let L := controlSize A Rb (k+6) R W S
  let P := model.rat (64*L)
  let Q := model.rat (8*(B+H+L))
  have hWidths := short_widths A Rb (k+6) R W S
  have hA : A≤P := (show A≤64*L by dsimp only [L,controlSize];omega).trans (model.word_le _)
  have hOne : 1≤P := (show 1≤64*L by dsimp only [L,controlSize];omega).trans (model.word_le _)
  have h0 := model.monotone hWidths.1
  have h1 := model.monotone hWidths.2.1
  have h2 := model.monotone hWidths.2.2.1
  have h3 := model.monotone hWidths.2.2.2.1
  have h4 := model.monotone hWidths.2.2.2.2.1
  have h5 := model.monotone hWidths.2.2.2.2.2
  change _≤P at h0 h1 h2 h3 h4 h5
  have h6 : model.rat (1+2*(binaryWordWidth R+2*binaryWordWidth W+H))≤Q :=
    model.monotone (by dsimp only [L,controlSize];omega)
  have h7 : model.rat (1+2*((B+1)+(binaryWordWidth R+2*binaryWordWidth W+H)))≤Q :=
    model.monotone (by dsimp only [L,controlSize];omega)
  have h8 : model.rat (1+2*((B+1)+H))≤Q := model.monotone (by dsimp only [L,controlSize];omega)
  have hWord := binaryWordWidth_mul R W
  have hW : binaryWordWidth (R*W)+1≤L := by dsimp only [L,controlSize];omega
  have hWPrice : (binaryWordWidth (R*W)+1)*(A+model.rat (GeneralPaperNativeShiftPrice.width (R*W) S))≤2*L*P := by
    have h := Nat.mul_le_mul hW (show A+model.rat (GeneralPaperNativeShiftPrice.width (R*W) S)≤2*P by omega)
    exact h.trans_eq (by ring)
  have hL : 1≤L := by dsimp only [L,controlSize];omega
  have hBits : Rb+(k+6)≤L := by dsimp only [L,controlSize];omega
  have hShift : 512*(binaryWordWidth (R*W)+1)*(A+model.rat (GeneralPaperNativeShiftPrice.width (R*W) S))≤1024*L*P := by nlinarith only [hWPrice]
  have hBuffer : GeneralPaperNativeFreshBufferBits.profile model.rat A (Rb+(k+6))≤134*L*P := by
    unfold GeneralPaperNativeFreshBufferBits.profile
    have h := Nat.mul_le_mul_left (70*P) hBits
    have hp := Nat.mul_le_mul_left (64*P) hL
    have hPrice : 5*model.rat (GeneralPaperNativeFreshBufferBits.width (Rb+(k+6)))+64*A+1≤70*P := by omega
    have hx := Nat.mul_le_mul_left (Rb+(k+6)) hPrice
    nlinarith only [h,hp,hx,hA]
  have hDecoder : GeneralPaperNativeDyadicBlocksBits.profile model.rat A Rb (k+6)≤204*L*P := by
    unfold GeneralPaperNativeDyadicBlocksBits.profile
    have hr := Nat.mul_le_mul_left Rb (show 10*model.rat (GeneralPaperNativeFairIndexBits.width (Rb+(k+6)) Rb)+64*A≤74*P by omega)
    have hs := Nat.mul_le_mul_left (k+6) (show 10*model.rat (GeneralPaperNativeFairIndexBits.width (Rb+(k+6)) (k+6))+64*A≤74*P by omega)
    have h := Nat.mul_le_mul_left (74*P) hBits
    have hp := Nat.mul_le_mul_left (130*P) hL
    nlinarith only [hr,hs,h,hp,hA,h3]
  have hCircle : GeneralPaperCircleControlDrawBits.profile model A R W S o.classified.light.size≤
      1024*L*P+768*(2*R+n+1)*P+36*P := by
    unfold GeneralPaperCircleControlDrawBits.profile GeneralPaperNativeShiftPrice.profile GeneralPaperCircleSweepBitPrice.unitPrice
    simp only [ite_true]
    have hu := Nat.mul_le_mul_left (2*R+o.classified.light.size+1)
      (show 512*A+256*model.rat (GeneralPaperCircleSweepBitBounds.width R W)≤768*P by omega)
    have hg' := Nat.mul_le_mul_right (768*P) (show 2*R+o.classified.light.size+1≤2*R+n+1 by omega)
    nlinarith only [hShift,hu,hg',h5,hA]
  have hChoice : GeneralPaperNativeChoiceArrayBits.profile model A R W S o.classified.light.size≤
      1024*L*P+768*(2*R+n+1)*P+(64*n+132)*P := by
    unfold GeneralPaperNativeChoiceArrayBits.profile
    have hg' := Nat.mul_le_mul_right (64*P) hg
    have ha := Nat.mul_le_mul_left (64*(o.classified.light.size+1)+32) hA
    nlinarith only [hCircle,hg',ha]
  have hAssemble : GeneralPaperNamedCircleBitPrice.assembleProfile model A (B+1)
      (binaryWordWidth R+2*binaryWordWidth W) H n≤4*n*Q+1024*(n+1)*P := by
    unfold GeneralPaperNamedCircleBitPrice.assembleProfile
    have hp := Nat.mul_le_mul_left (2*n) (show model.rat (1+2*(binaryWordWidth R+2*binaryWordWidth W+H))+
      model.rat (1+2*((B+1)+(binaryWordWidth R+2*binaryWordWidth W+H)))≤2*Q by omega)
    have ha := Nat.mul_le_mul_left (1024*(n+1)) hA
    nlinarith only [hp,ha]
  have hNamed : GeneralPaperNamedCircleBitPrice.drawProfile model A R W S (B+1) H n o.classified.light.size≤
      1024*L*P+768*(2*R+n+1)*P+(1088*n+1188)*P+4*n*Q := by
    unfold GeneralPaperNamedCircleBitPrice.drawProfile
    nlinarith only [hChoice,hAssemble,hA]
  have hSelected : GeneralPaperCachedCircleWork.selectedProfile o.classified.heavy.size A≤(172*n+108)*P := by
    unfold GeneralPaperCachedCircleWork.selectedProfile
    have ha := Nat.mul_le_mul_left (172*o.classified.heavy.size+108) hA
    have hh' := Nat.mul_le_mul_right (172*P) hh
    nlinarith only [ha,hh']
  have hDirect : GeneralPaperCachedBitSampling.directProfile model A Rb (k+6) (B+1) H n≤
      338*L*P+2*n*Q+(280*n+216)*P := by
    unfold GeneralPaperCachedBitSampling.directProfile
    have hp := Nat.mul_le_mul_left (2*n) h8
    have ha := Nat.mul_le_mul_left (280*n+216) hA
    nlinarith only [hBuffer,hDecoder,hp,ha]
  have hWhole : GeneralPaperClosedBitSampling.profile model A Rb k B H o≤
      1700*L*P+(1540*R+2500*n+3000)*P+6*n*Q := by
    unfold GeneralPaperClosedBitSampling.profile GeneralPaperCachedBitSampling.profile GeneralPaperNativeFairBitPrice.profile
    dsimp only [R,W,S] at hNamed ⊢
    nlinarith only [hBuffer,hDecoder,hNamed,hSelected,hDirect,hA]
  have hLong : (1540*R+2500*n+3000)*P≤(1540*R+2500*n+3000)*L*P := by
    have h := Nat.mul_le_mul_right ((1540*R+2500*n+3000)*P) hL
    exact (show (1540*R+2500*n+3000)*P≤L*((1540*R+2500*n+3000)*P) by simpa only [Nat.one_mul] using h).trans_eq (by ring)
  exact hWhole.trans (by
    change _≤65536*(n+R+1)*L*P+6*n*Q
    nlinarith only [hLong,Nat.zero_le (R*L*P),Nat.zero_le (n*L*P),Nat.zero_le (L*P)])

end Blotto.GeneralPaperSamplingOperandEnvelope

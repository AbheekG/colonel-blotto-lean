import Blotto.GeneralPaperClosedDescriptionStorage

/-! Compact retained-description algebra. Labels, reference rows and
anchor payloads are separate terms. The original budget contributes only
its own encoding; no rational anchor payload is copied per sorted entry. -/
namespace Blotto.GeneralPaperDescriptionSizeAlgebra
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperEnclosingSourceOwners GeneralPaperClosedDescriptionStorage
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def word (W n k : ℕ) : ℕ := 128+W+k+binaryWordWidth (n+4)
def shape (n m T K H : ℕ) : ℕ := n+1+m*T+m*K*(H+1)

theorem word_positive (W n k : ℕ) : 1≤word W n k := by unfold word;omega

theorem cache_bound (W n g R mass P : ℕ) (hP : 1≤P) (hW : W≤P) (hg : g≤n)
    (hR : binaryWordWidth R≤P) (hMass : binaryWordWidth mass≤P) :
    GeneralPaperCachedCircleRetainedStorage.commonProfile W g R mass≤512*(n+1)*P := by
  have hProduct := binaryWordWidth_mul R mass
  have hNat : natBits mass≤2*P := by unfold natBits;omega
  have hCoeff : 1+2*(binaryWordWidth R+2*binaryWordWidth mass)≤7*P := by omega
  have hArc : 2*natBits (R*mass)+34*W≤40*P := by unfold natBits;omega
  have h1 := Nat.mul_le_mul_left g (show W+natBits mass≤3*P by omega)
  have h2 := Nat.mul_le_mul_left g (show W+(1+2*(binaryWordWidth R+2*binaryWordWidth mass))≤8*P by omega)
  have h3 := Nat.mul_le_mul_left g hArc
  have hn := Nat.mul_le_mul_right (51*P) hg
  unfold GeneralPaperCachedCircleRetainedStorage.commonProfile arrayProfile
  nlinarith only [h1,h2,h3,hn,hW]

theorem columns_bound (W T m K H P : ℕ) (hP : 1≤P) (hW : W≤P) (hK : binaryWordWidth K≤P) :
    columnsProfile W T m K (1+2*H)≤3*m*T*P+2*m*K*(H+1)*P+161*m*P+64*P := by
  have hHP : H≤H*P := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left H hP
  have hLabel := Nat.mul_le_mul_left (m*T) (show W+natBits K≤3*P by unfold natBits;omega)
  have hAnchor := Nat.mul_le_mul_left (m*K) (show W+(1+2*H)≤2*(H+1)*P by nlinarith only [hHP,hW,hP])
  have hFrame := Nat.mul_le_mul_left (161*m+64) hW
  unfold columnsProfile columnProfile arrayProfile
  nlinarith only [hLabel,hAnchor,hFrame]

theorem references_bound (W T m P : ℕ) (hm : 0<m) (hW : W≤P) :
    GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile W T m≤66*m*T*P+64*P := by
  have hFrame := Nat.mul_le_mul_left ((m+65)*T+64) hW
  have hm' := Nat.mul_le_mul_left (65*T*P) (show 1≤m by omega)
  unfold GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile arrayProfile
  nlinarith only [hFrame,hm']

theorem description_bound {n : ℕ} (W T K H P : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hP : 1≤P) (hW : W≤P) (hm : 0<o.m) (hmn : o.m≤n) (hg : o.classified.light.size≤n)
    (hR : binaryWordWidth o.representatives≤P) (hMass : binaryWordWidth o.classified.lightWeight≤P)
    (hK : binaryWordWidth K≤P) :
    descriptionProfile W T K H o≤2048*shape n o.m T K H*P := by
  have hc := cache_bound W n o.classified.light.size o.representatives o.classified.lightWeight P hP hW hg hR hMass
  have hColumns := columns_bound W T o.m K H P hP hW hK
  have hReferences := references_bound W T o.m P hm hW
  have hn := Nat.mul_le_mul_right (322*P) hmn
  unfold descriptionProfile shape
  nlinarith only [hc,hColumns,hReferences,hn,hW,Nat.zero_le (o.m*T*P),Nat.zero_le (o.m*K*(H+1)*P),Nat.zero_le (n*P)]

theorem controls_bound (W T Rb k P : ℕ) (_hP : 1≤P) (hW : W≤P)
    (hT : binaryWordWidth T≤4*P) (hRb : binaryWordWidth Rb≤4*P) (hK : k+8≤P) :
    controlsProfile W T Rb k≤64*P := by
  have hS : binaryWordWidth (GeneralPaperNativeSelectedSecurity.count k)=k+7 := by
    rw [GeneralPaperNativeSelectedSecurity.count_power]
    simp only [binaryWordWidth,Nat.log2_two_pow]
  have hL : binaryWordWidth (k+6)≤k+7 := GeneralPaperSamplingFastBitBound.word_self _
  unfold controlsProfile fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,Nat.add_zero]
  unfold natBits
  omega

theorem native_profile {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv W k T K H Rb B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hK : binaryWordWidth K≤word W n k) (hT : binaryWordWidth T≤4*word W n k)
    (hRb : binaryWordWidth Rb≤4*word W n k) :
    let o := (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
    profile W T K Rb k B H o≤8192*shape n o.m T K H*word W n k+2*B := by
  let o := (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
  let P := word W n k
  have hP : 1≤P := word_positive W n k
  have hW : W≤P := by unfold P word;omega
  have hCounts := GeneralPaperOriginalValueReduction.count_bounds bits model Wv k values v hv
  have hg := GeneralPaperStrategyPreparationWork.light_size bits model Wv k values
  have hR := GeneralPaperOriginalValueReductionPrice.representatives_word k
  rw [←GeneralPaperNativeReductionShape.original_representatives bits model Wv k values] at hR
  have hMass := (binaryWordWidth_mono (GeneralPaperNativeCircleLoss.original_mass_bound bits model Wv k values)).trans
    (GeneralPaperOriginalValueReduction.denominator_word bits model Wv k values v hv)
  have hn := binaryWordWidth_mono (show n≤n+4 by omega)
  have hRP : binaryWordWidth o.representatives≤P := by dsimp only [o,P,word];omega
  have hMP : binaryWordWidth o.classified.lightWeight≤P := by dsimp only [o,P,word];omega
  have hd := description_bound W T K H P o hP hW hCounts.1 hCounts.2.1 hg hRP hMP hK
  have hControl := controls_bound W T Rb k P hP hW hT hRb (by dsimp only [P,word];omega)
  have hOriginal := Nat.mul_le_mul_left (2048*(n+1))
    (show W+binaryWordWidth n+k+1≤P by dsimp only [P,word];omega)
  have hShape : 1≤shape n o.m T K H := by unfold shape;omega
  have hOne := Nat.mul_le_mul_left P hShape
  change GeneralPaperClosedDescriptionStorage.profile W T K Rb k B H o≤8192*shape n o.m T K H*P+2*B
  unfold GeneralPaperClosedDescriptionStorage.profile
  unfold shape at hd hShape ⊢
  nlinarith only [hd,hControl,hOriginal,hW,hP,hOne,Nat.zero_le (o.m*T*P),Nat.zero_le (o.m*K*(H+1)*P)]

end Blotto.GeneralPaperDescriptionSizeAlgebra

import Blotto.GeneralPaperInitializerControlScalarStorage

/-! Complete native initializer-control parent. The full returned
parameter record, signed auxiliary numerator, scale result and every
native parent work prefix coexist with complete doubling/scalar windows. -/
namespace Blotto.GeneralPaperInitializerControlStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def parameterFoot (W : ℕ) (c : GeneralPaperInitializerParameters.Parameters) : ℕ :=
  natBits c.N+natBits c.depth+rationalWordWidth c.beta+rationalWordWidth c.tau+rationalWordWidth c.auxiliary+natBits c.work+32*W
def price (model : RationalCostModel) (W R : ℕ) : ℕ := 1024*(R+1)*(W+model.rat R)
def metadataCap (model : RationalCostModel) (W R : ℕ) : ℕ := 32*R+price model W R+128*W+128
def controls (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) : List ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  let scale := GeneralPaperPowerCeilingBits.run model.rat W c.N
  let a := GeneralPaperInitializerControlBits.naturalWork model m H p q c
  let b := GeneralPaperInitializerControlBits.casts model m p q c
  let r := GeneralPaperInitializerControlBits.rationalWork model m p q reciprocal c
  let s := GeneralPaperInitializerControlScalarStorage.signedPrice model m H p q reciprocal
  let result := GeneralPaperInitializerControlBits.run model W m H p q reciprocal
  [scale.1.doublings,scale.1.work,scale.2,a,b,r,s,result.2,result.1.1.depth,result.1.1.work,128*W,
    scale.2+a,scale.2+a+b,scale.2+a+b+r,scale.2+a+b+r+s]
def window (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) : ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  let scale := GeneralPaperPowerCeilingBits.run model.rat W c.N
  let result := GeneralPaperInitializerControlBits.run model W m H p q reciprocal
  GeneralPaperPowerCeilingStorage.window model W c.N 1 (by decide)+
    GeneralPaperInitializerControlScalarStorage.window model W m H p q reciprocal+
    parameterFoot W result.1.1+integerBits result.1.2+natBits scale.1.power+
    fields W (controls model W m H p q reciprocal)+256*W
def profile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  GeneralPaperPowerCeilingStorage.profile model W R+GeneralPaperInitializerControlScalarStorage.profile model W R+
    6*R+2*natBits (metadataCap model W R)+15*(natBits (metadataCap model W R)+W)+320*W

theorem bounded (model : RationalCostModel) (W m H p q R : ℕ) (reciprocal : Bool)
    (hR : GeneralPaperInitializerControlSize.width m H p q≤R) : window model W m H p q reciprocal≤profile model W R := by
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  let scale := GeneralPaperPowerCeilingBits.run model.rat W c.N
  let result := GeneralPaperInitializerControlBits.run model W m H p q reciprocal
  have hCeil := (GeneralPaperInitializerControlSize.ceiling_width m H p q reciprocal).trans hR
  have hCeiling := GeneralPaperPowerCeilingStorage.bounded model W c.N R hCeil
  have hScalar := GeneralPaperInitializerControlScalarStorage.bounded model W m H p q R reciprocal hR
  have hScale := GeneralPaperPowerCeilingStorage.result_bounds model W c.N 1 (c.N+1) R (by decide) (by omega) (by omega) hCeil
  change scale.1.power≤2*(c.N+1) ∧ scale.1.doublings≤R ∧ scale.1.work≤12*R+2 at hScale
  have hPower : natBits scale.1.power≤R := (Nat.add_le_add_left (binaryWordWidth_mono hScale.1) 1).trans hCeil
  obtain ⟨_,_,_,_,_,_,_,_,hN,_,_,_⟩ := GeneralPaperInitializerControlSize.natural_words m H p q reciprocal
  obtain ⟨_,_,_,_,hb,ht,ha⟩ := GeneralPaperInitializerControlSize.rational_words m H p q reciprocal
  have hi := (GeneralPaperInitializerControlSize.signed_words m H p q reciprocal).2.2
  have hNum : integerBits result.1.2≤R := hi.trans hR
  have hNWord : natBits result.1.1.N≤R := hN.trans hR
  have hBeta : rationalWordWidth result.1.1.beta≤R := hb.trans hR
  have hTau : rationalWordWidth result.1.1.tau≤R := ht.trans hR
  have hAux : rationalWordWidth result.1.1.auxiliary≤R := ha.trans hR
  have hDepth : result.1.1.depth≤R+1 := by change scale.1.doublings+1≤R+1; omega
  have hNative : result.1.1.work≤12*R+66 := by change scale.1.work+64≤12*R+66; omega
  have hDepthWord : natBits result.1.1.depth≤natBits (metadataCap model W R) := by
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold metadataCap
    omega
  have hNativeWord : natBits result.1.1.work≤natBits (metadataCap model W R) := by
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold metadataCap
    omega
  have hWork : result.2≤price model W R := by
    have h := GeneralPaperInitializerControlBits.work model W m H p q reciprocal
    have hw : binaryWordWidth (4*m*H*p*q)≤R := by change 1+binaryWordWidth (4*m*H*p*q)≤_ at hN; omega
    exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 1024 (Nat.add_le_add_right hw 1)) (Nat.add_le_add_left (model.monotone hR) W))
  have hShape : result.2=scale.2+GeneralPaperInitializerControlBits.naturalWork model m H p q c+
      GeneralPaperInitializerControlBits.casts model m p q c+GeneralPaperInitializerControlBits.rationalWork model m p q reciprocal c+
      GeneralPaperInitializerControlScalarStorage.signedPrice model m H p q reciprocal+128*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W R)) (controls model W m H p q reciprocal) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    change z∈[scale.1.doublings,scale.1.work,scale.2,
      GeneralPaperInitializerControlBits.naturalWork model m H p q c,GeneralPaperInitializerControlBits.casts model m p q c,
      GeneralPaperInitializerControlBits.rationalWork model m p q reciprocal c,
      GeneralPaperInitializerControlScalarStorage.signedPrice model m H p q reciprocal,result.2,result.1.1.depth,result.1.1.work,128*W,
      scale.2+GeneralPaperInitializerControlBits.naturalWork model m H p q c,
      scale.2+GeneralPaperInitializerControlBits.naturalWork model m H p q c+GeneralPaperInitializerControlBits.casts model m p q c,
      scale.2+GeneralPaperInitializerControlBits.naturalWork model m H p q c+GeneralPaperInitializerControlBits.casts model m p q c+
        GeneralPaperInitializerControlBits.rationalWork model m p q reciprocal c,
      scale.2+GeneralPaperInitializerControlBits.naturalWork model m H p q c+GeneralPaperInitializerControlBits.casts model m p q c+
        GeneralPaperInitializerControlBits.rationalWork model m p q reciprocal c+GeneralPaperInitializerControlScalarStorage.signedPrice model m H p q reciprocal] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W (controls model W m H p q reciprocal)≤15*(natBits (metadataCap model W R)+W)+32*W at hf
  unfold window profile parameterFoot
  dsimp only
  dsimp only [c,scale,result] at hCeiling hScalar hPower hNum hNWord hBeta hTau hAux hDepthWord hNativeWord
  omega

end Blotto.GeneralPaperInitializerControlStorage

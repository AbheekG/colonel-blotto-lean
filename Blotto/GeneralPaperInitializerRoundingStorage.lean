import Blotto.GeneralPaperSourceInitializerControlStorageReachedRates

/-! Literal downward-rounding scalar ownership. The existing native bit
quotient retains its computed numerator; no floor or rational numerator is
recomputed. Full quotient scratch/frames, returned raw record, casts and
rounded value coexist with all thirteen parent price/return fields. -/
namespace Blotto.GeneralPaperInitializerRoundingStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage GeneralPaperRationalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W R : ℕ) : ℕ := 256*(R+1)*(W+model.rat R)
def metadataCap (model : RationalCostModel) (W R : ℕ) : ℕ := 32*R+price model W R+64*W+64
def controls (model : RationalCostModel) (W N depth : ℕ) (u : ℚ) : List ℕ :=
  let raw := GeneralPaperBoundedQuotient.runWithBits model W (u*(N:ℚ)) 1 depth
  let result := GeneralPaperInitializerRoundingBits.run model W N depth u
  let a := binary model.rat (fun x y => x*y) u (N:ℚ)
  let b := model.rat (rationalWordWidth (N:ℚ))
  let c := model.rat (rationalWordWidth (raw.1.quotient:ℚ))
  let d := binary model.rat (fun x y => x/y) (raw.1.quotient:ℚ) (N:ℚ)
  [depth,raw.1.work,raw.2,result.2,a,b,c,d,48*W,raw.2+a,raw.2+a+b,raw.2+a+b+c,raw.2+a+b+c+d]
def window (model : RationalCostModel) (W N depth : ℕ) (u : ℚ) : ℕ :=
  let raw := GeneralPaperBoundedQuotient.runWithBits model W (u*(N:ℚ)) 1 depth
  let result := GeneralPaperInitializerRoundingBits.run model W N depth u
  GeneralPaperBitQuotientStorage.peak model W (u*(N:ℚ)) 1 depth+
    GeneralPaperQuotientConstructionStorage.record W raw.1+natBits N+natBits raw.1.quotient+
    rationalWordWidth u+rationalWordWidth (N:ℚ)+rationalWordWidth (u*(N:ℚ))+
    rationalWordWidth (raw.1.quotient:ℚ)+rationalWordWidth result.1.2+rationalWordWidth (1:ℚ)+
    binary model.rat (fun x y => x*y) u (N:ℚ)+model.rat (rationalWordWidth (N:ℚ))+
    model.rat (rationalWordWidth (raw.1.quotient:ℚ))+
    binary model.rat (fun x y => x/y) (raw.1.quotient:ℚ) (N:ℚ)+
    fields W (controls model W N depth u)+256*W
def profile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  GeneralPaperBitQuotientStorage.profile model W R 1 R+
    4*(1+2*GeneralPaperBoundedQuotient.heightBudget R 1 R)+128*W+
    8*R+6*model.rat R+13*(natBits (metadataCap model W R)+W)+320*W

theorem quotient_mono (model : RationalCostModel) (W A d R : ℕ) (hA : A≤R) (hd : d≤R) :
    GeneralPaperBitQuotientStorage.profile model W A 1 d≤GeneralPaperBitQuotientStorage.profile model W R 1 R := by
  have hBudget : GeneralPaperBoundedQuotient.heightBudget A 1 d≤GeneralPaperBoundedQuotient.heightBudget R 1 R := by
    unfold GeneralPaperBoundedQuotient.heightBudget
    omega
  have hRat := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hBudget) 1)
  have hBit : GeneralPaperBoundedQuotient.bitProfile model W A 1 d≤GeneralPaperBoundedQuotient.bitProfile model W R 1 R := by
    unfold GeneralPaperBoundedQuotient.bitProfile
    exact Nat.mul_le_mul (Nat.add_le_add_right hd 1) (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hRat) _)
  have hMeta : GeneralPaperBitQuotientStorage.metadataCap model W A 1 d≤GeneralPaperBitQuotientStorage.metadataCap model W R 1 R := by
    unfold GeneralPaperBitQuotientStorage.metadataCap
    omega
  have hWord := binaryWordWidth_mono hMeta
  unfold GeneralPaperBitQuotientStorage.profile GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
    GeneralPaperBitQuotientStorage.counterFrameProfile natBits
  dsimp only
  have hFirst : (d+1)*(4*(1+2*d+8)+128*W)≤(R+1)*(4*(1+2*R+8)+128*W) := by gcongr
  have hLast : (d+1)*(4*(1+binaryWordWidth (GeneralPaperBitQuotientStorage.metadataCap model W A 1 d)+W)+160*W)≤
      (R+1)*(4*(1+binaryWordWidth (GeneralPaperBitQuotientStorage.metadataCap model W R 1 R)+W)+160*W) := by gcongr
  omega

theorem bounded (model : RationalCostModel) (W N depth A R : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (u : ℚ) (hu : 0≤u ∧ u≤1) (hHeight : RationalHeight u A)
    (hR : GeneralPaperInitializerRoundingBits.width A N depth≤R) : window model W N depth u≤profile model W R := by
  let raw := GeneralPaperBoundedQuotient.runWithBits model W (u*(N:ℚ)) 1 depth
  let result := GeneralPaperInitializerRoundingBits.run model W N depth u
  let B := binaryWordWidth N
  have hAR : A+B≤R := by unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have hd : depth≤R := by unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have hn := GeneralPaperBasisDivideBits.nat_height N
  have hs := hHeight.mul hn
  have hOne : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
  have hScaled : u*(N:ℚ)<(1:ℚ)*(2:ℚ)^depth := by
    have hc : (N:ℚ)<(2:ℚ)^depth := by exact_mod_cast hCap
    have hn0 : (0:ℚ)≤N := by positivity
    nlinarith only [hu.2,hc,hn0]
  have hNonneg := mul_nonneg hu.1 (Nat.cast_nonneg N)
  have hQuotient := (GeneralPaperBitQuotientStorage.bounded model W (u*(N:ℚ)) 1 (by norm_num) depth (A+B) 1
    hNonneg hScaled hs hOne).trans (quotient_mono model W (A+B) depth R hAR hd)
  have hRecord := GeneralPaperBitQuotientStorage.returned_record model W (u*(N:ℚ)) 1 (by norm_num) depth (A+B) 1
    hNonneg hScaled hs hOne
  have hBudget : GeneralPaperBoundedQuotient.heightBudget (A+B) 1 depth≤GeneralPaperBoundedQuotient.heightBudget R 1 R := by
    unfold GeneralPaperBoundedQuotient.heightBudget
    omega
  have hRecord' := hRecord.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hBudget) 1)) _)
  have hRaw : raw.1=(GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth) := GeneralPaperBoundedQuotient.run_data _ _ _ _ _
  have hq : raw.1.quotient≤N := by rw [hRaw]; exact GeneralPaperInitializerRoundingBits.quotient_le N depth hN hCap u hu
  have hNatural := (GeneralPaperBasisDivideBits.nat_height raw.1.quotient).mono (binaryWordWidth_mono hq)
  have hOut := hNatural.div hn
  have hData : result.1.2=(raw.1.quotient:ℚ)/(N:ℚ) := rfl
  have wN : natBits N≤R := by unfold natBits GeneralPaperInitializerRoundingBits.width at *; omega
  have wQ : natBits raw.1.quotient≤R := (Nat.add_le_add_left (binaryWordWidth_mono hq) 1).trans wN
  have wu : rationalWordWidth u≤R := by have h := rationalWordWidth_of_height hHeight; unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have wn : rationalWordWidth (N:ℚ)≤R := by have h := rationalWordWidth_of_height hn; unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have ws : rationalWordWidth (u*(N:ℚ))≤R := by have h := rationalWordWidth_of_height hs; unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have wq : rationalWordWidth (raw.1.quotient:ℚ)≤R := by have h := rationalWordWidth_of_height hNatural; unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have wo : rationalWordWidth result.1.2≤R := by rw [hData]; have h := rationalWordWidth_of_height hOut; unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have wOne : rationalWordWidth (1:ℚ)≤R := by have h := rationalWordWidth_of_height hOne; unfold GeneralPaperInitializerRoundingBits.width at hR; omega
  have pMul := binary_le model.rat model.monotone (fun x y => x*y) u (N:ℚ) R wu wn ws
  have pN := model.monotone wn
  have pQ := model.monotone wq
  have pDiv := binary_le model.rat model.monotone (fun x y => x/y) (raw.1.quotient:ℚ) (N:ℚ) R wq wn (by rw [←hData]; exact wo)
  have hWork := (GeneralPaperInitializerRoundingBits.work model W N depth A hN hCap u hu hHeight).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hd 1)) (Nat.add_le_add_left (model.monotone hR) W))
  change result.2≤price model W R at hWork
  have hNative : raw.1.work=12*depth+2 := by rw [hRaw]; exact GeneralPaperBoundedQuotient.run_work _ _ _
  have hShape : result.2=raw.2+binary model.rat (fun x y => x*y) u (N:ℚ)+model.rat (rationalWordWidth (N:ℚ))+
      model.rat (rationalWordWidth (raw.1.quotient:ℚ))+binary model.rat (fun x y => x/y) (raw.1.quotient:ℚ) (N:ℚ)+48*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W R)) (controls model W N depth u) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold controls at hz
    dsimp only at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    dsimp only [raw,result] at hShape hWork hNative
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W (controls model W N depth u)≤13*(natBits (metadataCap model W R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [raw,result] at wQ wq wo hRecord' pQ pDiv
  omega

end Blotto.GeneralPaperInitializerRoundingStorage

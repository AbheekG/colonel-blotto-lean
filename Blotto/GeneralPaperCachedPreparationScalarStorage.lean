import Blotto.GeneralPaperPreparedPairReferenceContract
import Blotto.GeneralPaperCachedBitSourcePair

/-! Actual once-only proxy decoding and cached Shared assembly. These are
scalar activation frames: the calling owner retains the complete borrowed
cache, weights and returned Shared records. Primitive scratch is the sum
of the fixed six or eleven reached scalar charges, never child work. -/
namespace Blotto.GeneralPaperCachedPreparationScalarStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def decodeWidth (B : ℕ) : ℕ := 1+2*binaryWordWidth B

def decodePrice (model : RationalCostModel) (W B : ℕ) : ℕ := 6*model.rat (decodeWidth B)+32*W

def decodeScratch (model : RationalCostModel) (f : Farey.Fraction) : ℕ :=
  model.rat (1+binaryWordWidth f.num)+model.rat (1+binaryWordWidth f.den)+
    model.rat (rationalWordWidth (f.num:ℚ))+model.rat (rationalWordWidth (f.den:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (f.num:ℚ) (f.den:ℚ)

def decodeCap (model : RationalCostModel) (W B : ℕ) : ℕ := B+decodePrice model W B+W+1

def decodeFrame (model : RationalCostModel) (W : ℕ) (f : Farey.Fraction) : ℕ :=
  let a := model.rat (1+binaryWordWidth f.num)
  let b := model.rat (1+binaryWordWidth f.den)
  let c := model.rat (rationalWordWidth (f.num:ℚ))
  let d := model.rat (rationalWordWidth (f.den:ℚ))
  let division := GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x/y) (f.num:ℚ) (f.den:ℚ)
  natBits f.num+natBits f.den+rationalWordWidth (f.num:ℚ)+rationalWordWidth (f.den:ℚ)+
    rationalWordWidth (GeneralPaperCachedBitSourcePair.decode model W f).1+decodeScratch model f+
    fields W [f.num,f.den,W,a,b,c,d,division,a+b,a+b+c,a+b+c+d,decodeScratch model f,32*W,
      (GeneralPaperCachedBitSourcePair.decode model W f).2,a+b+c+d+division]+128*W

def decodeProfile (model : RationalCostModel) (W B : ℕ) : ℕ :=
  2*natBits B+3*decodeWidth B+6*model.rat (decodeWidth B)+
    15*(natBits (decodeCap model W B)+W)+160*W

theorem decode_words (B : ℕ) (f : Farey.Fraction) (hn : f.num≤B) (hd : f.den≤B) :
    rationalWordWidth (f.num:ℚ)≤decodeWidth B ∧ rationalWordWidth (f.den:ℚ)≤decodeWidth B ∧
      rationalWordWidth f.value≤decodeWidth B := by
  have hN : RationalHeight (f.num:ℚ) (binaryWordWidth B) := by
    simpa only [Int.cast_natCast] using GeneralPaperBasisStageSize.int_height (f.num:ℤ) B (by simpa only [Int.natAbs_natCast] using hn)
  have hD : RationalHeight (f.den:ℚ) (binaryWordWidth B) := by
    simpa only [Int.cast_natCast] using GeneralPaperBasisStageSize.int_height (f.den:ℤ) B (by simpa only [Int.natAbs_natCast] using hd)
  have hV : RationalHeight ((f.num:ℚ)/(f.den:ℚ)) (binaryWordWidth B) := by
    simpa only [Int.cast_natCast] using RationalHeight.fraction (f.num:ℤ) f.den (binaryWordWidth B) f.den_pos
      (by simpa only [Int.natAbs_natCast] using hn.trans_lt (lt_pow_binaryWordWidth B)) (hd.trans_lt (lt_pow_binaryWordWidth B))
  exact ⟨rationalWordWidth_of_height hN,rationalWordWidth_of_height hD,rationalWordWidth_of_height hV⟩

theorem decode_bounded (model : RationalCostModel) (W B : ℕ) (f : Farey.Fraction) (hn : f.num≤B) (hd : f.den≤B) :
    decodeFrame model W f≤decodeProfile model W B ∧
      (GeneralPaperCachedBitSourcePair.decode model W f).2≤decodePrice model W B := by
  let a := model.rat (1+binaryWordWidth f.num)
  let b := model.rat (1+binaryWordWidth f.den)
  let c := model.rat (rationalWordWidth (f.num:ℚ))
  let d := model.rat (rationalWordWidth (f.den:ℚ))
  let division := GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x/y) (f.num:ℚ) (f.den:ℚ)
  have hWork := GeneralPaperCachedBitSourcePair.decode_work model W B f hn hd
  change (GeneralPaperCachedBitSourcePair.decode model W f).2≤decodePrice model W B at hWork
  have hScratch : decodeScratch model f≤6*model.rat (decodeWidth B) := by
    change decodeScratch model f+32*W≤6*model.rat (decodeWidth B)+32*W at hWork
    omega
  have hs : decodeScratch model f=a+b+c+d+division := rfl
  have hN := Nat.add_le_add_left (binaryWordWidth_mono hn) 1
  have hD := Nat.add_le_add_left (binaryWordWidth_mono hd) 1
  change natBits f.num≤natBits B at hN
  change natBits f.den≤natBits B at hD
  have hWords := decode_words B f hn hd
  have hf := fields_bound W (natBits (decodeCap model W B))
    [f.num,f.den,W,a,b,c,d,division,a+b,a+b+c,a+b+c+d,decodeScratch model f,32*W,
      (GeneralPaperCachedBitSourcePair.decode model W f).2,a+b+c+d+division] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold decodeCap decodePrice at *;omega)
  change fields W _≤15*(natBits (decodeCap model W B)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  change natBits f.num+natBits f.den+rationalWordWidth (f.num:ℚ)+rationalWordWidth (f.den:ℚ)+
    rationalWordWidth (GeneralPaperCachedBitSourcePair.decode model W f).1+decodeScratch model f+
    fields W [f.num,f.den,W,a,b,c,d,division,a+b,a+b+c,a+b+c+d,decodeScratch model f,32*W,
      (GeneralPaperCachedBitSourcePair.decode model W f).2,a+b+c+d+division]+128*W≤_
  unfold decodeProfile
  have hValue : rationalWordWidth (GeneralPaperCachedBitSourcePair.decode model W f).1≤decodeWidth B := hWords.2.2
  omega

def sharedPrice (model : RationalCostModel) (W k p : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) : ℕ :=
  192*W+5*model.rat (GeneralPaperSharedSpanPrice.width a)+6*model.rat (GeneralPaperSharedWidthPrice.width p k)

def sharedScratch (model : RationalCostModel) (k p : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) : ℕ :=
  model.rat (rationalWordWidth (a.C:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x*y) 8 (a.C:ℚ)+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x*y) 2 ((8:ℚ)*a.C)+
    GeneralPaperSharedWidthPrice.work model.rat p k

def sharedCap (model : RationalCostModel) (W k p : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) : ℕ :=
  a.C+p+k+40+sharedPrice model W k p a+W

def sharedFrame {m : ℕ} (model : RationalCostModel) (W k : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet)
    (cache : GeneralPaperMaterializedGridCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let p := cache.source.powers.format.fractionalBits
  let cast := model.rat (rationalWordWidth (a.C:ℚ))
  let mul8 := GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x*y) 8 (a.C:ℚ)
  let mul2 := GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x*y) 2 ((8:ℚ)*a.C)
  let addk := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun x y => x+y) 34 k
  let addp := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun x y => x+y) p 1
  let addlast := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun x y => x+y) (p+1) (34+k)
  rationalWordWidth (a.C:ℚ)+rationalWordWidth (8:ℚ)+rationalWordWidth ((8:ℚ)*a.C)+
    rationalWordWidth (2:ℚ)+rationalWordWidth ((2:ℚ)*(8*a.C))+sharedScratch model k p a+
    fields W [a.C,p,k,34,1,p+1,34+k,p+1+(34+k),W,cast,mul8,mul2,addk,addp,addlast,
      (GeneralPaperSharedSpanPrice.run model.rat W a).2,GeneralPaperSharedWidthPrice.work model.rat p k,
      sharedScratch model k p a,(GeneralPaperCachedSharedPreparation.fromCache model.rat W k a cache weights Bc Br).2,
      64*W,128*W,192*W,cast+mul8,cast+mul8+mul2,
      (GeneralPaperSharedSpanPrice.run model.rat W a).2+GeneralPaperSharedWidthPrice.work model.rat p k]+128*W

def sharedProfile (model : RationalCostModel) (W k p : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) : ℕ :=
  5*GeneralPaperSharedSpanPrice.width a+5*model.rat (GeneralPaperSharedSpanPrice.width a)+
    6*model.rat (GeneralPaperSharedWidthPrice.width p k)+25*(natBits (sharedCap model W k p a)+W)+160*W

theorem shared_bounded {m : ℕ} (model : RationalCostModel) (W k : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet)
    (cache : GeneralPaperMaterializedGridCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    sharedFrame model W k a cache weights Bc Br≤sharedProfile model W k cache.source.powers.format.fractionalBits a ∧
      (GeneralPaperCachedSharedPreparation.fromCache model.rat W k a cache weights Bc Br).2≤
        sharedPrice model W k cache.source.powers.format.fractionalBits a := by
  let p := cache.source.powers.format.fractionalBits
  let cast := model.rat (rationalWordWidth (a.C:ℚ))
  let mul8 := GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x*y) 8 (a.C:ℚ)
  let mul2 := GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x*y) 2 ((8:ℚ)*a.C)
  let addk := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun x y => x+y) 34 k
  let addp := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun x y => x+y) p 1
  let addlast := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun x y => x+y) (p+1) (34+k)
  have hWords := GeneralPaperSharedSpanPrice.widths a
  have hSpan := GeneralPaperSharedSpanPrice.work model.rat model.monotone W a
  have hWidth := GeneralPaperSharedWidthPrice.work_le model.rat model.monotone p k
  have hWork := GeneralPaperCachedSharedPreparation.work model.rat model.monotone W k a cache weights Bc Br
  change (GeneralPaperCachedSharedPreparation.fromCache model.rat W k a cache weights Bc Br).2≤sharedPrice model W k p a at hWork
  have hs : sharedScratch model k p a=cast+mul8+mul2+(addk+addp+addlast) := rfl
  have hspan : (GeneralPaperSharedSpanPrice.run model.rat W a).2=cast+mul8+mul2+64*W := rfl
  have hwidth : GeneralPaperSharedWidthPrice.work model.rat p k=addk+addp+addlast := rfl
  have hScratch : sharedScratch model k p a≤5*model.rat (GeneralPaperSharedSpanPrice.width a)+
      6*model.rat (GeneralPaperSharedWidthPrice.width p k) := by omega
  have hf := fields_bound W (natBits (sharedCap model W k p a))
    [a.C,p,k,34,1,p+1,34+k,p+1+(34+k),W,cast,mul8,mul2,addk,addp,addlast,
      (GeneralPaperSharedSpanPrice.run model.rat W a).2,GeneralPaperSharedWidthPrice.work model.rat p k,
      sharedScratch model k p a,(GeneralPaperCachedSharedPreparation.fromCache model.rat W k a cache weights Bc Br).2,
      64*W,128*W,192*W,cast+mul8,cast+mul8+mul2,
      (GeneralPaperSharedSpanPrice.run model.rat W a).2+GeneralPaperSharedWidthPrice.work model.rat p k] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold sharedCap sharedPrice at *;omega)
  change fields W _≤25*(natBits (sharedCap model W k p a)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  change rationalWordWidth (a.C:ℚ)+rationalWordWidth (8:ℚ)+rationalWordWidth ((8:ℚ)*a.C)+
    rationalWordWidth (2:ℚ)+rationalWordWidth ((2:ℚ)*(8*a.C))+sharedScratch model k p a+
    fields W [a.C,p,k,34,1,p+1,34+k,p+1+(34+k),W,cast,mul8,mul2,addk,addp,addlast,
      (GeneralPaperSharedSpanPrice.run model.rat W a).2,GeneralPaperSharedWidthPrice.work model.rat p k,
      sharedScratch model k p a,(GeneralPaperCachedSharedPreparation.fromCache model.rat W k a cache weights Bc Br).2,
      64*W,128*W,192*W,cast+mul8,cast+mul8+mul2,
      (GeneralPaperSharedSpanPrice.run model.rat W a).2+GeneralPaperSharedWidthPrice.work model.rat p k]+128*W≤_
  change _≤5*GeneralPaperSharedSpanPrice.width a+5*model.rat (GeneralPaperSharedSpanPrice.width a)+
    6*model.rat (GeneralPaperSharedWidthPrice.width p k)+25*(natBits (sharedCap model W k p a)+W)+160*W
  omega

end Blotto.GeneralPaperCachedPreparationScalarStorage

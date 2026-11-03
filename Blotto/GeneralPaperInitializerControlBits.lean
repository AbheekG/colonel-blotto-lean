import Blotto.GeneralPaperInitializerControlSize

/-! Complete bit prices for initializer-control construction. The literal
shared products and one doubling ceiling are followed by all rational
casts/divisions/subtraction and the signed auxiliary-numerator conversion/
subtraction. Input/output words use their actual sizes. No parameter-price,
operand-height, reciprocal or doubling-depth oracle is supplied.
-/
namespace Blotto.GeneralPaperInitializerControlBits
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def naturalWork (model : RationalCostModel) (m H p q : ℕ) (c : GeneralPaperInitializerProducts.Products) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 4 m+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.first H+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.shared p+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.third q+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.chosen c.chosen+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c.shared c.square

theorem natural_work (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) :
    naturalWork model m H p q (GeneralPaperInitializerProducts.run m H p q reciprocal)≤
      12*model.rat (GeneralPaperInitializerControlSize.width m H p q) := by
  obtain ⟨h4,hm,hH,hp,hq,h1,h2,h3,hN,hc,hs,hb⟩ := GeneralPaperInitializerControlSize.natural_words m H p q reciprocal
  let L := GeneralPaperInitializerControlSize.width m H p q
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  have w1 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) 4 m L h4 hm h1
  have w2 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) c.first H L h1 hH h2
  have w3 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) c.shared p L h2 hp h3
  have w4 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) c.third q L h3 hq hN
  have w5 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) c.chosen c.chosen L hc hc hs
  have w6 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) c.shared c.square L h2 hs hb
  change naturalWork model m H p q c≤12*model.rat L
  unfold naturalWork
  omega

def casts (model : RationalCostModel) (m p q : ℕ) (c : GeneralPaperInitializerProducts.Products) : ℕ :=
  model.rat (rationalWordWidth (m:ℚ))+model.rat (rationalWordWidth (p:ℚ))+
  model.rat (rationalWordWidth (q:ℚ))+model.rat (rationalWordWidth (c.N:ℚ))+
  model.rat (GeneralPaperIntegerPrimitivePrice.word (c.scaled:ℤ))+model.rat (GeneralPaperIntegerPrimitivePrice.word (m:ℤ))

theorem casts_work (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) :
    casts model m p q (GeneralPaperInitializerProducts.run m H p q reciprocal)≤
      6*model.rat (GeneralPaperInitializerControlSize.width m H p q) := by
  obtain ⟨hm,hp,hq,hn,_,_,_⟩ := GeneralPaperInitializerControlSize.rational_words m H p q reciprocal
  obtain ⟨hb,hi,_⟩ := GeneralPaperInitializerControlSize.signed_words m H p q reciprocal
  have w1 := model.monotone hm
  have w2 := model.monotone hp
  have w3 := model.monotone hq
  have w4 := model.monotone hn
  have w5 := model.monotone hb
  have w6 := model.monotone hi
  unfold casts
  omega

def rationalWork (model : RationalCostModel) (m p q : ℕ) (reciprocal : Bool) (c : GeneralPaperInitializerProducts.Products) : ℕ :=
  (if reciprocal then GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (q:ℚ) (p:ℚ)
    else GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (p:ℚ) (q:ℚ))+
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (m:ℚ) (c.N:ℚ)+
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a-b)
    (GeneralPaperInitializerControlWork.beta p q reciprocal) ((m:ℚ)/c.N)

theorem rational_work (model : RationalCostModel) (m H p q : ℕ) (reciprocal : Bool) :
    rationalWork model m p q reciprocal (GeneralPaperInitializerProducts.run m H p q reciprocal)≤
      6*model.rat (GeneralPaperInitializerControlSize.width m H p q) := by
  obtain ⟨hm,hp,hq,hn,hb,ht,ha⟩ := GeneralPaperInitializerControlSize.rational_words m H p q reciprocal
  let L := GeneralPaperInitializerControlSize.width m H p q
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  have wr :
      (if reciprocal then GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (q:ℚ) (p:ℚ)
        else GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (p:ℚ) (q:ℚ))≤2*model.rat L := by
    cases reciprocal with
    | false =>
      exact GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (p:ℚ) (q:ℚ) L hp hq hb
    | true =>
      exact GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (q:ℚ) (p:ℚ) L hq hp hb
  have wt := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (m:ℚ) (c.N:ℚ) L hm hn ht
  have wa := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b)
    (GeneralPaperInitializerControlWork.beta p q reciprocal) ((m:ℚ)/c.N) L hb ht ha
  change rationalWork model m p q reciprocal c≤6*model.rat L
  unfold rationalWork
  omega

def run (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) :
    (GeneralPaperInitializerParameters.Parameters × ℤ) × ℕ :=
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  let scale := GeneralPaperPowerCeilingBits.run model.rat W c.N
  let result := GeneralPaperInitializerControlWork.assemble m p q reciprocal c scale.1
  (result,scale.2+naturalWork model m H p q c+casts model m p q c+rationalWork model m p q reciprocal c+
    GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a-b) (c.scaled:ℤ) (m:ℤ)+128*W)

theorem data (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) :
    (run model W m H p q reciprocal).1=(GeneralPaperInitializerControlWork.run m H p q reciprocal).1 := by
  simp only [run,GeneralPaperInitializerControlWork.run,GeneralPaperPowerCeilingBits.data]

def profile (model : RationalCostModel) (W m H p q : ℕ) : ℕ :=
  1024*(binaryWordWidth (4*m*H*p*q)+1)*(W+model.rat (GeneralPaperInitializerControlSize.width m H p q))

theorem work (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool) :
    (run model W m H p q reciprocal).2≤profile model W m H p q := by
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  let L := GeneralPaperInitializerControlSize.width m H p q
  let P := model.rat L
  have hc := GeneralPaperPowerCeilingBits.work model.rat model.monotone W c.N
  have hL := model.monotone (GeneralPaperInitializerControlSize.ceiling_width m H p q reciprocal)
  have hc' : (GeneralPaperPowerCeilingBits.run model.rat W c.N).2≤64*(binaryWordWidth c.N+1)*(W+P) :=
    hc.trans (Nat.mul_le_mul_left (64*(binaryWordWidth c.N+1)) (Nat.add_le_add_left hL W))
  have hn := natural_work model m H p q reciprocal
  have hCast := casts_work model m H p q reciprocal
  have hRat := rational_work model m H p q reciprocal
  obtain ⟨hB,hM,hOut⟩ := GeneralPaperInitializerControlSize.signed_words m H p q reciprocal
  have hInt := GeneralPaperIntegerWordPrice.integer_binary model.rat model.monotone (fun a b => a-b) (c.scaled:ℤ) (m:ℤ) L hB hM hOut
  change naturalWork model m H p q c≤12*P at hn
  change casts model m p q c≤6*P at hCast
  change rationalWork model m p q reciprocal c≤6*P at hRat
  change GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a-b) (c.scaled:ℤ) (m:ℤ)≤2*P at hInt
  dsimp only [run]
  change (GeneralPaperPowerCeilingBits.run model.rat W c.N).2+naturalWork model m H p q c+casts model m p q c+
    rationalWork model m p q reciprocal c+GeneralPaperIntegerPrimitivePrice.binary model.rat (fun a b => a-b) (c.scaled:ℤ) (m:ℤ)+128*W≤_
  change _≤1024*(binaryWordWidth c.N+1)*(W+P)
  nlinarith only [hc',hn,hCast,hRat,hInt,Nat.zero_le (binaryWordWidth c.N*W),Nat.zero_le (binaryWordWidth c.N*P)]

theorem positive_work (model : RationalCostModel) (W m H p q : ℕ) (reciprocal : Bool)
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    (run model W m H p q reciprocal).2≤1024*(binaryWordWidth (4*m*H*p*q)+1)*
      (W+model.rat (96+64*binaryWordWidth (4*m*H*p*q))) := by
  have hw := work model W m H p q reciprocal
  have hp := model.monotone (GeneralPaperInitializerControlSize.positive_width m H p q hm hH hp hq)
  exact hw.trans (Nat.mul_le_mul_left (1024*(binaryWordWidth (4*m*H*p*q)+1)) (Nat.add_le_add_left hp W))

end Blotto.GeneralPaperInitializerControlBits

import Blotto.GeneralPaperInitializerControlWork

/-! Uniform widths for every literal initializer-control operand/result.
Unsigned raw products, all rational casts/divisions/subtraction, and the
signed auxiliary numerator are bounded before cancellation. The original
unreduced p,q remain valid; no value-height certificate is supplied.
-/
namespace Blotto.GeneralPaperInitializerControlSize
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def width (m H p q : ℕ) : ℕ := 32+16*GeneralPaperInitializerProducts.width m H p q

theorem natural_words (m H p q : ℕ) (reciprocal : Bool) :
    let c := GeneralPaperInitializerProducts.run m H p q reciprocal
    let L := width m H p q
    1+binaryWordWidth 4≤L ∧ 1+binaryWordWidth m≤L ∧ 1+binaryWordWidth H≤L ∧
    1+binaryWordWidth p≤L ∧ 1+binaryWordWidth q≤L ∧ 1+binaryWordWidth c.first≤L ∧
    1+binaryWordWidth c.shared≤L ∧ 1+binaryWordWidth c.third≤L ∧ 1+binaryWordWidth c.N≤L ∧
    1+binaryWordWidth c.chosen≤L ∧ 1+binaryWordWidth c.square≤L ∧ 1+binaryWordWidth c.scaled≤L := by
  have hh := GeneralPaperInitializerProducts.words m H p q reciprocal
  dsimp only at hh ⊢
  have h4 : binaryWordWidth 4=3 := by decide
  unfold width
  omega

theorem rational_heights (m H p q : ℕ) (reciprocal : Bool) :
    let c := GeneralPaperInitializerProducts.run m H p q reciprocal
    let F := GeneralPaperInitializerProducts.width m H p q
    RationalHeight (m:ℚ) F ∧ RationalHeight (p:ℚ) F ∧ RationalHeight (q:ℚ) F ∧ RationalHeight (c.N:ℚ) F ∧
    RationalHeight (GeneralPaperInitializerControlWork.beta p q reciprocal) (2*F) ∧
    RationalHeight ((m:ℚ)/c.N) (2*F) ∧
    RationalHeight (GeneralPaperInitializerControlWork.beta p q reciprocal-(m:ℚ)/c.N) (4*F+1) := by
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  let F := GeneralPaperInitializerProducts.width m H p q
  have hw := GeneralPaperInitializerProducts.words m H p q reciprocal
  dsimp only at hw
  have hm : RationalHeight (m:ℚ) F := (GeneralPaperBasisDivideBits.nat_height m).mono hw.1
  have hp : RationalHeight (p:ℚ) F := (GeneralPaperBasisDivideBits.nat_height p).mono hw.2.2.1
  have hq : RationalHeight (q:ℚ) F := (GeneralPaperBasisDivideBits.nat_height q).mono hw.2.2.2.1
  have hn : RationalHeight (c.N:ℚ) F := (GeneralPaperBasisDivideBits.nat_height c.N).mono hw.2.2.2.2.2.2.2.1
  have hb : RationalHeight (GeneralPaperInitializerControlWork.beta p q reciprocal) (2*F) := by
    cases reciprocal
    · simpa only [GeneralPaperInitializerControlWork.beta,Bool.false_eq_true,ite_false,two_mul] using hp.div hq
    · simpa only [GeneralPaperInitializerControlWork.beta,ite_true,two_mul] using hq.div hp
  have ht : RationalHeight ((m:ℚ)/c.N) (2*F) := by simpa only [two_mul] using hm.div hn
  have ha : RationalHeight (GeneralPaperInitializerControlWork.beta p q reciprocal-(m:ℚ)/c.N) (4*F+1) :=
    (hb.sub ht).mono (by omega)
  exact ⟨hm,hp,hq,hn,hb,ht,ha⟩

theorem rational_words (m H p q : ℕ) (reciprocal : Bool) :
    let c := GeneralPaperInitializerProducts.run m H p q reciprocal
    let L := width m H p q
    rationalWordWidth (m:ℚ)≤L ∧ rationalWordWidth (p:ℚ)≤L ∧ rationalWordWidth (q:ℚ)≤L ∧ rationalWordWidth (c.N:ℚ)≤L ∧
    rationalWordWidth (GeneralPaperInitializerControlWork.beta p q reciprocal)≤L ∧ rationalWordWidth ((m:ℚ)/c.N)≤L ∧
    rationalWordWidth (GeneralPaperInitializerControlWork.beta p q reciprocal-(m:ℚ)/c.N)≤L := by
  obtain ⟨hm,hp,hq,hn,hb,ht,ha⟩ := rational_heights m H p q reciprocal
  dsimp only
  refine ⟨(rationalWordWidth_of_height hm).trans ?_,(rationalWordWidth_of_height hp).trans ?_,
    (rationalWordWidth_of_height hq).trans ?_,(rationalWordWidth_of_height hn).trans ?_,
    (rationalWordWidth_of_height hb).trans ?_,(rationalWordWidth_of_height ht).trans ?_,
    (rationalWordWidth_of_height ha).trans ?_⟩ <;> unfold width <;> omega

theorem signed_words (m H p q : ℕ) (reciprocal : Bool) :
    let c := GeneralPaperInitializerProducts.run m H p q reciprocal
    let L := width m H p q
    GeneralPaperIntegerPrimitivePrice.word (c.scaled:ℤ)≤L ∧ GeneralPaperIntegerPrimitivePrice.word (m:ℤ)≤L ∧
    GeneralPaperIntegerPrimitivePrice.word ((c.scaled:ℤ)-(m:ℤ))≤L := by
  let c := GeneralPaperInitializerProducts.run m H p q reciprocal
  let F := GeneralPaperInitializerProducts.width m H p q
  have hw := GeneralPaperInitializerProducts.words m H p q reciprocal
  dsimp only at hw
  have hm : ((c.scaled:ℤ)-(m:ℤ)).natAbs≤c.scaled+m := by
    simpa only [←sub_eq_add_neg,Int.natAbs_natCast,Int.natAbs_neg] using Int.natAbs_add_le (c.scaled:ℤ) (-(m:ℤ))
  have ha := binaryWordWidth_mono hm
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add c.scaled m
  dsimp only [c,F] at *
  unfold GeneralPaperIntegerPrimitivePrice.word
  simp only [Int.natAbs_natCast]
  unfold width
  omega

theorem ceiling_width (m H p q : ℕ) (reciprocal : Bool) :
    1+binaryWordWidth (2*((GeneralPaperInitializerProducts.run m H p q reciprocal).N+1))≤width m H p q := by
  have hw := GeneralPaperInitializerProducts.words m H p q reciprocal
  dsimp only at hw
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (GeneralPaperInitializerProducts.run m H p q reciprocal).N 1
  have hm := binaryWordWidth_mul 2 ((GeneralPaperInitializerProducts.run m H p q reciprocal).N+1)
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  unfold width
  omega

theorem positive_factors (m H p q : ℕ) (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    m≤4*m*H*p*q ∧ H≤4*m*H*p*q ∧ p≤4*m*H*p*q ∧ q≤4*m*H*p*q := by
  have right (a b : ℕ) (hb : 0<b) : a≤a*b := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a (show 1≤b by omega)
  have left (a b : ℕ) (ha : 0<a) : b≤a*b := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right b (show 1≤a by omega)
  have ha := right (4*m) H hH
  have hb := right (4*m*H) p hp
  have hc := right (4*m*H*p) q hq
  exact ⟨(show m≤4*m by omega).trans (ha.trans (hb.trans hc)),
    (left (4*m) H (by positivity)).trans (hb.trans hc),
    (left (4*m*H) p (by positivity)).trans hc,left (4*m*H*p) q (by positivity)⟩

theorem positive_width (m H p q : ℕ) (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    width m H p q≤96+64*binaryWordWidth (4*m*H*p*q) := by
  obtain ⟨hmN,hHN,hpN,hqN⟩ := positive_factors m H p q hm hH hp hq
  have wm := binaryWordWidth_mono hmN
  have wH := binaryWordWidth_mono hHN
  have wp := binaryWordWidth_mono hpN
  have wq := binaryWordWidth_mono hqN
  unfold width GeneralPaperInitializerProducts.width
  omega

end Blotto.GeneralPaperInitializerControlSize

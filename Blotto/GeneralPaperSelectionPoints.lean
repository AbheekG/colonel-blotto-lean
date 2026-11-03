import Blotto.GeneralPaperCachedRootQueryBits

/-! Retain all three rational cell points once for the constant-size proxy
selection. Natural upper/midpoint numerators and the doubled denominator
are also retained, avoiding repeated arithmetic in the branch records.
-/
namespace Blotto.GeneralPaperSelectionPoints
set_option autoImplicit false

structure Points where
  upperNum : ℕ
  midNum : ℕ
  midDen : ℕ
  lower : ℚ
  upper : ℚ
  middle : ℚ

def prepare (Q j : ℕ) : Points :=
  let scale : ℚ := Q
  let upperNum := j+1
  let midNum := 2*j+1
  let midDen := 2*Q
  ⟨upperNum,midNum,midDen,(j:ℚ)/scale,(upperNum:ℚ)/scale,(midNum:ℚ)/(midDen:ℚ)⟩

theorem data (Q j : ℕ) :
    (prepare Q j).upperNum=j+1 ∧ (prepare Q j).midNum=2*j+1 ∧ (prepare Q j).midDen=2*Q ∧
    (prepare Q j).lower=GeneralPaperBucketGeometry.lower Q j ∧
    (prepare Q j).upper=GeneralPaperBucketGeometry.upper Q j ∧
    (prepare Q j).middle=GeneralPaperBucketGeometry.midpoint Q j := by
  simp only [prepare,GeneralPaperBucketGeometry.lower,GeneralPaperBucketGeometry.upper,
    GeneralPaperBucketGeometry.midpoint,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,and_self]

def width (Q B : ℕ) : ℕ := 32+4*B+16*binaryWordWidth Q

theorem natural_words (Q j B : ℕ) (_hQ : 0<Q) (hj : j<Q) :
    let p := prepare Q j
    let L := width Q B
    1+binaryWordWidth 1≤L ∧ 1+binaryWordWidth 2≤L ∧ 1+binaryWordWidth j≤L ∧
    1+binaryWordWidth Q≤L ∧ 1+binaryWordWidth p.upperNum≤L ∧
    1+binaryWordWidth (2*j)≤L ∧ 1+binaryWordWidth p.midNum≤L ∧ 1+binaryWordWidth p.midDen≤L := by
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have hjW := binaryWordWidth_mono (show j≤Q by omega)
  have huW := binaryWordWidth_mono (show j+1≤Q by omega)
  have hmW := binaryWordWidth_mono (show 2*j+1≤2*Q by omega)
  have hdW := binaryWordWidth_mul 2 Q
  have htW := binaryWordWidth_mono (show 2*j≤2*Q by omega)
  dsimp only [prepare]
  unfold width
  omega

theorem cast_height (Q x : ℕ) (hx : x≤2*Q) :
    RationalHeight (x:ℚ) (binaryWordWidth Q+2) := by
  have hw := binaryWordWidth_mul 2 Q
  have h2 : binaryWordWidth 2=2 := by decide
  exact (GeneralPaperBasisDivideBits.nat_height x).mono ((binaryWordWidth_mono hx).trans (by omega))

theorem rational_words (Q j B : ℕ) (b : ℚ) (hQ : 0<Q) (hj : j<Q) (hB : RationalHeight b B) :
    let p := prepare Q j
    let L := width Q B
    rationalWordWidth b≤L ∧ rationalWordWidth (j:ℚ)≤L ∧ rationalWordWidth (Q:ℚ)≤L ∧
    rationalWordWidth (p.upperNum:ℚ)≤L ∧ rationalWordWidth (p.midNum:ℚ)≤L ∧
    rationalWordWidth (p.midDen:ℚ)≤L ∧ rationalWordWidth p.lower≤L ∧
    rationalWordWidth p.upper≤L ∧ rationalWordWidth p.middle≤L := by
  have hjH := cast_height Q j (by omega)
  have hQH := cast_height Q Q (by omega)
  have huH := cast_height Q (j+1) (by omega)
  have hnH := cast_height Q (2*j+1) (by omega)
  have hdH := cast_height Q (2*Q) (by omega)
  have hlH := hjH.div hQH
  have hhH := huH.div hQH
  have hmH := hnH.div hdH
  dsimp only [prepare]
  refine ⟨(rationalWordWidth_of_height hB).trans ?_,(rationalWordWidth_of_height hjH).trans ?_,
    (rationalWordWidth_of_height hQH).trans ?_,(rationalWordWidth_of_height huH).trans ?_,
    (rationalWordWidth_of_height hnH).trans ?_,(rationalWordWidth_of_height hdH).trans ?_,
    (rationalWordWidth_of_height hlH).trans ?_,(rationalWordWidth_of_height hhH).trans ?_,
    (rationalWordWidth_of_height hmH).trans ?_⟩ <;> unfold width <;> omega

theorem root_words (Q B : ℕ) (f : Farey.Fraction) (hn : f.num≤2*Q) (hd : f.den≤2*Q) :
    rationalWordWidth (f.num:ℚ)≤width Q B ∧ rationalWordWidth (f.den:ℚ)≤width Q B ∧
    rationalWordWidth f.value≤width Q B := by
  have hnH := cast_height Q f.num hn
  have hdH := cast_height Q f.den hd
  have hvH := hnH.div hdH
  refine ⟨(rationalWordWidth_of_height hnH).trans ?_,(rationalWordWidth_of_height hdH).trans ?_,
    (rationalWordWidth_of_height hvH).trans ?_⟩ <;> unfold width <;> omega

end Blotto.GeneralPaperSelectionPoints

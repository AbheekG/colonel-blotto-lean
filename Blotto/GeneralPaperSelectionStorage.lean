import Blotto.GeneralPaperPrecallCacheStorage
import Blotto.GeneralPaperSelectionBits

/-! Literal native fraction, option, selection-point and selected records.
The output payload uses only the constructed grid/root, independently of the
original budget's rational height. That height remains in comparison scratch. -/
namespace Blotto.GeneralPaperSelectionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperProxySelection
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def fraction (W : ℕ) (f : Farey.Fraction) : ℕ := fields W [f.num,f.den]+32*W

def root (W : ℕ) : Option Farey.Fraction → ℕ
  | none => 32*W
  | some f => fraction W f+32*W

def selected (W : ℕ) (s : Selected) : ℕ :=
  fraction W s.proxy+rationalWordWidth s.endpoint+natBits s.work+66*W

def points (W : ℕ) (p : GeneralPaperSelectionPoints.Points) : ℕ :=
  fields W [p.upperNum,p.midNum,p.midDen]+
    rationalWordWidth p.lower+rationalWordWidth p.upper+rationalWordWidth p.middle+64*W

theorem natural (Q x : ℕ) (hx : x≤2*Q) : natBits x≤GeneralPaperSelectionPoints.width Q 0 := by
  have hm := binaryWordWidth_mul 2 Q
  have hw := binaryWordWidth_mono hx
  have h2 : binaryWordWidth 2=2 := by decide
  unfold natBits GeneralPaperSelectionPoints.width
  omega

theorem fraction_bound (W P : ℕ) (f : Farey.Fraction)
    (hn : natBits f.num≤P) (hd : natBits f.den≤P) : fraction W f≤2*P+66*W := by
  have h := fields_bound W P [f.num,f.den] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption)
  change _≤2*(P+W)+32*W at h
  unfold fraction
  omega

theorem root_bound (W Q : ℕ) (r : Option Farey.Fraction)
    (hr : ∀ f,r=some f → f.num≤2*Q ∧ f.den≤2*Q) :
    root W r≤2*GeneralPaperSelectionPoints.width Q 0+98*W := by
  cases he : r with
  | none => change 32*W≤_; omega
  | some f =>
    have hf := hr f he
    have h := fraction_bound W _ f (natural Q f.num hf.1) (natural Q f.den hf.2)
    change fraction W f+32*W≤_
    omega

theorem point_record (W Q j : ℕ) (hQ : 0<Q) (hj : j<Q) :
    points W (GeneralPaperSelectionPoints.prepare Q j)≤6*GeneralPaperSelectionPoints.width Q 0+99*W := by
  have hn := GeneralPaperSelectionPoints.natural_words Q j 0 hQ hj
  have hfields := fields_bound W (GeneralPaperSelectionPoints.width Q 0)
    [(GeneralPaperSelectionPoints.prepare Q j).upperNum,(GeneralPaperSelectionPoints.prepare Q j).midNum,
      (GeneralPaperSelectionPoints.prepare Q j).midDen] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl
      · exact hn.2.2.2.2.1
      · exact hn.2.2.2.2.2.2.1
      · exact hn.2.2.2.2.2.2.2)
  -- The three cell rationals have no dependence on the queried budget.
  have hjH := GeneralPaperSelectionPoints.cast_height Q j (by omega)
  have hQH := GeneralPaperSelectionPoints.cast_height Q Q (by omega)
  have huH := GeneralPaperSelectionPoints.cast_height Q (j+1) (by omega)
  have hmH := GeneralPaperSelectionPoints.cast_height Q (2*j+1) (by omega)
  have hdH := GeneralPaperSelectionPoints.cast_height Q (2*Q) (by omega)
  have hl := rationalWordWidth_of_height (hjH.div hQH)
  have hu := rationalWordWidth_of_height (huH.div hQH)
  have hm := rationalWordWidth_of_height (hmH.div hdH)
  change _≤3*(GeneralPaperSelectionPoints.width Q 0+W)+32*W at hfields
  unfold points
  dsimp only [GeneralPaperSelectionPoints.prepare] at hfields ⊢
  unfold GeneralPaperSelectionPoints.width at *
  omega

theorem selected_bound (W Q j : ℕ) (hQ : 0<Q) (hj : j<Q) (b : ℝ) (r : Option Farey.Fraction)
    (hr : ∀ f,r=some f → f.num≤2*Q ∧ f.den≤2*Q) :
    selected W (select Q j hQ b r)≤4*GeneralPaperSelectionPoints.width Q 0+132*W := by
  let P := GeneralPaperSelectionPoints.width Q 0
  have hfrac (f : Farey.Fraction) (hn : f.num≤2*Q) (hd : f.den≤2*Q) :
      fraction W f≤2*P+66*W := fraction_bound W P f (natural Q f.num hn) (natural Q f.den hd)
  have hl := hfrac ⟨j,Q,hQ⟩ (by dsimp only; omega) (by dsimp only; omega)
  have hu := hfrac ⟨j+1,Q,hQ⟩ (by dsimp only; omega) (by dsimp only; omega)
  have hm := hfrac ⟨2*j+1,2*Q,by omega⟩ (by dsimp only; omega) (by dsimp only; omega)
  have hjH := GeneralPaperSelectionPoints.cast_height Q j (by omega)
  have hQH := GeneralPaperSelectionPoints.cast_height Q Q (by omega)
  have huH := GeneralPaperSelectionPoints.cast_height Q (j+1) (by omega)
  have hlV := rationalWordWidth_of_height (hjH.div hQH)
  have huV := rationalWordWidth_of_height (huH.div hQH)
  have hlV' : rationalWordWidth (GeneralPaperBucketGeometry.lower Q j)≤P := by
    change rationalWordWidth ((j:ℚ)/(Q:ℚ))≤_
    dsimp [P,GeneralPaperSelectionPoints.width]
    omega
  have huV' : rationalWordWidth (GeneralPaperBucketGeometry.upper Q j)≤P := by
    have hv : rationalWordWidth (((j+1:ℕ):ℚ)/(Q:ℚ))≤P := by
      dsimp [P,GeneralPaperSelectionPoints.width]
      omega
    simpa only [GeneralPaperBucketGeometry.upper,Nat.cast_add,Nat.cast_one] using hv
  have hzero : rationalWordWidth (0:ℚ)≤P := by
    have hz : rationalWordWidth (0:ℚ)=3 := by decide
    dsimp [P,GeneralPaperSelectionPoints.width]
    omega
  have hwork (n : ℕ) (hn : n≤48) : natBits n≤P := by
    have hw := binaryWordWidth_mono hn
    have h48 : binaryWordWidth 48=6 := by decide
    dsimp [P,GeneralPaperSelectionPoints.width]
    unfold natBits
    omega
  unfold select
  split
  · change selected W ⟨⟨j,Q,hQ⟩,none,0,24⟩≤_
    have hw := hwork 24 (by decide)
    unfold selected
    dsimp only
    change _≤4*P+132*W
    omega
  · cases he : r with
    | none =>
      dsimp only
      split_ifs <;> unfold selected <;> dsimp only
      · have hw := hwork 40 (by decide); change _≤4*P+132*W; omega
      · have hw := hwork 48 (by decide); change _≤4*P+132*W; omega
      · have hw := hwork 48 (by decide); change _≤4*P+132*W; omega
    | some f =>
      have hf := hr f he
      have hff := hfrac f hf.1 hf.2
      have hv := (GeneralPaperSelectionPoints.root_words Q 0 f hf.1 hf.2).2.2
      change rationalWordWidth f.value≤P at hv
      dsimp only
      split_ifs <;> unfold selected <;> dsimp only
      · have hw := hwork 32 (by decide); change _≤4*P+132*W; omega
      · have hw := hwork 40 (by decide); change _≤4*P+132*W; omega
      · have hw := hwork 40 (by decide); change _≤4*P+132*W; omega

end Blotto.GeneralPaperSelectionStorage

import Blotto.GeneralPaperEpochCDF

/-! The ordered-variation calculation for the selected loss formulas.
Rounded CDF components must be monotone, bounded in [0,1], and retain exact
one at the last code. Both signs are concatenated before normalization.
-/
namespace Blotto.GeneralPaperLossVariation
open scoped BigOperators Classical
open GeneralPaperOrderedVariation
set_option autoImplicit false

theorem monotone_variation (f : ℕ → ℝ) (last : ℕ) (h : ∀ i<last, f i≤f (i+1)) :
    variation f last=f last-f 0 := by
  induction last with
  | zero => simp [variation]
  | succ last ih =>
    unfold variation
    rw [Finset.sum_range_succ]
    change variation f last+|f (last+1)-f last|=f (last+1)-f 0
    rw [ih (fun i hi => h i (by omega)),abs_of_nonneg (sub_nonneg.mpr (h last (by omega)))]
    ring

theorem antitone_variation (f : ℕ → ℝ) (last : ℕ) (h : ∀ i<last, f (i+1)≤f i) :
    variation f last=f 0-f last := by
  have he := monotone_variation (fun i => -f i) last (fun i hi => by linarith [h i hi])
  have hv := variation_scale_shift f (-1) 0 last
  simp only [neg_mul,one_mul,add_zero,abs_neg,abs_one] at hv
  rw [hv] at he
  linarith

theorem subtract_variation (f g : ℕ → ℝ) (last : ℕ) :
    variation (fun i => f i-g i) last≤variation f last+variation g last := by
  have he := variation_add f (fun i => -g i) last
  have hv := variation_scale_shift g (-1) 0 last
  simp only [neg_mul,one_mul,add_zero,abs_neg,abs_one] at hv
  rw [hv] at he
  simpa only [sub_eq_add_neg,one_mul] using he

theorem unit_monotone_variation (f : ℕ → ℝ) (last : ℕ)
    (h : ∀ i<last, f i≤f (i+1)) (h0 : 0≤f 0) (h1 : f last≤1) : variation f last≤1 := by
  rw [monotone_variation f last h]
  linarith

theorem unit_antitone_variation (f : ℕ → ℝ) (last : ℕ)
    (h : ∀ i<last, f (i+1)≤f i) (h0 : f 0≤1) (h1 : 0≤f last) : variation f last≤1 := by
  rw [antitone_variation f last h]
  linarith

theorem half_cdf_tail_variation (lo hi pos neg : ℕ → ℝ) (last : ℕ) (shift : ℝ)
    (hlo : variation lo last≤1) (hhi : variation hi last≤1)
    (hp : variation pos last≤1) (hn : variation neg last≤1) :
    variation (fun i => shift-(lo i+hi i)/2+(pos i-neg i)) last≤4 := by
  have hHalf := variation_add lo hi last
  have hScale := variation_scale_shift (fun i => lo i+hi i) (-1/2) shift last
  have hTail := subtract_variation pos neg last
  have hSum := variation_add (fun i => (-1/2)*(lo i+hi i)+shift) (fun i => pos i-neg i) last
  have hFun : (fun i => (-1/2)*(lo i+hi i)+shift+(pos i-neg i))=
    (fun i => shift-(lo i+hi i)/2+(pos i-neg i)) := by funext i; ring
  rw [hFun,hScale] at hSum
  norm_num at hSum
  linarith

def indicator (bid code : ℕ) : ℝ := if bid≤code then 1 else 0

theorem indicator_monotone (bid : ℕ) : Monotone (indicator bid) := by
  intro a b hab
  unfold indicator
  split_ifs <;> norm_num <;> omega

theorem indicator_variation (bid last : ℕ) (hBid : bid≤last) :
    variation (indicator bid) last=1-indicator bid 0 := by
  rw [monotone_variation _ _ (fun i _ => indicator_monotone bid (by omega))]
  simp only [indicator,if_pos hBid]

def rowDifference (cdf : ℕ → ℝ) (bid : ℕ) : ℕ → ℝ := fun i => indicator bid i-cdf i

theorem row_difference_endpoint (cdf : ℕ → ℝ) (bid last : ℕ) (hBid : bid≤last) (hEnd : cdf last=1) :
    rowDifference cdf bid last=0 := by simp [rowDifference,indicator,hBid,hEnd]

theorem row_difference_variation (cdf : ℕ → ℝ) (bid last : ℕ) (hBid : bid≤last)
    (hMono : ∀ i<last, cdf i≤cdf (i+1)) (h0 : 0≤cdf 0) (h01 : cdf 0≤1) (hEnd : cdf last=1) :
    variation (rowDifference cdf bid) last≤2-|rowDifference cdf bid 0| := by
  have he := subtract_variation (indicator bid) cdf last
  rw [indicator_variation bid last hBid,monotone_variation cdf last hMono,hEnd] at he
  by_cases hz : bid=0
  · subst bid
    simp only [indicator,Nat.zero_le,if_true] at he
    have hAbs : |rowDifference cdf 0 0|=1-cdf 0 := by
      unfold rowDifference indicator
      simp only [Nat.zero_le,if_true]
      exact abs_of_nonneg (by linarith)
    rw [hAbs]
    have hFun : rowDifference cdf 0=(fun i => 1-cdf i) := by funext i; simp [rowDifference,indicator]
    rw [hFun]
    linarith
  · have hb : ¬bid≤0 := by omega
    simp only [indicator,if_neg hb] at he
    have hAbs : |rowDifference cdf bid 0|=cdf 0 := by simp [rowDifference,indicator,hb,abs_of_nonneg h0]
    rw [hAbs]
    unfold rowDifference indicator
    linarith

def signedConcatenation (g : ℕ → ℝ) (last : ℕ) (i : ℕ) : ℝ :=
  if i≤last then g i else -g (i-(last+1))

theorem signed_concatenation_variation (g : ℕ → ℝ) (last : ℕ) :
    variation (signedConcatenation g last) (2*last+1)=
      2*variation g last+|g last+g 0| := by
  have hSize : 2*last+1=(last+1)+last := by omega
  unfold variation
  rw [hSize,Finset.sum_range_add,Finset.sum_range_succ]
  have hFirst : (∑ i ∈ Finset.range last,
      |signedConcatenation g last (i+1)-signedConcatenation g last i|)=
      ∑ i ∈ Finset.range last, |g (i+1)-g i| := by
    apply Finset.sum_congr rfl
    intro i hi
    have hb := Finset.mem_range.mp hi
    simp [signedConcatenation,show i+1≤last by omega,show i≤last by omega]
  have hSecond : (∑ i ∈ Finset.range last,
      |signedConcatenation g last (last+1+i+1)-signedConcatenation g last (last+1+i)|)=
      ∑ i ∈ Finset.range last, |g (i+1)-g i| := by
    apply Finset.sum_congr rfl
    intro i _
    have h1 : ¬last+1+i+1≤last := by omega
    have h2 : ¬last+1+i≤last := by omega
    have h3 : last+1+i+1-(last+1)=i+1 := by omega
    have h4 : last+1+i-(last+1)=i := by omega
    simp only [signedConcatenation,if_neg h1,if_neg h2,h3,h4]
    rw [← abs_neg]
    congr 1
    ring
  rw [hFirst,hSecond]
  have hBoundary : |signedConcatenation g last (last+1)-signedConcatenation g last last|=|g last+g 0| := by
    simp only [signedConcatenation,show ¬last+1≤last by omega,if_false,Nat.le_refl,if_true,Nat.sub_self]
    rw [← abs_neg]
    congr 1
    ring
  rw [hBoundary]
  ring

theorem signed_loss_variation (cdf : ℕ → ℝ) (bid last : ℕ) (hBid : bid≤last)
    (hMono : ∀ i<last, cdf i≤cdf (i+1)) (h0 : 0≤cdf 0) (h01 : cdf 0≤1) (hEnd : cdf last=1) :
    variation (signedConcatenation (rowDifference cdf bid) last) (2*last+1)≤4 := by
  have he := row_difference_variation cdf bid last hBid hMono h0 h01 hEnd
  rw [signed_concatenation_variation,row_difference_endpoint cdf bid last hBid hEnd,zero_add]
  linarith [abs_nonneg (rowDifference cdf bid 0)]

end Blotto.GeneralPaperLossVariation

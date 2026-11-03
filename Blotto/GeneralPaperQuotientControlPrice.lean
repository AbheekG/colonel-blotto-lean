import Blotto.GeneralPaperCompleteQuotientPrice

/-! All constructed quotient bits, native work additions and depth controls
have words derived from the actual recursion depth. No counter-word oracle
or extra validation pass is part of the implementation.
-/
namespace Blotto.GeneralPaperQuotientControlPrice
open GeneralPaperCompleteQuotientPrice
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem quotient_words (x a : ℚ) (A t depth : ℕ) :
    let higher := GeneralPaperBoundedQuotient.run x (2*a) depth
    1+binaryWordWidth higher.quotient≤width A t (depth+1) ∧
    1+binaryWordWidth (2*higher.quotient)≤width A t (depth+1) ∧
    1+binaryWordWidth (2*higher.quotient+1)≤width A t (depth+1) := by
  have hq := GeneralPaperInitializerRoundingBits.raw_quotient_words x a depth (depth+2) (Nat.le_refl _)
  have hSmall := binaryWordWidth_mono
    (show (GeneralPaperBoundedQuotient.run x (2*a) depth).quotient≤2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient by omega)
  have hw := width_lower A t (depth+1)
  exact ⟨by omega,by omega,by omega⟩

theorem work_words (x a : ℚ) (A t depth : ℕ) :
    let higher := GeneralPaperBoundedQuotient.run x (2*a) depth
    1+binaryWordWidth higher.work≤width A t (depth+1) ∧
    1+binaryWordWidth (higher.work+12)≤width A t (depth+1) := by
  dsimp only
  rw [GeneralPaperBoundedQuotient.run_work]
  have h := GeneralPaperParameterCounterWords.linear_word depth
  have hm := binaryWordWidth_mono (show 12*depth+2+12≤12*depth+194 by omega)
  have hSmall := binaryWordWidth_mono (show 12*depth+2≤12*depth+2+12 by omega)
  have hd := GeneralPaperInitializerControlCounters.word_le_self depth
  have hw := width_lower A t (depth+1)
  exact ⟨by omega,by omega⟩

theorem depth_words (A t depth : ℕ) :
    1+binaryWordWidth (depth+1)≤width A t (depth+1) ∧
    1+binaryWordWidth ((depth+1)-1)≤width A t (depth+1) := by
  have h := GeneralPaperInitializerControlCounters.word_le_self (depth+1)
  have hs := binaryWordWidth_mono (show (depth+1)-1≤depth+1 by omega)
  have hw := width_lower A t (depth+1)
  exact ⟨by omega,by omega⟩

theorem control_work (price : ℕ → ℕ) (hMono : Monotone price) (x a : ℚ) (A t depth : ℕ) :
    controlCost price depth (GeneralPaperBoundedQuotient.run x (2*a) depth)≤6*price (width A t (depth+1)) := by
  have hq := quotient_words x a A t depth
  have hw := work_words x a A t depth
  have hd := depth_words A t depth
  have h2 := constant_word A t (depth+1) 2 (by omega)
  have h1 := constant_word A t (depth+1) 1 (by omega)
  have h12 := constant_word A t (depth+1) 12 (Nat.le_refl _)
  have hm := GeneralPaperIntegerWordPrice.natural_binary price hMono (fun a b => a*b) 2 _ _ h2 hq.1 hq.2.1
  have ha := GeneralPaperIntegerWordPrice.natural_binary price hMono (fun a b => a+b) _ 12 _ hw.1 h12 hw.2
  have hp := GeneralPaperIntegerWordPrice.natural_binary price hMono (fun a b => a-b) (depth+1) 1 _ hd.1 h1 hd.2
  unfold controlCost
  omega

theorem selected_quotient_work (price : ℕ → ℕ) (hMono : Monotone price) (x a : ℚ) (A t depth : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b)
      (2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient) 1≤2*price (width A t (depth+1)) := by
  have hq := quotient_words x a A t depth
  exact GeneralPaperIntegerWordPrice.natural_binary price hMono (fun a b => a+b) _ 1 _
    hq.2.1 (constant_word A t (depth+1) 1 (by omega)) hq.2.2

end Blotto.GeneralPaperQuotientControlPrice

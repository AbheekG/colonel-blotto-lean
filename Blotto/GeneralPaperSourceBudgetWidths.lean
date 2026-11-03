import Blotto.GeneralPaperFastSourceDPPrice

/-! The actual classified source budgets use constructed-size rationals.
Both defender normalizations have budget words no larger than a leaf tag's
word, so the repeated root comparisons carry no original-budget input-width
factor. Original exact input scales remain retained separately for output. -/
namespace Blotto.GeneralPaperSourceBudgetWidths
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 1000000

def height (m k : ℕ) : ℕ := (alphabet m k).lambda+1
def word (m k : ℕ) : ℕ := 1+2*height m k

theorem cap_height (m k : ℕ) : binaryWordWidth (prepare m k).qbar≤height m k :=
  (binaryWordWidth_mono ((GeneralPaperSourceAlphabetLower.cap_le_order m k).trans
    (GeneralPaperSourceAlphabetLower.order_le_scale (alphabet m k)))).trans
    (GeneralPaperSourceAlphabetLower.scale_width (alphabet m k))

theorem proxy_height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    RationalHeight (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value (height m k) :=
  (GeneralPaperSourceScoreHeights.proxy_height m k b hb).mono (cap_height m k)

theorem own_height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    RationalHeight (ownBudget m k b reciprocal) (height m k) :=
  (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal).mono (cap_height m k)

theorem opposing_height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    RationalHeight (opposingBudget m k b reciprocal) (height m k) := by
  cases reciprocal with
  | false => exact proxy_height m k b hb
  | true =>
    change RationalHeight (1:ℚ) (height m k)
    exact (show RationalHeight (1:ℚ) 1 by norm_num [RationalHeight]).mono (by unfold height; omega)

theorem proxy_word (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    rationalWordWidth (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value≤word m k :=
  rationalWordWidth_of_height (proxy_height m k b hb)

theorem own_word (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    rationalWordWidth (ownBudget m k b reciprocal)≤word m k :=
  rationalWordWidth_of_height (own_height m k b hb reciprocal)

theorem opposing_word (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    rationalWordWidth (opposingBudget m k b reciprocal)≤word m k :=
  rationalWordWidth_of_height (opposing_height m k b hb reciprocal)

theorem leaf_word (m k H : ℕ) : word m k≤GeneralPaperTagHeight.word (height m k) H := by
  have h := GeneralPaperTagHeight.word_mono (height m k) 0 H (Nat.zero_le _)
  rw [GeneralPaperTagHeight.word_zero] at h
  exact h

theorem root_max (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (H : ℕ) :
    max (GeneralPaperTagHeight.word (height m k) H) (rationalWordWidth (ownBudget m k b reciprocal))=
      GeneralPaperTagHeight.word (height m k) H ∧
    max (GeneralPaperTagHeight.word (height m k) H) (rationalWordWidth (opposingBudget m k b reciprocal))=
      GeneralPaperTagHeight.word (height m k) H :=
  ⟨max_eq_left ((own_word m k b hb reciprocal).trans (leaf_word m k H)),
    max_eq_left ((opposing_word m k b hb reciprocal).trans (leaf_word m k H))⟩

theorem prepared_proxy_word {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    rationalWordWidth (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1.1.1.2.choice.proxy.value≤word m k := by
  rw [GeneralPaperPreparedSharedSource.data]
  exact proxy_word m k (b:ℝ) (by exact_mod_cast hb)

end Blotto.GeneralPaperSourceBudgetWidths

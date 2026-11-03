import Blotto.GeneralPaperSignedCutOperands

/-! Complete signed-cut array construction in both paper cost models.
The endpoint slot is present even when the query array is empty.
-/
namespace Blotto.GeneralPaperSignedCutPrice
open GeneralPaperSignedCutExecution
open GeneralPaperSignedCutOperands (width)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile (primitive : ℕ → ℕ) (W m U : ℕ) : ℕ :=
  (m+1)*(3*primitive (width m U)+64*W)+44*(m+2)*arrayWord W (m+1)+6*primitive (width m U)+64*W

def arithmeticProfile (m : ℕ) : ℕ := (m+1)*67+44*(m+2)+70

theorem bit_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (hQueries : ∀ q,queries.read q≤U) :
    (run true (fun w => w) primitive W U negative queries).2≤profile primitive W m U := by
  have hFill := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W (m+1))
    (3*primitive (width m U)+64*W) (element primitive W U negative queries)
    (GeneralPaperSummaryArrayControls.array_word_positive W (m+1))
    (GeneralPaperSummaryArrayControls.array_index W (m+1))
    (GeneralPaperSignedCutOperands.element_work primitive hMono W U negative queries hQueries)
  change _≤(m+1)*(3*primitive (width m U)+64*W)+44*(m+2)*arrayWord W (m+1) at hFill
  have hAnnotation := GeneralPaperSignedCutOperands.annotation_work primitive hMono m U
  unfold run profile
  dsimp only
  simp only [ite_true]
  omega

theorem element_arithmetic_work {m : ℕ} (U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ) (i : Fin (m+1)) :
    (element (fun _ => 1) 1 U negative queries i).2≤67 := by
  unfold element
  dsimp only
  split <;> cases negative <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary] <;> omega

theorem arithmetic_work {m : ℕ} (U : ℕ) (negative : Bool) (queries : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 U negative queries).2≤arithmeticProfile m := by
  have hFill := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 67 (element (fun _ => 1) 1 U negative queries)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (element_arithmetic_work U negative queries)
  unfold run arithmeticProfile GeneralPaperNaturalPrimitivePrice.binary
  dsimp only
  simp only [Bool.false_eq_true,ite_false]
  omega

theorem codes {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (hQueries : ∀ q,queries.read q≤U) (i : Fin (m+1)) :
    (run bits index primitive W U negative queries).1.1.read i≤2*U := by
  rw [array_data]
  exact GeneralPaperSourceRankCache.signed_cuts_bound U negative queries hQueries i

end Blotto.GeneralPaperSignedCutPrice

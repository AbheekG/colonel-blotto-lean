import Blotto.GeneralPaperSourceRankCache

/-! Native signed-tail cuts with their own complete prices. The constant
native annotation has a closed form, computed once and priced explicitly.
There is one array fill and no annotation-sum traversal after it.
-/
namespace Blotto.GeneralPaperSignedCutExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def element {m : ℕ} (primitive : ℕ → ℕ) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (i : Fin (m+1)) : ℕ × ℕ :=
  let checked := GeneralPaperIntegerWordPrice.compare primitive i.val m
  if h : i.val<m then
    let a := queries.read ⟨i.val,h⟩
    if negative then (U+a,checked+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) U a+64*W)
    else (a,checked+64*W)
  else if negative then (2*U,checked+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 U+64*W)
    else (U,checked+64*W)

def run {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) : (FixedArrayTable (m+1) ℕ × ℕ) × ℕ :=
  let count := m+1
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W count else W)
    (element primitive W U negative queries)
  let scaled := 54*count
  let annotation := scaled+18
  ((filled.1,annotation),filled.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) m 1+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 54 count+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) scaled 18+64*W)

theorem element_data {m : ℕ} (primitive : ℕ → ℕ) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (i : Fin (m+1)) :
    (element primitive W U negative queries i).1=GeneralPaperSignedTailPlan.cutValue U negative queries i := by
  unfold element GeneralPaperSignedTailPlan.cutValue
  split <;> cases negative <;> rfl

theorem array_data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) :
    (run bits index primitive W U negative queries).1.1=(GeneralPaperSignedTailPlan.cutBuild U negative queries).1 := by
  unfold run GeneralPaperSignedTailPlan.cutBuild
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext i
  exact element_data primitive W U negative queries i

theorem data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) :
    (run bits index primitive W U negative queries).1=GeneralPaperSignedTailPlan.cutBuild U negative queries := by
  apply Prod.ext
  · exact array_data bits index primitive W U negative queries
  · exact (GeneralPaperSignedTailPlan.cut_work U negative queries).symm

theorem every_prefix {m : ℕ} (index primitive : ℕ → ℕ) (W A U : ℕ) (negative : Bool)
    (queries : FixedArrayTable m ℕ) (count : ℕ) (hCount : count≤m+1) :
    (PaperIndexedArrayConstruction.fill index A (element primitive W U negative queries) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperSignedCutExecution

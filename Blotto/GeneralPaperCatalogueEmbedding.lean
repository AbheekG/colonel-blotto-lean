import Blotto.GeneralPaperCatalogueRowSemantics

/-! Every actually decoded whole code row has a generated catalogue row
with no larger exact resource and the same rounded signed-tail objective.
The existential row is a proof comparator, not a source enumeration or a
run-time choice oracle. The actual optimizer receives only the cached arrays.
-/
namespace Blotto.GeneralPaperCatalogueEmbedding
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCatalogueArrays
open GeneralPaperCatalogueRowSemantics
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem represents {m : ℕ} (a : Alphabet) (response : Bool) (k T Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (summaries : FixedArrayTable m (Summary k)) (prefixes : FixedArrayTable m (Prefix k))
    (hMono : ∀ j, Monotone (summaries.read j).read) (hCodes : ∀ j r, (summaries.read j).read r<2*(8*a.C))
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode a response (codes.read j)).choice=some (choices.read j)) :
    ∃ row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),
      GeneralPaperNativeRowOptimizer.resource k T weights prefixes
        (GeneralPaperOrderedNativeProfitOptimizer.plans k (8*a.C) summaries (prepare a response k summaries).codes
          (tags (prepare a response k summaries))) row≤(∑ j, (choices.read j).tag) ∧
      GeneralPaperNativeRowValues.score k Qv weights prefixes
        (GeneralPaperOrderedNativeProfitOptimizer.plans k (8*a.C) summaries (prepare a response k summaries).codes
          (tags (prepare a response k summaries))) row=
        referenceScore k (8*a.C) Qv weights summaries prefixes codes := by
  classical
  have he := fun j : Fin m => GeneralPaperCachedCatalogue.preserves_objective a response k (summaries.read j)
    (prefixes.read j) (hMono j) (hCodes j) (codes.read j) (choices.read j) (hDecode j)
  choose index hTags hValues using he
  let row := FixedArrayTable.ofFn index
  refine ⟨row,?_,?_⟩
  · rw [resource_exact]
    apply Finset.sum_le_sum
    intro j _
    simp only [row,rowChoices,FixedArrayTable.read_ofFn,entries_read]
    exact hTags j
  · rw [score_exact]
    unfold referenceScore
    apply Finset.sum_congr rfl
    intro j _
    simp only [row,rowCodes,FixedArrayTable.read_ofFn,codes_read,entries_read]
    rw [hValues j]

end Blotto.GeneralPaperCatalogueEmbedding

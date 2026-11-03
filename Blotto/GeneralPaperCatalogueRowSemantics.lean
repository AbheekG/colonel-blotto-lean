import Blotto.GeneralPaperCatalogueArrays

/-! The generated native catalogue's original code rows, decoded choices,
exact tags and signed-tail score. These identities link the existing native
profit optimizer to literal catalogue entries, with no dummy-field terms.
-/
namespace Blotto.GeneralPaperCatalogueRowSemantics
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCatalogueArrays
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def rowCodes {m K : ℕ} (data : Arrays m K) (row : FixedArrayTable m (Fin K)) : FixedArrayTable m ℕ :=
  FixedArrayTable.ofFn (fun j => (data.codes.read j).read (row.read j))

def rowChoices {m K : ℕ} (data : Arrays m K) (row : FixedArrayTable m (Fin K)) : FixedArrayTable m Choice :=
  FixedArrayTable.ofFn (fun j => ((data.entries.read j).read (row.read j)).predecessor)

def referenceScore {m : ℕ} (k U Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (summaries : FixedArrayTable m (Summary k)) (prefixes : FixedArrayTable m (Prefix k)) (codes : FixedArrayTable m ℕ) : ℚ :=
  ∑ j, (weights.read j:ℚ)/Qv*GeneralPaperSignedTailProperties.signedValue k U (summaries.read j) (prefixes.read j) (codes.read j)

theorem row_decoded {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k))
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (j : Fin m) :
    (decode a response ((rowCodes (prepare a response k summaries) row).read j)).choice=
      some ((rowChoices (prepare a response k summaries) row).read j) := by
  simp only [rowCodes,rowChoices,FixedArrayTable.read_ofFn]
  exact decoded_entry a response k summaries j (row.read j)

theorem resource_exact {m K : ℕ} (k U T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (summaries : FixedArrayTable m (Summary k)) (data : Arrays m K) (row : FixedArrayTable m (Fin K)) :
    GeneralPaperNativeRowOptimizer.resource k T weights prefixes
      (GeneralPaperOrderedNativeProfitOptimizer.plans k U summaries data.codes (tags data)) row=
      ∑ j, ((rowChoices data row).read j).tag := by
  rw [GeneralPaperNativeRowValues.resource_tags]
  simp only [tags_read,rowChoices,FixedArrayTable.read_ofFn]

theorem score_exact {m K : ℕ} (k U Qv : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (summaries : FixedArrayTable m (Summary k)) (data : Arrays m K) (row : FixedArrayTable m (Fin K)) :
    GeneralPaperNativeRowValues.score k Qv weights prefixes
      (GeneralPaperOrderedNativeProfitOptimizer.plans k U summaries data.codes (tags data)) row=
      referenceScore k U Qv weights summaries prefixes (rowCodes data row) := by
  unfold GeneralPaperNativeRowValues.score referenceScore
  apply Finset.sum_congr rfl
  intro j _
  simp only [GeneralPaperOrderedNativeProfitOptimizer.plans,FixedArrayTable.read_ofFn,
    GeneralPaperOrderedNativeOptionProfits.prepare,GeneralPaperSignedTailValues.evaluate_value,rowCodes]

theorem physical_entry {m K : ℕ} (data : Arrays m K) (row : FixedArrayTable m (Fin K)) (delta : ℚ) (j : Fin m) :
    (GeneralPaperNativeRowBudget.physicalRow data.thresholds data.opened delta row).read j=
      ((rowChoices data row).read j).physical delta := by
  simp only [GeneralPaperNativeRowBudget.physicalRow,FixedArrayTable.read_ofFn,thresholds_read,opened_read,rowChoices,Choice.physical]

end Blotto.GeneralPaperCatalogueRowSemantics

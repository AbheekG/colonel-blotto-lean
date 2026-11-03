import Blotto.GeneralPaperFieldPhaseCursorCoverage

/-! Native Ready/catalogue progress is represented exactly in the finite
frontier. The returned tail partition derives raw cell counts; actual fixed
summary and packed-list sizes derive copy/padding limits. All three native
projection fields are included, with final prefixes unchanged. -/
namespace Blotto.GeneralPaperReadyPhaseCursorCoverage
open GeneralPaperCodeAlphabet GeneralPaperFiniteStorageWindows GeneralPaperStorageCursorPacking
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCatalogueProjection (Field)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def projectionIndex : Field → Fin 3
  | .code => 0
  | .threshold => 1
  | .opened => 2

theorem projection_identity (field : Field) : GeneralPaperReadyPreparationPhaseStorage.projection (projectionIndex field)=field := by
  cases field <;> rfl

theorem part_count {k : ℕ} (a : Alphabet) (summary : Summary k) :
    (GeneralPaperCachedCatalogueStorage.part a summary).count≤(GeneralPaperSourceParameters.prepare k).summarySize+1 :=
  GeneralPaperTailCataloguePartition.count_bound (8*a.C) summary

def cachedAt {k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (summary : Summary k)
    (progress : Fin 5 → Fin (GeneralPaperFieldPreparationPhaseStorage.progressCap k+1)) : ℕ :=
  let part := GeneralPaperCachedCatalogueStorage.part a summary
  GeneralPaperCachedCatalogueStorage.window model W a response summary (progress 0).val (progress 1).val
    (min (progress 2).val part.count) (min (progress 3).val part.count)
    (min (progress 4).val ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..)

theorem visit_covered {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (field : Field) (count copied rowCount tailCount : ℕ) (hc : count≤m) (hd : copied≤m)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1))
    (progress : Fin 5 → Fin (GeneralPaperFieldPreparationPhaseStorage.progressCap k+1)) :
    GeneralPaperReadyConstructionStorage.window model W mesh a response summaries hm count rowCount tailCount hc hr ht j i q+
      (GeneralPaperCatalogueArrayConstructionStorage.window model W a response summaries field count copied rowCount hc hd hr j+
        cachedAt model W a response (summaries.read j) progress)≤
      GeneralPaperReadyPreparationPhaseStorage.peak model W mesh a response summaries hm := by
  let cursor : GeneralPaperReadyPreparationPhaseStorage.Cursor m k :=
    (counter m count hc,counter m copied hd,
      counter ((GeneralPaperSourceParameters.prepare k).summarySize+2) rowCount hr,
      counter (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1) tailCount ht,j,i,q,projectionIndex field,progress)
  have h := observed_le_maximum (GeneralPaperReadyPreparationPhaseStorage.visit model W mesh a response summaries hm) cursor
  have heq : GeneralPaperReadyPreparationPhaseStorage.visit model W mesh a response summaries hm cursor=
      GeneralPaperReadyConstructionStorage.window model W mesh a response summaries hm count rowCount tailCount hc hr ht j i q+
        (GeneralPaperCatalogueArrayConstructionStorage.window model W a response summaries field count copied rowCount hc hd hr j+
          cachedAt model W a response (summaries.read j) progress) := by
    dsimp only [GeneralPaperReadyPreparationPhaseStorage.visit,cursor,counter]
    rw [projection_identity]
    rfl
  exact heq ▸ h

theorem native_cached_constructor {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (field : Field) (count copied rowCount tailCount : ℕ) (hc : count≤m) (hd : copied≤m)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1))
    (used rowCopied : Fin (GeneralPaperBatchCounterPrice.limit k+2)) (partCount rawCount padCount : ℕ)
    (hp : partCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
    (hraw : rawCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
    (hpad : padCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2) :
    GeneralPaperReadyConstructionStorage.window model W mesh a response summaries hm count rowCount tailCount hc hr ht j i q+
      (GeneralPaperCatalogueArrayConstructionStorage.window model W a response summaries field count copied rowCount hc hd hr j+
        GeneralPaperCachedCatalogueStorage.window model W a response (summaries.read j) used.val rowCopied.val
          partCount rawCount padCount hp hraw hpad)≤GeneralPaperReadyPreparationPhaseStorage.peak model W mesh a response summaries hm := by
  let values : Fin 5 → ℕ := fun r => if r.val=0 then used.val else if r.val=1 then rowCopied.val
    else if r.val=2 then partCount else if r.val=3 then rawCount else padCount
  have hpart := part_count a (summaries.read j)
  have hcap := GeneralPaperFieldPhaseCursorCoverage.count_word_cap k
  have hu := used.isLt
  have hr' := rowCopied.isLt
  have hs : (GeneralPaperSourceParameters.prepare k).summarySize+2≤GeneralPaperBatchCounterPrice.limit k+1 := by
    unfold GeneralPaperBatchCounterPrice.limit
    omega
  have hv : ∀ r,values r≤GeneralPaperFieldPreparationPhaseStorage.progressCap k := by
    intro r
    dsimp only [values]
    split_ifs <;> omega
  let progress := vector (GeneralPaperFieldPreparationPhaseStorage.progressCap k) values hv
  have h := visit_covered model W mesh a response summaries hm field count copied rowCount tailCount hc hd hr ht j i q progress
  have heq : cachedAt model W a response (summaries.read j) progress=
      GeneralPaperCachedCatalogueStorage.window model W a response (summaries.read j) used.val rowCopied.val partCount rawCount padCount hp hraw hpad := by
    dsimp only [cachedAt]
    congr 1
    · exact Nat.min_eq_left hp
    · exact Nat.min_eq_left hraw
    · exact Nat.min_eq_left hpad
  exact heq ▸ h

end Blotto.GeneralPaperReadyPhaseCursorCoverage

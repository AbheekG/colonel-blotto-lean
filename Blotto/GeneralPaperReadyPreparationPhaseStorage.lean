import Blotto.GeneralPaperFieldPreparationPhaseStorage

/-! Complete finite Ready/catalogue phase frontier. Full Ready parents,
catalogue/reference projection buffers and active cached-row constructors
coexist. Native partitions determine clipped raw/final counts. The three
projection fields and all progress extrema are erased observers. -/
namespace Blotto.GeneralPaperReadyPreparationPhaseStorage
open GeneralPaperCodeAlphabet GeneralPaperFiniteStorageWindows
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def projection (i : Fin 3) : GeneralPaperCatalogueProjection.Field :=
  if i.val=0 then .code else if i.val=1 then .threshold else .opened

abbrev Cursor (m k : ℕ) :=
  Fin (m+1) × Fin (m+1) × Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1) ×
    Fin ((((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)+1) × Fin m ×
    Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2) ×
    Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1) × Fin 3 ×
    (Fin 5 → Fin (GeneralPaperFieldPreparationPhaseStorage.progressCap k+1))

def visit {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (cursor : Cursor m k) : ℕ :=
  let ⟨count,copied,rowCount,tailCount,j,i,q,field,progress⟩ := cursor
  let part := GeneralPaperCachedCatalogueStorage.part a (summaries.read j)
  let p := fun r : Fin 5 => (progress r).val
  GeneralPaperReadyConstructionStorage.window model W mesh a response summaries hm count.val rowCount.val tailCount.val
    (Nat.le_of_lt_succ count.isLt) (Nat.le_of_lt_succ rowCount.isLt) (Nat.le_of_lt_succ tailCount.isLt) j i q+
    (GeneralPaperCatalogueArrayConstructionStorage.window model W a response summaries (projection field)
      count.val copied.val rowCount.val (Nat.le_of_lt_succ count.isLt) (Nat.le_of_lt_succ copied.isLt) (Nat.le_of_lt_succ rowCount.isLt) j+
      GeneralPaperCachedCatalogueStorage.window model W a response (summaries.read j) (p 0) (p 1)
        (min (p 2) part.count) (min (p 3) part.count) (min (p 4) ((GeneralPaperSourceParameters.prepare k).summarySize+2))
        (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..))

def peak {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) : ℕ :=
  maximum (visit model W mesh a response summaries hm)

def profile (model : RationalCostModel) (W m k mesh : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperReadyConstructionStorage.profile model W m k mesh a+
    (GeneralPaperCatalogueArrayConstructionStorage.profile model W m (GeneralPaperSourceParameters.prepare k).summarySize a+
      GeneralPaperCachedCatalogueStorage.profile model W (GeneralPaperSourceParameters.prepare k).summarySize a)

theorem bounded {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hs : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    peak model W mesh a response summaries hm≤profile model W m k mesh a := by
  apply maximum_bound
  intro cursor
  rcases cursor with ⟨count,copied,rowCount,tailCount,j,i,q,field,progress⟩
  exact GeneralPaperReadyConstructionStorage.with_catalogue_constructor model W mesh a response summaries hm hs (projection field)
    count.val copied.val rowCount.val tailCount.val (Nat.le_of_lt_succ count.isLt) (Nat.le_of_lt_succ copied.isLt)
    (Nat.le_of_lt_succ rowCount.isLt) (Nat.le_of_lt_succ tailCount.isLt) j i q
    (progress 0).val (progress 1).val _ _ _ (Nat.min_le_right ..) (Nat.min_le_right ..) (Nat.min_le_right ..)

theorem native_tree_arrays (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hv : GeneralPaperCatalogueTreeCache.Valid a k trees) (hp : GeneralPaperCatalogueTreeCache.Paths a k trees) :
    let x := GeneralPaperTreeEpochConstructionStorage.arrays model W m k Qv a c hc digits trees
    let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
    max (peak model W c.controls.source.meshDenominator a false x.lambda hm)
      (peak model W c.controls.source.meshDenominator a true x.mu hm)≤
        profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a := by
  dsimp only
  have hs := GeneralPaperTreeEpochConstructionStorage.valid_four model W m k Qv a c hc digits trees hv hp
  have hca := bounded model W c.controls.source.meshDenominator a false _
    (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) hs.2.2.1
  have hra := bounded model W c.controls.source.meshDenominator a true _
    (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) hs.2.2.2
  have hmesh := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
  have hca' := hca.trans_eq (show profile model W m k c.controls.source.meshDenominator a=
    profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a by rw [hmesh])
  have hra' := hra.trans_eq (show profile model W m k c.controls.source.meshDenominator a=
    profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a by rw [hmesh])
  exact max_le hca' hra'

end Blotto.GeneralPaperReadyPreparationPhaseStorage

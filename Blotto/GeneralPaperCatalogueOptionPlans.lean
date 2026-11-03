import Blotto.GeneralPaperOptionPlanFamily

/-! Complete the cached-plan portion of native optimizer preparation from
retained catalogue/tag arrays. Their own construction is a separate required
price; this join reuses them and the retained mesh without regeneration.
-/
namespace Blotto.GeneralPaperCatalogueOptionPlans
open GeneralPaperCodeAlphabet
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k))
    (data : GeneralPaperCatalogueArrays.Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hData : data=GeneralPaperCatalogueArrays.prepare a response k summaries)
    (tags : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) GeneralPaperResponseTag.Tag))
    (hTags : tags=GeneralPaperCatalogueArrays.tags data)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) : GeneralPaperCatalogueOptimizer.Ready m k × ℕ :=
  let returned := GeneralPaperOptionPlanFamily.run bits index primitive W k (8*a.C) mesh summaries data.codes tags
  (⟨a,response,summaries,data,returned.1,hData,by
    rw [GeneralPaperOptionPlanFamily.data bits index primitive W k (8*a.C) mesh summaries data.codes tags hMesh,hTags]⟩,
    returned.2+128*W)

theorem data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k))
    (catalogue : GeneralPaperCatalogueArrays.Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hData : catalogue=GeneralPaperCatalogueArrays.prepare a response k summaries)
    (tags : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) GeneralPaperResponseTag.Tag))
    (hTags : tags=GeneralPaperCatalogueArrays.tags catalogue)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index primitive W k mesh a response summaries catalogue hData tags hTags hMesh).1=
      GeneralPaperCatalogueOptimizer.prepare a response k summaries := by
  subst catalogue
  subst tags
  unfold run GeneralPaperCatalogueOptimizer.prepare
  dsimp only
  simp only [GeneralPaperOptionPlanFamily.data bits index primitive W k (8*a.C) mesh _ _ _ hMesh]

theorem bit_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k))
    (catalogue : GeneralPaperCatalogueArrays.Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hData : catalogue=GeneralPaperCatalogueArrays.prepare a response k summaries)
    (tags : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) GeneralPaperResponseTag.Tag))
    (hTags : tags=GeneralPaperCatalogueArrays.tags catalogue)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hSummary : ∀ field r,(summaries.read field).read r≤2*(8*a.C)) :
    (run true (fun w => w) primitive W k mesh a response summaries catalogue hData tags hTags hMesh).2≤
      GeneralPaperOptionPlanFamily.profile primitive W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) k (8*a.C)+128*W := by
  have hCodes : ∀ field i,(catalogue.codes.read field).read i≤8*a.C := by
    intro field i
    rw [hData]
    exact (GeneralPaperCatalogueArrays.code_bound a response k summaries field i).le
  exact Nat.add_le_add_right (GeneralPaperOptionPlanFamily.bit_work primitive hMono W k (8*a.C) mesh
    summaries catalogue.codes tags hCodes hSummary) _

theorem arithmetic_work {m : ℕ} (k mesh : ℕ) (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (Summary k))
    (catalogue : GeneralPaperCatalogueArrays.Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hData : catalogue=GeneralPaperCatalogueArrays.prepare a response k summaries)
    (tags : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) GeneralPaperResponseTag.Tag))
    (hTags : tags=GeneralPaperCatalogueArrays.tags catalogue)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run false (fun _ => 1) (fun _ => 1) 1 k mesh a response summaries catalogue hData tags hTags hMesh).2≤
      GeneralPaperOptionPlanFamily.arithmeticProfile m ((GeneralPaperSourceParameters.prepare k).summarySize+2) k+128 := by
  exact Nat.add_le_add_right (GeneralPaperOptionPlanFamily.arithmetic_work k (8*a.C) mesh summaries catalogue.codes tags) _

def signed {m k : ℕ} (response : Bool) (arrays : GeneralPaperFourSummaryArrays.Arrays m k) : FixedArrayTable m (Summary k) :=
  if response then arrays.mu else arrays.lambda

theorem generated_summary_bound (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hValid : GeneralPaperCatalogueTreeCache.Valid a k trees) (hPaths : GeneralPaperCatalogueTreeCache.Paths a k trees)
    (response : Bool) :
    let arrays := (GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc digits trees).1
    ∀ field r,((signed response arrays).read field).read r≤2*(8*a.C) := by
  have hCodes := GeneralPaperSourceRankCache.codes bits index primitive W m k Qv a c hc digits trees hValid hPaths
  cases response
  · exact fun field r => (hCodes .lambda field r).le
  · exact fun field r => (hCodes .mu field r).le

theorem generated_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hValid : GeneralPaperCatalogueTreeCache.Valid a k trees) (hPaths : GeneralPaperCatalogueTreeCache.Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc digits trees).1)
    (response : Bool)
    (catalogue : GeneralPaperCatalogueArrays.Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hData : catalogue=GeneralPaperCatalogueArrays.prepare a response k (signed response arrays))
    (tags : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) GeneralPaperResponseTag.Tag))
    (hTags : tags=GeneralPaperCatalogueArrays.tags catalogue) :
    (run true (fun w => w) primitive W k c.controls.source.meshDenominator a response (signed response arrays) catalogue hData tags hTags
      (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)).2≤
      GeneralPaperOptionPlanFamily.profile primitive W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) k (8*a.C)+128*W := by
  have hSummary := generated_summary_bound true (fun w => w) primitive W m k Qv a c hc digits trees hValid hPaths response
  rw [←hArrays] at hSummary
  exact bit_work primitive hMono W k c.controls.source.meshDenominator a response (signed response arrays) catalogue hData tags hTags
    (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) hSummary

end Blotto.GeneralPaperCatalogueOptionPlans

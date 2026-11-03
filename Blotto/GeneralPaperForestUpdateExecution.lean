import Blotto.GeneralPaperEpochNodeUpdate

/-! Four indexed field loops update the same retained incoming forest from
its actual returned final cell arrays. Height additions and all field reads,
references/dispatch/record operations are explicit. Source preparation and
local-round simulation are not executed by this wrapper.
-/
namespace Blotto.GeneralPaperForestUpdateExecution
open GeneralPaperIntervalCache GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def heightCost (price : ℕ → ℕ) (learner : Learner) (lambda : ℕ) : ℕ :=
  match learner with
  | .p | .q => 0
  | .lambda | .mu => GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) lambda 1

def element {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (shared : Shared m) (trees : Trees m cache.alphabet.lambda)
    (state : State cache) (learner : Learner) (j : Fin m) : Node (treeHeight learner cache.alphabet.lambda) × ℕ :=
  let updated := GeneralPaperEpochNodeUpdate.run bits index price W c learner state j
    (treeHeight learner cache.alphabet.lambda) (node learner trees j) (span learner shared)
  (updated.1.node,updated.2+heightCost (if bits then price else fun _ => 1) learner cache.alphabet.lambda+256*W)

def family {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (shared : Shared m) (trees : Trees m cache.alphabet.lambda)
    (state : State cache) (learner : Learner) : FixedArrayTable m (Node (treeHeight learner cache.alphabet.lambda)) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (element bits index price W c shared trees state learner)

def run {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (shared : Shared m) (trees : Trees m cache.alphabet.lambda)
    (state : State cache) : Trees m cache.alphabet.lambda × ℕ :=
  let p := family bits index price W c shared trees state .p
  let q := family bits index price W c shared trees state .q
  let lambda := family bits index price W c shared trees state .lambda
  let mu := family bits index price W c shared trees state .mu
  (⟨p.1,q.1,lambda.1,mu.1⟩,p.2+q.2+lambda.2+mu.2+128*W)

theorem element_data {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (hPowers : c.powers=shared.powers) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (learner : Learner) (j : Fin m) (hSpan : span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ i<2^(treeHeight learner cache.alphabet.lambda),GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (element bits index price W c shared trees state learner j).1=
      GeneralPaperCatalogueForestUpdate.updatedNode (a:=cache.alphabet) shared learner trees state j := by
  have hd := GeneralPaperEpochNodeUpdate.data bits index price W Qv c hc learner state j _ _ _ hSpan (hValid learner j) hFinal
  change (GeneralPaperEpochNodeUpdate.run bits index price W c learner state j _ _ _).1.node=_
  rw [hd,hPowers]
  rfl

theorem family_data {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (hPowers : c.powers=shared.powers) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (learner : Learner) (hSpan : span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (family bits index price W c shared trees state learner).1=
      FixedArrayTable.ofFn (GeneralPaperCatalogueForestUpdate.updatedNode (a:=cache.alphabet) shared learner trees state) := by
  rw [family,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact element_data bits index price W Qv c hc shared hPowers trees state learner j hSpan hValid (hFinal j)

theorem data {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (hPowers : c.powers=shared.powers) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (hSpan : ∀ learner,span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ learner j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (run bits index price W c shared trees state).1=GeneralPaperCatalogueForestUpdate.apply (a:=cache.alphabet) shared trees state := by
  unfold run GeneralPaperCatalogueForestUpdate.apply
  dsimp only
  rw [family_data bits index price W Qv c hc shared hPowers trees state .p (hSpan .p) hValid (hFinal .p),
    family_data bits index price W Qv c hc shared hPowers trees state .q (hSpan .q) hValid (hFinal .q),
    family_data bits index price W Qv c hc shared hPowers trees state .lambda (hSpan .lambda) hValid (hFinal .lambda),
    family_data bits index price W Qv c hc shared hPowers trees state .mu (hSpan .mu) hValid (hFinal .mu)]
  rfl

end Blotto.GeneralPaperForestUpdateExecution

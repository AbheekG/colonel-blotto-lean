import Blotto.GeneralPaperReferenceRegionProgram

/-! Header owners selected in actual layout order inherit block separation,
encoded root correctness and numerical capacity. Thus one installation and
all subsequent indexed field reads use the executed measured layout, without
an independently supplied address, non-aliasing or capacity certificate. -/
namespace Blotto.GeneralPaperReferenceLayoutInstallation
open GeneralPaperReferenceRegionSlots GeneralPaperReferenceRegionProgram GeneralPaperSequentialLayout GeneralPaperMeasuredBlockPlan
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def FromLayout (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A)) : Prop :=
  (headers.map Header.region).Sublist (GeneralPaperMeasuredBlockLayout.run model S A start plan).1

theorem owner_mem (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) (header : Header A) (hHeader : header ∈ headers) :
    header.region ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 :=
  hFrom.subset (List.mem_map.mpr ⟨header,hHeader,rfl⟩)

theorem owners (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) : DisjointOwners headers := by
  have h := (GeneralPaperMeasuredBlockLayout.disjoint model S A start plan).sublist hFrom
  simpa only [DisjointOwners,List.pairwise_map] using h

theorem capacities (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ header ∈ headers,header.region.stop < 2 ^ A := by
  intro header hh
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan header.region
    (owner_mem model S A start plan headers hFrom header hh)
  exact hRange.2.trans_lt hCap

theorem roots (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ header ∈ headers,header.region.reference.value = header.region.start := by
  intro header hh
  exact GeneralPaperMeasuredBlockLayout.references model S A start plan hCap header.region
    (owner_mem model S A start plan headers hFrom header hh)

theorem all_keys (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) (hA : 0 < A)
    (hValid : ∀ header ∈ headers,Valid header) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ((collect model S A headers).entries.map (fun entry => entry.location.value)).Nodup :=
  GeneralPaperReferenceRegionProgram.keys_nodup model S A headers hA hValid
    (capacities model S A start plan headers hFrom hCap) (owners model S A start plan headers hFrom)

theorem read_prepared (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (headers : List (Header A))
    (hFrom : FromLayout model S A start plan headers) (memory : GeneralPaperRawReferenceMemory.Memory A)
    (hA : 0 < A) (hValid : ∀ header ∈ headers,Valid header) (hCap : start + plan.sizes.sum < 2 ^ A)
    (header : Header A) (hHeader : header ∈ headers) (j : Fin header.targets.length) :
    (read model A (prepare model S A headers memory).memory header.region.reference header.fixed j.val).1 =
      some header.targets[j.val] :=
  GeneralPaperReferenceRegionProgram.read_prepared model S A headers memory hA hValid
    (capacities model S A start plan headers hFrom hCap) (roots model S A start plan headers hFrom hCap)
    (owners model S A start plan headers hFrom) header hHeader j

end Blotto.GeneralPaperReferenceLayoutInstallation

import Blotto.GeneralPaperStoredRouteCoordinateWork
import Blotto.GeneralPaperStoredRouteEmission

/-! Complete emission charges the actual count, every route/coordinate
read, counter increment, output payload copy and one array materialization.
The measured front owner supplies all counter and buffer capacities. -/
namespace Blotto.GeneralPaperStoredRouteEmissionWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def collectBound (model : RationalCostModel) (A n m s : ℕ) : ℕ :=
  n * (GeneralPaperStoredRouteCoordinateWork.bound model A m s + GeneralPaperStoredStreamWork.stepBound model A +
    128 * (A + 1) + (1 + 4 * s)) + GeneralPaperStoredCountReadWork.bound model A + 192 * (A + 1)

def bound (model : RationalCostModel) (A n m s : ℕ) : ℕ :=
  collectBound model A n m s + 64 * (n + 1) * A + 128 * (A + 1)

theorem collect_work {n m : ℕ} (model : RationalCostModel) (S A layoutStart start s : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (routes : FixedArrayTable n (GroupRoute m))
    (hRead : Readback model A installed (GeneralPaperRouteArrayCursor.expected model S A start routes))
    (hHeaders : ∀ header ∈ (GeneralPaperRouteArrayCursor.expected model S A start routes).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference)
    (groups : FixedArrayTable m ℚ) (hs : 2 ≤ s) (hC : ∀ j,RationalHeight (routes.read j).2 s)
    (hG : ∀ g,RationalHeight (groups.read g) s) :
    (GeneralPaperStoredRouteEmission.collect model A installed groups.data).work ≤ collectBound model A n m s := by
  let values := List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))
  have hExtent := GeneralPaperStoredRouteArrayWork.capacity model S A layoutStart start plan full installed ctx routes hHeaders
  have hEach : ∀ index : Fin values.length,(GeneralPaperStoredRouteCoordinate.read model A installed groups.data (0 + index.val)).2 ≤
      0 * rationalWordWidth values[index.val] + GeneralPaperStoredRouteCoordinateWork.bound model A m s := by
    intro index
    have hi : index.val < n := by simpa only [values,List.length_ofFn] using index.isLt
    let j : Fin n := ⟨index.val,hi⟩
    obtain ⟨_,hRoute,_⟩ := GeneralPaperStoredRouteArraySource.source model S A start installed routes hRead hRoot j
    have hReadWork := (GeneralPaperStoredRouteArrayWork.work model S A layoutStart start plan full installed ctx routes hRead hHeaders hRoot j).trans
      (GeneralPaperStoredRouteArrayWork.height_bound model A m s (routes.read j).2 (hC j))
    simpa only [Nat.zero_add,Nat.zero_mul] using GeneralPaperStoredRouteCoordinateWork.work model A s installed groups index.val (routes.read j)
      hRoute hReadWork hs (hC j) hG
  have hPrice := GeneralPaperStoredStreamWork.price_bound model A (GeneralPaperStoredRouteCoordinate.read model A installed groups.data)
    rationalWordWidth values 0 0 (GeneralPaperStoredRouteCoordinateWork.bound model A m s)
    (by simpa only [values,List.length_ofFn,Nat.zero_add] using Nat.lt_of_succ_lt hExtent) hEach
  have hPayload : (values.map rationalWordWidth).sum ≤ n * (1 + 4 * s) := by
    simp only [values,List.map_ofFn,List.sum_ofFn]
    calc
      _ ≤ ∑ _j : Fin n,(1 + 4 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (GeneralPaperStoredRouteCoordinateWork.value_height groups (routes.read j) s hs (hC j) hG)).trans (by omega))
      _ = _ := by simp
  have hHeader : GeneralPaperStoredRouteArrayWork.header model S A start routes ∈ full.headers := hHeaders _ (List.mem_cons_self ..)
  have hCountWork := GeneralPaperStoredCountReadWork.work model A installed full ctx.contract _ hHeader (by change (64 : ℕ) ≠ 0; decide)
  change (GeneralPaperHeaderCountReadback.count model A installed
    (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference).2 ≤ _ at hCountWork
  rw [← hRoot] at hCountWork
  rw [(GeneralPaperStoredRouteEmission.collect_source model S A start installed full ctx.contract routes hRead hHeaders hRoot groups).2.2]
  simp only [values,List.length_ofFn,Nat.zero_add,Nat.one_mul] at hPrice
  unfold collectBound
  nlinarith only [hPrice,hPayload,hCountWork]

theorem work {n m : ℕ} (model : RationalCostModel) (S A layoutStart start s : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (routes : FixedArrayTable n (GroupRoute m))
    (hRead : Readback model A installed (GeneralPaperRouteArrayCursor.expected model S A start routes))
    (hHeaders : ∀ header ∈ (GeneralPaperRouteArrayCursor.expected model S A start routes).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference)
    (groups : FixedArrayTable m ℚ) (hs : 2 ≤ s) (hC : ∀ j,RationalHeight (routes.read j).2 s)
    (hG : ∀ g,RationalHeight (groups.read g) s) :
    (GeneralPaperStoredRouteEmission.run model A installed groups.data).work ≤ bound model A n m s := by
  have hCollect := collect_work model S A layoutStart start s plan full installed ctx routes hRead hHeaders hRoot groups hs hC hG
  have hExtent := GeneralPaperStoredRouteArrayWork.capacity model S A layoutStart start plan full installed ctx routes hHeaders
  have hBuffer := PaperListReferenceArray.bit_work A (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))) ctx.positive
    (by rw [List.length_ofFn]; exact binaryWordWidth_le_of_lt_pow ctx.positive hExtent)
  rw [List.length_ofFn] at hBuffer
  rw [(GeneralPaperStoredRouteEmission.source model S A start installed full ctx.contract routes hRead hHeaders hRoot groups).2.2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredRouteEmissionWork

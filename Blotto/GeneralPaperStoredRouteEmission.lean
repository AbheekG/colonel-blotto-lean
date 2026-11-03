import Blotto.GeneralPaperStoredRouteCoordinate

/-! Emission loads its actual route count and computes every coordinate in
source order, then materializes the full rational array once. The executed
collector fixes its actual stored-route reader and copy price internally. -/
namespace Blotto.GeneralPaperStoredRouteEmission
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

structure Result where
  values : Option (Array ℚ)
  count : ℕ
  work : ℕ

def collect (model : RationalCostModel) (A : ℕ) (installed : Installed A) (groups : Array ℚ) : GeneralPaperStoredReadStream.Result ℚ :=
  GeneralPaperStoredReadStream.counted model A installed (GeneralPaperStoredRouteCoordinate.read model A installed groups) rationalWordWidth

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) (groups : Array ℚ) : Result :=
  let actual := collect model A installed groups
  match actual.values with
  | none => ⟨none,actual.count,actual.work + 64 * (A + 1)⟩
  | some values =>
    let buffer := PaperListReferenceArray.run (fun w => w) A values
    ⟨some buffer.1,actual.count,actual.work + buffer.2 + 128 * (A + 1)⟩

theorem collect_source {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (full : Directory A) (hContract : Contract model A installed full) (routes : FixedArrayTable n (GroupRoute m))
    (hRead : Readback model A installed (GeneralPaperRouteArrayCursor.expected model S A start routes))
    (hHeaders : ∀ header ∈ (GeneralPaperRouteArrayCursor.expected model S A start routes).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference)
    (groups : FixedArrayTable m ℚ) :
    (collect model A installed groups.data).values = some (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))) ∧
      (collect model A installed groups.data).count = n ∧
      (collect model A installed groups.data).work = (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 +
        GeneralPaperStoredReadStream.price model A (GeneralPaperStoredRouteCoordinate.read model A installed groups.data) rationalWordWidth 0
          (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))) + 128 * (A + 1) := by
  have hCount := GeneralPaperStoredRouteArraySource.count_source model S A start installed full hContract routes hHeaders hRoot
  have hEach : ∀ index : Fin (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))).length,
      (GeneralPaperStoredRouteCoordinate.read model A installed groups.data index.val).1 =
        some (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j)))[index.val] := by
    intro index
    have hi : index.val < n := by simpa only [List.length_ofFn] using index.isLt
    obtain ⟨_,hRoute,_⟩ := GeneralPaperStoredRouteArraySource.source model S A start installed routes hRead hRoot ⟨index.val,hi⟩
    simpa only [List.getElem_ofFn] using (GeneralPaperStoredRouteCoordinate.source model A installed groups index.val (routes.read ⟨index.val,hi⟩) hRoute).1
  simpa only [collect,List.length_ofFn] using GeneralPaperStoredReadStream.counted_source model A installed
    (GeneralPaperStoredRouteCoordinate.read model A installed groups.data) rationalWordWidth
    (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))) (by simpa only [List.length_ofFn] using hCount) hEach

theorem source {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (full : Directory A) (hContract : Contract model A installed full) (routes : FixedArrayTable n (GroupRoute m))
    (hRead : Readback model A installed (GeneralPaperRouteArrayCursor.expected model S A start routes))
    (hHeaders : ∀ header ∈ (GeneralPaperRouteArrayCursor.expected model S A start routes).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference)
    (groups : FixedArrayTable m ℚ) :
    (run model A installed groups.data).values = some (FixedArrayTable.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))).data ∧
      (run model A installed groups.data).count = n ∧
      (run model A installed groups.data).work = (collect model A installed groups.data).work +
        (PaperListReferenceArray.run (fun w => w) A (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j)))).2 + 128 * (A + 1) := by
  obtain ⟨hv,hc,_⟩ := collect_source model S A start installed full hContract routes hRead hHeaders hRoot groups
  have hList : (List.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))).toArray =
      (FixedArrayTable.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))).data := by
    have h := GeneralPaperRowPrefix.list_ofFn (FixedArrayTable.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j)))
    have hf : (FixedArrayTable.ofFn (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j))).read =
        (fun j => GeneralPaperStoredRouteCoordinate.value groups (routes.read j)) := by
      funext j
      exact FixedArrayTable.read_ofFn _ j
    rw [hf] at h
    rw [h,Array.toArray_toList]
  simp only [run,hv,hc,PaperListReferenceArray.data,hList,and_self]

end Blotto.GeneralPaperStoredRouteEmission

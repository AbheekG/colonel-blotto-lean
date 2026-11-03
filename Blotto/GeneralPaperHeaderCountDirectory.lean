import Blotto.GeneralPaperHeaderCountExpansion

/-! Executed count-header preparation maps actual extracted headers once.
The root, scalar cells, owner regions and complete allocation partition stay
the same. New control words consume only the already reserved header area. -/
namespace Blotto.GeneralPaperHeaderCountDirectory
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def headers (model : RationalCostModel) (S A : ℕ) : List (Header A) → List (Header A) × ℕ
  | [] => ([],64 * (S + A + 1))
  | header :: rest =>
    let actual := GeneralPaperHeaderCountExpansion.run model S A header
    let later := headers model S A rest
    (actual.1 :: later.1,actual.2 + later.2 + 64 * (S + A + 1))

theorem headers_data (model : RationalCostModel) (S A : ℕ) (values : List (Header A)) :
    (headers model S A values).1 = values.map GeneralPaperHeaderCountExpansion.expanded := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [headers,GeneralPaperHeaderCountExpansion.data,ih,List.map_cons]

theorem headers_work (model : RationalCostModel) (S A : ℕ) (values : List (Header A)) :
    (headers model S A values).2 = (values.map (fun header => (GeneralPaperHeaderCountExpansion.run model S A header).2)).sum +
      (values.length + 1) * (64 * (S + A + 1)) := by
  induction values with
  | nil => simp only [headers,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
  | cons value values ih => simp only [headers,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

def expanded {A : ℕ} (directory : Directory A) : Directory A :=
  ⟨directory.root,directory.headers.map GeneralPaperHeaderCountExpansion.expanded,directory.cells⟩

def prepare (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : Directory A × ℕ :=
  let actual := headers model S A directory.headers
  (⟨directory.root,actual.1,directory.cells⟩,actual.2 + GeneralPaperLastRegionSelection.price S A directory.root + 64 * (S + A + 1))

theorem data (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : (prepare model S A directory).1 = expanded directory := by
  simp only [prepare,headers_data,expanded]

theorem root {A : ℕ} (directory : Directory A) : (expanded directory).root = directory.root := rfl
theorem cells {A : ℕ} (directory : Directory A) : (expanded directory).cells = directory.cells := rfl

theorem header_regions {A : ℕ} (directory : Directory A) :
    (expanded directory).headers.map Header.region = directory.headers.map Header.region := by
  simp only [expanded,List.map_map,Function.comp_def,GeneralPaperHeaderCountExpansion.region]

theorem header_member {A : ℕ} (directory : Directory A) (header : Header A) (hHeader : header ∈ directory.headers) :
    GeneralPaperHeaderCountExpansion.expanded header ∈ (expanded directory).headers :=
  List.mem_map.mpr ⟨header,hHeader,rfl⟩

theorem safe {A : ℕ} (regions : List (Region A)) (directory : Directory A) (hSafe : Safe regions directory) :
    Safe regions (expanded directory) := by
  refine ⟨hSafe.1,?_,hSafe.2.2.1,?_,hSafe.2.2.2.2⟩
  · rw [header_regions]; exact hSafe.2.1
  · intro header hh
    obtain ⟨source,hs,rfl⟩ := List.mem_map.mp hh
    exact GeneralPaperHeaderCountExpansion.valid source (hSafe.2.2.2.1 source hs)

theorem covered {A : ℕ} (regions : List (Region A)) (directory : Directory A) (hCovered : Covered regions directory) :
    Covered regions (expanded directory) := by
  unfold Covered
  rw [header_regions,cells]
  exact hCovered

theorem joint_area (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    A * GeneralPaperReferenceHeaderSlotArea.slots (expanded directory).headers +
      ((expanded directory).cells.map (fun cell => GeneralPaperRetainedScalarValue.encode cell.value)).sum ≤ plan.sizes.sum :=
  GeneralPaperFieldDirectorySeparation.joint_area model S A start plan (expanded directory)
    (safe _ directory hSafe) (covered _ directory hCovered)

theorem work (model : RationalCostModel) (S A : ℕ) (directory : Directory A) :
    (prepare model S A directory).2 = (directory.headers.map (fun header => (GeneralPaperHeaderCountExpansion.run model S A header).2)).sum +
      (directory.headers.length + 2) * (64 * (S + A + 1)) + GeneralPaperLastRegionSelection.price S A directory.root := by
  simp only [prepare,headers_work]
  ring

end Blotto.GeneralPaperHeaderCountDirectory

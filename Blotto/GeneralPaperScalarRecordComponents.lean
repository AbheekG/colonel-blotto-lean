import Blotto.GeneralPaperSegmentRecordCursor

/-! Scalar leaves and front-header scalar lists used by retained control and
budget fields. Existing measured regions determine all roots. Complete owner
partitions and scalar fit are preserved, with priced source mapping. -/
namespace Blotto.GeneralPaperScalarRecordComponents
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def leaf {A : ℕ} (region : Region A) (value : Scalar) : Directory A := ⟨region,[],[⟨region,value⟩]⟩
def leafExpected (A start : ℕ) (value : Scalar) : Directory A :=
  leaf ⟨start,encode value,FixedBinaryWord.ofNat A start⟩ value
def leafRun (S A : ℕ) (value : Scalar) : List (Region A) → GeneralPaperFieldDirectoryParsers.Result A
  | [] => ⟨none,[],64 * (S + A + 1)⟩
  | region :: rest => ⟨some (leaf region value),rest,encode value + GeneralPaperLastRegionSelection.price S A region + 128 * (S + A + 1)⟩

theorem leaf_success (model : RationalCostModel) (S A start : ℕ) (value : Scalar) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start [encode value]).1
    (leafRun S A value (regions ++ rest)).values = some (leafExpected A start value) ∧
      (leafRun S A value (regions ++ rest)).remaining = rest ∧
      Safe regions (leafExpected A start value) ∧ Covered regions (leafExpected A start value) := by
  dsimp only [GeneralPaperSequentialLayout.run]
  simp only [GeneralPaperStoredWordEncoding.word_data,List.singleton_append,leafRun,leafExpected]
  refine ⟨True.intro,True.intro,?_,List.Perm.refl _⟩
  refine ⟨List.mem_singleton_self _,List.nil_sublist _,List.Sublist.refl _,?_,?_⟩
  · intro header hh
    exact False.elim (List.not_mem_nil hh)
  · intro cell hc
    have he : cell = (⟨⟨start,encode value,FixedBinaryWord.ofNat A start⟩,value⟩ : Cell A) := List.mem_singleton.mp hc
    subst cell
    rfl

def listHeader (A start fixed stride count : ℕ) : Region A := ⟨start,A * (stride * count + fixed),FixedBinaryWord.ofNat A start⟩
def compose {A : ℕ} (fixed : ℕ) (header : Region A) (cells : List (Cell A)) : Directory A :=
  ⟨header,[⟨header,fixed,cells.map (fun cell => cell.region.reference)⟩],cells⟩
def listExpected (model : RationalCostModel) (S A start fixed stride : ℕ) (values : List Scalar) : Directory A :=
  compose fixed (listHeader A start fixed stride values.length)
    (GeneralPaperScalarFieldCursor.cells A
      (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map encode)).1 values)

def listRun (S A fixed : ℕ) (values : List Scalar) : List (Region A) → GeneralPaperFieldDirectoryParsers.Result A
  | [] => ⟨none,[],64 * (S + A + 1)⟩
  | header :: regions =>
    let parsed := GeneralPaperScalarFieldCursor.run S A values regions
    match parsed.values with
    | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
    | some cells =>
      let targets := GeneralPaperScalarArrayFieldCursor.targets S A cells
      ⟨some ⟨header,[⟨header,fixed,targets.1⟩],cells⟩,parsed.remaining,
        parsed.work + targets.2 + GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1)⟩

theorem list_success (model : RationalCostModel) (S A start fixed stride : ℕ) (values : List Scalar)
    (rest : List (Region A)) (hStride : 1 ≤ stride) :
    let regions := (GeneralPaperSequentialLayout.run model S A start
      (A * (stride * values.length + fixed) :: values.map encode)).1
    (listRun S A fixed values (regions ++ rest)).values = some (listExpected model S A start fixed stride values) ∧
      (listRun S A fixed values (regions ++ rest)).remaining = rest ∧
      Safe regions (listExpected model S A start fixed stride values) ∧ Covered regions (listExpected model S A start fixed stride values) := by
  dsimp only
  let header := listHeader A start fixed stride values.length
  let regions := (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map encode)).1
  let cells := GeneralPaperScalarFieldCursor.cells A regions values
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  obtain ⟨hv,hr,hFits⟩ := GeneralPaperScalarFieldCursor.layout_success model S A
    (start + A * (stride * values.length + fixed)) values rest
  change (GeneralPaperScalarFieldCursor.run S A values (regions ++ rest)).values = some cells at hv
  change (GeneralPaperScalarFieldCursor.run S A values (regions ++ rest)).remaining = rest at hr
  have hCount := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at hCount
  have hRegions : (GeneralPaperSequentialLayout.run model S A start (A * (stride * values.length + fixed) :: values.map encode)).1 = header :: regions := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header,regions,listHeader]
  rw [hRegions,List.cons_append]
  refine ⟨?_,?_,?_,?_⟩
  · simp only [listRun,hv,hr,GeneralPaperScalarArrayFieldCursor.targets_data,listExpected,compose]
    rfl
  · simp only [listRun,hv,hr]
  · refine ⟨List.mem_cons_self ..,?_,?_,?_,hFits⟩
    · change [header].Sublist (header :: regions)
      exact (List.nil_sublist regions).cons_cons header
    · change (cells.map Cell.region).Sublist (header :: regions)
      rw [GeneralPaperScalarFieldCursor.cells_regions A regions values hLength]
      exact (List.Sublist.refl regions).cons header
    · intro actual ha
      have he : actual = (⟨header,fixed,cells.map (fun cell => cell.region.reference)⟩ : GeneralPaperReferenceRegionSlots.Header A) := List.mem_singleton.mp ha
      subst actual
      change A * (fixed + (cells.map (fun cell => cell.region.reference)).length) ≤ A * (stride * values.length + fixed)
      rw [List.length_map,hCount]
      apply Nat.mul_le_mul_left
      nlinarith
  · change (header :: cells.map Cell.region).Perm (header :: regions)
    rw [GeneralPaperScalarFieldCursor.cells_regions A regions values hLength]

def lift {α : Type*} (S A : ℕ) (value : α → Scalar) : List α → List Scalar × ℕ
  | [] => ([],64 * (S + A + 1))
  | x :: xs =>
    let later := lift S A value xs
    (value x :: later.1,later.2 + encode (value x) + 64 * (S + A + 1))
theorem lift_data {α : Type*} (S A : ℕ) (value : α → Scalar) (values : List α) : (lift S A value values).1 = values.map value := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp only [lift,ih,List.map_cons]
theorem lift_work {α : Type*} (S A : ℕ) (value : α → Scalar) (values : List α) :
    (lift S A value values).2 = (values.map (fun x => encode (value x))).sum + (values.length + 1) * (64 * (S + A + 1)) := by
  induction values with
  | nil => simp only [lift,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
  | cons x xs ih => simp only [lift,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

def naturals (S A : ℕ) (values : List ℕ) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  let actual := lift S A Scalar.natural values
  let parsed := listRun S A 32 actual.1 regions
  ⟨parsed.values,parsed.remaining,actual.2 + parsed.work + 64 * (S + A + 1)⟩

theorem natural_plan (model : RationalCostModel) (S A : ℕ) (values : List ℕ) :
    (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values).sizes =
      A * (1 * (values.map Scalar.natural).length + 32) :: (values.map Scalar.natural).map encode := by
  rw [GeneralPaperMeasuredListBlockPlan.data]
  simp only [List.length_map,List.singleton_append]
  congr 1
  induction values with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.flatten_cons]
    rw [GeneralPaperMeasuredBlockPlan.natural_data]
    exact congrArg (List.cons (GeneralPaperEncodedScalarStorage.natBits x)) ih

theorem naturals_success (model : RationalCostModel) (S A start : ℕ) (values : List ℕ) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values)).1
    (naturals S A values (regions ++ rest)).values = some (listExpected model S A start 32 1 (values.map Scalar.natural)) ∧
      (naturals S A values (regions ++ rest)).remaining = rest ∧
      Safe regions (listExpected model S A start 32 1 (values.map Scalar.natural)) ∧
      Covered regions (listExpected model S A start 32 1 (values.map Scalar.natural)) := by
  simpa only [GeneralPaperMeasuredBlockLayout.run,natural_plan,naturals,lift_data] using
    list_success model S A start 32 1 (values.map Scalar.natural) rest (by decide)

end Blotto.GeneralPaperScalarRecordComponents

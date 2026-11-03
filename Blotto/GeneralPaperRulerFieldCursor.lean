import Blotto.GeneralPaperBooleanRowCursor

/-! Unit rulers carry no scalar payload. A priced source count is stored in
the existing reserved header word. The draw-side reader receives only memory
and root; native capacity derives the exact count without a length oracle. -/
namespace Blotto.GeneralPaperRulerFieldCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperUnifiedFieldValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def expected (A start : ℕ) (source : List Unit) : Directory A :=
  let header := GeneralPaperScalarRecordComponents.listHeader A start 32 2 source.length
  ⟨header,[⟨header,0,[FixedBinaryWord.ofNat A source.length]⟩],[]⟩

def run (model : RationalCostModel) (S A : ℕ) (source : List Unit) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  let counted := GeneralPaperMeasuredListBlockPlan.body model S (GeneralPaperEqualMeasuredLeafPlans.unit S) source
  match regions with
  | [] => ⟨none,[],counted.work + 64 * (S + A + 1)⟩
  | header :: rest =>
    let count := GeneralPaperStoredWordEncoding.word model S A counted.count
    ⟨some ⟨header,[⟨header,0,[count.1]⟩],[]⟩,rest,
      counted.work + count.2 + GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1)⟩

theorem unit_sizes (S : ℕ) (source : List Unit) :
    (source.map (fun value => (GeneralPaperEqualMeasuredLeafPlans.unit S value).sizes)).flatten = [] := by
  induction source with
  | nil => rfl
  | cons x xs ih => exact ih

theorem plan (model : RationalCostModel) (S A : ℕ) (source : List Unit) :
    (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source).sizes = [A * (2 * source.length + 32)] := by
  rw [GeneralPaperMeasuredListBlockPlan.data,unit_sizes,List.append_nil]

theorem success (model : RationalCostModel) (S A start : ℕ) (source : List Unit) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source)).1
    (run model S A source (regions ++ rest)).values = some (expected A start source) ∧
      (run model S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected A start source) ∧ Covered regions (expected A start source) := by
  dsimp only [GeneralPaperMeasuredBlockLayout.run]
  rw [plan]
  simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,List.singleton_append,
    run,GeneralPaperMeasuredListBlockPlan.body_count,expected,GeneralPaperScalarRecordComponents.listHeader]
  refine ⟨True.intro,True.intro,?_,List.Perm.refl _⟩
  refine ⟨List.mem_singleton_self _,List.Sublist.refl _,List.nil_sublist _,?_,?_⟩
  · intro header hh
    have he := List.mem_singleton.mp hh
    subst header
    change A * (0 + 1) ≤ A * (2 * source.length + 32)
    apply Nat.mul_le_mul_left
    omega
  · intro cell hc
    exact False.elim (List.not_mem_nil hc)

theorem count_fits (model : RationalCostModel) (S A start : ℕ) (source : List Unit) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source).sizes.sum < 2 ^ A) :
    source.length < 2 ^ A := by
  rw [plan] at hCap
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have hn : source.length ≤ A * source.length := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right source.length (Nat.succ_le_of_lt hA)
  nlinarith

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option ℕ × ℕ :=
  let actual := GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 0
  (actual.1.map (fun word => word.2.value),actual.2 + actual.1.elim 0 (fun word => word.1) + 64 * A + 64)

theorem read_source (model : RationalCostModel) (S A start : ℕ) (source : List Unit) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source).sizes.sum < 2 ^ A) :
    let installed := GeneralPaperUnifiedDirectoryInstallation.install model S A (expected A start source)
    (read model A installed).1 = some source.length ∧ (read model A installed).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 0).2 + 65 * A + 64 := by
  dsimp only
  obtain ⟨_,_,hs,hc⟩ := success model S A start source []
  let header : GeneralPaperReferenceRegionSlots.Header A :=
    ⟨(expected A start source).root,0,[FixedBinaryWord.ofNat A source.length]⟩
  have hHeader : header ∈ (expected A start source).headers := List.mem_singleton_self _
  have hRead := GeneralPaperUnifiedDirectoryInstallation.header_read model S A start
    (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source)
    (expected A start source) hs hc hA hCap header hHeader ⟨0,by change 0 < 1; decide⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A
    (referenceMemory (GeneralPaperUnifiedDirectoryInstallation.install model S A (expected A start source)).memory)
    (GeneralPaperUnifiedDirectoryInstallation.install model S A (expected A start source)).root 0 0).1 =
      some (⟨A,FixedBinaryWord.ofNat A source.length⟩ : Word) at hRead
  simp only [read,hRead,Option.map_some,Option.elim_some,FixedBinaryWord.value_ofNat A source.length (count_fits model S A start source hA hCap)]
  constructor
  · exact True.intro
  · ring

end Blotto.GeneralPaperRulerFieldCursor

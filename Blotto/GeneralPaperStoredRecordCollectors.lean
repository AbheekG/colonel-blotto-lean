import Blotto.GeneralPaperStoredChildRead

/-! Record descendants use the loaded child representation. These concrete
collectors need only installed memory/root and a fixed record slot. -/
namespace Blotto.GeneralPaperStoredRecordCollectors
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000

def naturals (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : GeneralPaperStoredReadStream.Result ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 index
  match child.1 with
  | none => ⟨none,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredReadStream.naturals model B loaded 32
    ⟨actual.values,actual.count,child.2 + actual.work + 64 * (A + B + 1)⟩

def word (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : Option Word × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 index
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredBooleanWordRead.read model B loaded
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

theorem naturals_trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (index : ℕ)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 index).1 = some (⟨A,loaded⟩ : Child)) :
    (naturals model A installed index).values = (GeneralPaperStoredReadStream.naturals model A loaded 32).values ∧
      (naturals model A installed index).count = (GeneralPaperStoredReadStream.naturals model A loaded 32).count ∧
      (naturals model A installed index).work = (GeneralPaperStoredChildRead.load model A installed 0 index).2 +
        (GeneralPaperStoredReadStream.naturals model A loaded 32).work + 128 * A + 64 := by
  simp only [naturals,hChild]
  refine ⟨True.intro,True.intro,?_⟩
  ring

theorem word_trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (index : ℕ)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 index).1 = some (⟨A,loaded⟩ : Child)) :
    (word model A installed index).1 = (GeneralPaperStoredBooleanWordRead.read model A loaded).1 ∧
      (word model A installed index).2 = (GeneralPaperStoredChildRead.load model A installed 0 index).2 +
        (GeneralPaperStoredBooleanWordRead.read model A loaded).2 + 128 * A + 64 := by
  simp only [word,hChild]
  constructor
  · exact True.intro
  · ring

end Blotto.GeneralPaperStoredRecordCollectors

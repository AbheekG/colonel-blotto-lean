import Blotto.GeneralPaperStoredBooleanRows

/-! Cumulative selection reads only each reached stored labelled word. The
stored row count bounds the loop; residuals are formed by Boolean borrow.
Execution receives neither decoded counts nor a source row list. -/
namespace Blotto.GeneralPaperStoredCategoricalScan
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def loop (model : RationalCostModel) (A : ℕ) (installed : Installed A) : ℕ → ℕ → List Bool → Option ℕ × ℕ
  | _,0,_ => (none,64 * (A + 1))
  | index,fuel + 1,bits =>
    let row := GeneralPaperStoredBooleanRows.read model A installed index
    match row.1 with
    | none => (none,row.2 + 64 * (A + 1))
    | some (label,word) =>
      let difference := GeneralPaperBooleanBorrow.loop bits word.2.bits false []
      if difference.borrow then
        (some label,row.2 + difference.work + GeneralPaperEncodedScalarStorage.natBits label + 128 * (A + 1))
      else
        let next := GeneralPaperNaturalScalarStep.run model A .add index 1
        let later := loop model A installed next.1 fuel difference.bits
        (later.1,row.2 + difference.work + next.2 + later.2 + 128 * (A + 1))

def price {r w : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A) :
    ℕ → List (Fin r × FixedBinaryWord w) → FixedBinaryWord w → ℕ
  | _,[],_ => 64 * (A + 1)
  | index,row :: rest,word =>
    let difference := GeneralPaperBooleanBorrow.subtract word row.2
    if difference.2.1 then
      (GeneralPaperStoredBooleanRows.read model A installed index).2 + difference.2.2 +
        GeneralPaperEncodedScalarStorage.natBits row.1.val + 128 * (A + 1)
    else
      (GeneralPaperStoredBooleanRows.read model A installed index).2 + difference.2.2 +
        (GeneralPaperNaturalScalarStep.run model A .add index 1).2 +
        price model A installed (index + 1) rest difference.1 + 128 * (A + 1)

theorem loop_source {r w : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (start : ℕ) (rows : List (Fin r × FixedBinaryWord w)) (word : FixedBinaryWord w)
    (hRows : ∀ index : Fin rows.length,
      (GeneralPaperStoredBooleanRows.read model A installed (start + index.val)).1 =
        some ((rows[index.val]).1.val,(⟨w,(rows[index.val]).2⟩ : Word))) :
    (loop model A installed start rows.length word.bits).1 =
      (GeneralPaperBooleanCategoricalSelect.run rows word).1.map Fin.val ∧
      (loop model A installed start rows.length word.bits).2 = price model A installed start rows word := by
  induction rows generalizing start word with
  | nil => exact ⟨rfl,rfl⟩
  | cons row rows ih =>
    have hHead := hRows ⟨0,by simp only [List.length_cons]; omega⟩
    simp only [Nat.add_zero,List.getElem_cons_zero] at hHead
    have hTail : ∀ index : Fin rows.length,
        (GeneralPaperStoredBooleanRows.read model A installed (start + 1 + index.val)).1 =
          some ((rows[index.val]).1.val,(⟨w,(rows[index.val]).2⟩ : Word)) := by
      intro index
      have h := hRows ⟨index.val + 1,by simp only [List.length_cons]; omega⟩
      simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 index.val] using h
    have hLater := ih (start + 1) (GeneralPaperBooleanBorrow.subtract word row.2).1 hTail
    have hBorrow : (GeneralPaperBooleanBorrow.loop word.bits row.2.bits false []).borrow =
        (GeneralPaperBooleanBorrow.subtract word row.2).2.1 := rfl
    have hBits : (GeneralPaperBooleanBorrow.loop word.bits row.2.bits false []).bits =
        (GeneralPaperBooleanBorrow.subtract word row.2).1.bits := rfl
    have hWork : (GeneralPaperBooleanBorrow.loop word.bits row.2.bits false []).work =
        (GeneralPaperBooleanBorrow.subtract word row.2).2.2 := rfl
    simp only [List.length_cons,loop,hHead,hBorrow,hBits,hWork]
    by_cases hb : (GeneralPaperBooleanBorrow.subtract word row.2).2.1 = true
    · simp only [hb,ite_true,GeneralPaperBooleanCategoricalSelect.run,price,Option.map_some,and_self]
    · have hf : (GeneralPaperBooleanBorrow.subtract word row.2).2.1 = false := Bool.eq_false_of_not_eq_true hb
      simp only [hf,Bool.false_eq_true,ite_false,GeneralPaperBooleanCategoricalSelect.run,price,
        GeneralPaperNaturalScalarStep.data,GeneralPaperNaturalScalarStep.Op.apply,hLater.1,hLater.2,and_self]

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) (bits : List Bool) : Option ℕ × ℕ :=
  let count := GeneralPaperHeaderCountReadback.count model A installed installed.root
  match count.1 with
  | none => (none,count.2 + 64 * (A + 1))
  | some size =>
    let actual := loop model A installed 0 size bits
    (actual.1,count.2 + actual.2 + 128 * (A + 1))

theorem source {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (rows : List (Fin r × FixedBinaryWord w))
    (hRead : Readback model A installed (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).root.reference)
    (word : FixedBinaryWord w) :
    (run model A installed word.bits).1 = (GeneralPaperBooleanCategoricalSelect.run rows word).1.map Fin.val ∧
      (run model A installed word.bits).2 = (GeneralPaperHeaderCountReadback.count model A installed installed.root).2 +
        price model A installed 0 rows word + 128 * (A + 1) := by
  have hCount := GeneralPaperStoredBooleanRows.count_source model S A start installed full hContract rows hHeaders hRoot
  have hEach : ∀ index : Fin rows.length,
      (GeneralPaperStoredBooleanRows.read model A installed (0 + index.val)).1 =
        some ((rows[index.val]).1.val,(⟨w,(rows[index.val]).2⟩ : Word)) := by
    intro index
    obtain ⟨_,hv,_⟩ := GeneralPaperStoredBooleanRows.source model S A start installed full hContract rows hRead hHeaders hRoot index
    simpa only [Nat.zero_add] using hv
  obtain ⟨hv,hw⟩ := loop_source model A installed 0 rows word hEach
  simp only [run,hCount,hv,hw,and_self]

end Blotto.GeneralPaperStoredCategoricalScan

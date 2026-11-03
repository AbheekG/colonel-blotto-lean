import Blotto.GeneralPaperStoredBooleanRowsWork

/-! Complete reached-row categorical work includes every actual selected
row, Boolean borrow, index increment and control step. The stored list owner
supplies its loop extent and count-access capacity in the enclosing memory. -/
namespace Blotto.GeneralPaperStoredCategoricalWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def perRow (model : RationalCostModel) (A w r : ℕ) : ℕ :=
  GeneralPaperStoredBooleanRowsWork.bound model A w r + 22 * w + 8 + GeneralPaperEncodedScalarStorage.natBits r +
    GeneralPaperStoredStreamWork.stepBound model A + 128 * (A + 1)

def bound (model : RationalCostModel) (A w r count : ℕ) : ℕ :=
  count * perRow model A w r + GeneralPaperStoredCountReadWork.bound model A + 192 * (A + 1)

theorem price_bound {r w : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (rows : List (Fin r × FixedBinaryWord w)) (start : ℕ) (word : FixedBinaryWord w)
    (hEnd : start + rows.length < 2 ^ A)
    (hReads : ∀ index : Fin rows.length,(GeneralPaperStoredBooleanRows.read model A installed (start + index.val)).2 ≤
      GeneralPaperStoredBooleanRowsWork.bound model A w r) :
    GeneralPaperStoredCategoricalScan.price model A installed start rows word ≤ rows.length * perRow model A w r + 64 * (A + 1) := by
  induction rows generalizing start word with
  | nil => simp only [GeneralPaperStoredCategoricalScan.price,List.length_nil,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons row rows ih =>
    have hHead := hReads ⟨0,by simp only [List.length_cons]; omega⟩
    simp only [Nat.add_zero] at hHead
    have hLabel : GeneralPaperEncodedScalarStorage.natBits row.1.val ≤ GeneralPaperEncodedScalarStorage.natBits r :=
      Nat.add_le_add_left (binaryWordWidth_mono row.1.isLt.le) 1
    have hStep := GeneralPaperStoredStreamWork.increment_work model A start (by simp only [List.length_cons] at hEnd; omega)
    have hTail : ∀ index : Fin rows.length,(GeneralPaperStoredBooleanRows.read model A installed (start + 1 + index.val)).2 ≤
        GeneralPaperStoredBooleanRowsWork.bound model A w r := by
      intro index
      have h := hReads ⟨index.val + 1,by simp only [List.length_cons]; omega⟩
      simpa only [Nat.add_assoc,Nat.add_comm 1 index.val] using h
    have hLater := ih (start + 1) (GeneralPaperBooleanBorrow.subtract word row.2).1
      (by simp only [List.length_cons] at hEnd; omega) hTail
    simp only [GeneralPaperStoredCategoricalScan.price,GeneralPaperBooleanBorrow.subtract_work,List.length_cons]
    split_ifs
    · unfold perRow
      nlinarith only [hHead,hLabel,Nat.zero_le (rows.length * perRow model A w r)]
    · unfold perRow at *
      nlinarith only [hHead,hStep,hLater]

theorem work {r w : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed) (rows : List (Fin r × FixedBinaryWord w))
    (hRead : Readback model A installed (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows))
    (hHeaders : ∀ h ∈ (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).headers,h ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRowCursor.rowsExpected model S A start rows).root.reference) (word : FixedBinaryWord w) :
    (GeneralPaperStoredCategoricalScan.run model A installed word.bits).2 ≤ bound model A w r rows.length := by
  have hFits := GeneralPaperStoredListReadWork.capacity ctx start
    (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes) (GeneralPaperBooleanRowCursor.expected model S A) rows hHeaders
  have hEach : ∀ index : Fin rows.length,(GeneralPaperStoredBooleanRows.read model A installed (0 + index.val)).2 ≤
      GeneralPaperStoredBooleanRowsWork.bound model A w r := by
    intro index
    simpa only [Nat.zero_add] using GeneralPaperStoredBooleanRowsWork.work model S A layoutStart start plan full installed ctx rows hRead hHeaders hRoot index
  have hPrice := price_bound model A installed rows 0 word (by simpa only [Nat.zero_add] using hFits) hEach
  have hCount := GeneralPaperStoredListReadWork.count_work model S A layoutStart start plan full installed ctx
    (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes) (GeneralPaperBooleanRowCursor.expected model S A) rows hHeaders hRoot
  rw [(GeneralPaperStoredCategoricalScan.source model S A start installed full ctx.contract rows hRead hHeaders hRoot word).2]
  unfold bound
  omega

end Blotto.GeneralPaperStoredCategoricalWork

import Blotto.GeneralPaperStoredInterpolation

/-! Load the actual original budget, selected segment rows and compute the
materialized scaled group vector. No source prepared cache or decoded matrix
is an input to the executed producer. -/
namespace Blotto.GeneralPaperStoredPreparedGroups
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) (midpoint : ℚ) : Option (Array ℚ) × ℕ :=
  let budget := GeneralPaperStoredPreparedRead.budget model A installed
  match budget.1 with
  | none => (none,budget.2 + 64 * (A + 1))
  | some value =>
    let child := GeneralPaperStoredChildRead.load model A installed 0 1
    match child.1 with
    | none => (none,budget.2 + child.2 + 64 * (A + 1))
    | some ⟨B,loaded⟩ =>
      let left := GeneralPaperStoredEndpointRows.read model B loaded .left index
      let right := GeneralPaperStoredEndpointRows.read model B loaded .right index
      match left.values,right.values with
      | some ps,some qs =>
        let actual := GeneralPaperStoredInterpolation.array model B value midpoint ps qs
        (actual.1,budget.2 + child.2 + left.work + right.work + actual.2 + 128 * (A + B + 1))
      | _,_ => (none,budget.2 + child.2 + left.work + right.work + 64 * (A + B + 1))

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference)
    (index : Fin (count l)) (fresh : Fin prepared.midpointBits → Bool) :
    ∃ root : FixedBinaryWord A,
      (run model A installed index.val (GeneralPaperEqualPreparedCache.midpoint prepared fresh)).1 =
        some (GeneralPaperEqualCachedEmission.scaledPoint prepared index fresh).data ∧
      (run model A installed index.val (GeneralPaperEqualPreparedCache.midpoint prepared fresh)).2 =
        (GeneralPaperStoredPreparedRead.budget model A installed).2 + (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredEndpointRows.read model A (GeneralPaperStoredScalarRead.atRoot installed root) .left index.val).work +
        (GeneralPaperStoredEndpointRows.read model A (GeneralPaperStoredScalarRead.atRoot installed root) .right index.val).work +
        (GeneralPaperStoredInterpolation.array model A prepared.budget (GeneralPaperEqualPreparedCache.midpoint prepared fresh)
          (prepared.segments.left.read index).data.toList (prepared.segments.right.read index).data.toList).2 + 256 * A + 128 := by
  have hBudget := (GeneralPaperStoredPreparedRead.budget_source model S A start installed prepared hRead hRoot).1
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨1,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .segments fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded full := hContract
  change (GeneralPaperStoredChildRead.load model A installed 0 1).1 =
    some (⟨A,loaded⟩ : GeneralPaperStoredChildRead.Child) at hLoad
  obtain ⟨_,hLeft,_,_⟩ := GeneralPaperStoredEndpointRows.source model S A fieldStart loaded full hChildContract prepared.segments
    hChildRead (fun header hh => hHeaders header (hChildHeaders header hh)) rfl .left index
  obtain ⟨_,hRight,_,_⟩ := GeneralPaperStoredEndpointRows.source model S A fieldStart loaded full hChildContract prepared.segments
    hChildRead (fun header hh => hHeaders header (hChildHeaders header hh)) rfl .right index
  simp only [GeneralPaperStoredEndpointRows.matrix] at hLeft hRight
  have hArray := (GeneralPaperStoredInterpolation.array_source model A prepared.budget
    (GeneralPaperEqualPreparedCache.midpoint prepared fresh) (prepared.segments.left.read index) (prepared.segments.right.read index)).1
  have hTarget : (FixedArrayTable.ofFn (fun g => prepared.budget *
      ((1 - GeneralPaperEqualPreparedCache.midpoint prepared fresh) * (prepared.segments.left.read index).read g +
      GeneralPaperEqualPreparedCache.midpoint prepared fresh * (prepared.segments.right.read index).read g))).data =
      (GeneralPaperEqualCachedEmission.scaledPoint prepared index fresh).data := by
    simp only [GeneralPaperEqualCachedEmission.scaledPoint,GeneralPaperEqualPreparedCache.groupPoint,FixedArrayTable.read_ofFn]
  refine ⟨child.root.reference,?_,?_⟩
  · simpa only [run,hBudget,hLoad,hLeft,hRight] using hArray.trans (congrArg some hTarget)
  · simp only [run,hBudget,hLoad,hLeft,hRight]
    ring

end Blotto.GeneralPaperStoredPreparedGroups

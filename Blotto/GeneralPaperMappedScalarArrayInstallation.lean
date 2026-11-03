import Blotto.GeneralPaperScalarArrayFieldInstallation

/-! One returned RAM/root combines source mapping, forward field extraction
and actual scalar-array installation. Existing measured rational/natural
array prefixes supply all fields; subsequent regions are left untouched.
Every indexed read from the same return recovers the actual source value. -/
namespace Blotto.GeneralPaperMappedScalarArrayInstallation
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperScalarArrayFieldInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def finish (model : RationalCostModel) (S A prefixWork : ℕ) (fields : GeneralPaperScalarArrayFieldCursor.Fields A) : Installed A :=
  let actual := GeneralPaperScalarArrayFieldInstallation.install model S A fields
  ⟨actual.references,actual.payloads,actual.root,prefixWork + actual.work + 64 * (S + A + 1)⟩

structure Result (A : ℕ) where
  values : Option (Installed A)
  remaining : List (Region A)
  work : ℕ

def run {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (lift : α → Scalar)
    (source : FixedArrayTable n α) (regions : List (Region A)) : Result A :=
  let parsed := GeneralPaperMappedScalarArrayCursor.run S A lift source regions
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some fields =>
    let actual := finish model S A parsed.work fields
    ⟨some actual,parsed.remaining,actual.work⟩

theorem on_parsed {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (lift : α → Scalar)
    (source : FixedArrayTable n α) (regions : List (Region A)) (fields : GeneralPaperScalarArrayFieldCursor.Fields A)
    (hParsed : (GeneralPaperMappedScalarArrayCursor.run S A lift source regions).values = some fields) :
    (run model S A lift source regions).values =
        some (finish model S A (GeneralPaperMappedScalarArrayCursor.run S A lift source regions).work fields) ∧
      (run model S A lift source regions).remaining = (GeneralPaperMappedScalarArrayCursor.run S A lift source regions).remaining ∧
      (run model S A lift source regions).work =
        (finish model S A (GeneralPaperMappedScalarArrayCursor.run S A lift source regions).work fields).work := by
  simp only [run,hParsed,and_self]

theorem expected_read (model : RationalCostModel) (S A start prefixWork : ℕ) (values : List Scalar) (hA : 0 < A)
    (hCap : start + (A * (64 + values.length) :: values.map encode).sum < 2 ^ A) (j : Fin values.length) :
    (GeneralPaperScalarArrayFieldInstallation.read model A
      (finish model S A prefixWork (GeneralPaperMappedScalarArrayCursor.expected model S A start values)) j.val).1 =
      some values[j.val] :=
  GeneralPaperScalarArrayFieldInstallation.expected_read model S A start values hA hCap j

theorem rational {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℚ)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A
      (GeneralPaperMeasuredBlockPlan.rational model S) source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source)).1 ++ rest
    ∃ output : Installed A,(run model S A Scalar.rational source regions).values = some output ∧
      (run model S A Scalar.rational source regions).remaining = rest ∧
      output.work = (run model S A Scalar.rational source regions).work ∧
      ∀ j : Fin n,(GeneralPaperScalarArrayFieldInstallation.read model A output j.val).1 = some (Scalar.rational (source.read j)) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source)).1 ++ rest
  let fields := GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)
  obtain ⟨hParsed,hRest,_⟩ := GeneralPaperMappedScalarArrayCursor.rational_success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A Scalar.rational source regions fields hParsed
  refine ⟨_,hv,hr.trans hRest,hw.symm,?_⟩
  intro j
  have hIndex : j.val < (source.data.toList.map Scalar.rational).length := by
    rw [List.length_map,Array.length_toList,source.size]
    exact j.isLt
  rw [GeneralPaperMappedScalarArrayCursor.rational_plan] at hCap
  have h := expected_read model S A start (GeneralPaperMappedScalarArrayCursor.run S A Scalar.rational source regions).work
    (source.data.toList.map Scalar.rational) hA hCap ⟨j.val,hIndex⟩
  simpa only [List.getElem_map,Array.getElem_toList,FixedArrayTable.read] using h

theorem natural {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℕ)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A
      (GeneralPaperMeasuredBlockPlan.natural model S) source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source)).1 ++ rest
    ∃ output : Installed A,(run model S A Scalar.natural source regions).values = some output ∧
      (run model S A Scalar.natural source regions).remaining = rest ∧
      output.work = (run model S A Scalar.natural source regions).work ∧
      ∀ j : Fin n,(GeneralPaperScalarArrayFieldInstallation.read model A output j.val).1 = some (Scalar.natural (source.read j)) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
    (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source)).1 ++ rest
  let fields := GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural)
  obtain ⟨hParsed,hRest,_⟩ := GeneralPaperMappedScalarArrayCursor.natural_success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A Scalar.natural source regions fields hParsed
  refine ⟨_,hv,hr.trans hRest,hw.symm,?_⟩
  intro j
  have hIndex : j.val < (source.data.toList.map Scalar.natural).length := by
    rw [List.length_map,Array.length_toList,source.size]
    exact j.isLt
  rw [GeneralPaperMappedScalarArrayCursor.natural_plan] at hCap
  have h := expected_read model S A start (GeneralPaperMappedScalarArrayCursor.run S A Scalar.natural source regions).work
    (source.data.toList.map Scalar.natural) hA hCap ⟨j.val,hIndex⟩
  simpa only [List.getElem_map,Array.getElem_toList,FixedArrayTable.read] using h

end Blotto.GeneralPaperMappedScalarArrayInstallation

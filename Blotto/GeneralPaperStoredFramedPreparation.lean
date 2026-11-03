import Blotto.GeneralPaperStoredParsedPreparation

/-! One priced accuracy-frame read feeds the parsed-exponent continuation.
The final result keeps only installed memory/root, its width and untouched
input suffix. Reading/preparing accuracy never repeats after parsing. -/
namespace Blotto.GeneralPaperStoredFramedPreparation
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (width prepare input)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

abbrev Output := Σ A : ℕ, Installed A × List Bool

def finish (A prefixWork : ℕ) {B : ℕ} (inner : Installed B) (suffix : List Bool) : Output :=
  ⟨B,GeneralPaperSamplerRecordInstallation.attach A B prefixWork inner,suffix⟩

def run {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (frame : List Bool) : Option Output × ℕ :=
  let parsed := GeneralPaperBinaryAccuracy.read id A frame
  match parsed.1 with
  | none => (none,parsed.2 + 64 * (A + 1))
  | some (actual,suffix) =>
    let made := GeneralPaperStoredParsedPreparation.run model A K values v hv budget actual
    match made.1 with
    | none => (none,parsed.2 + made.2 + 64 * (A + 1))
    | some inner =>
      let output := finish A parsed.2 inner suffix
      (some output,output.2.1.work)

theorem on_parsed {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (frame suffix : List Bool) (parsed : Parsed)
    (hRead : (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix))
    (inner : Installed (width model A K values v hv budget parsed))
    (hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner) :
    (run model A K values v hv budget frame).1 = some (finish A (GeneralPaperBinaryAccuracy.read id A frame).2 inner suffix) ∧
      (run model A K values v hv budget frame).2 =
        (finish A (GeneralPaperBinaryAccuracy.read id A frame).2 inner suffix).2.1.work := by
  simp only [run,hRead,hBuild,and_self]

theorem every_returned {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (frame : List Bool)
    (returned : Output) (hReturn : (run model A K values v hv budget frame).1 = some returned) :
    ∃ (parsed : Parsed) (suffix : List Bool) (inner : Installed (width model A K values v hv budget parsed)),
      (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix) ∧
      (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner ∧
      returned = finish A (GeneralPaperBinaryAccuracy.read id A frame).2 inner suffix ∧
      returned.2.1.work = (run model A K values v hv budget frame).2 := by
  unfold run at hReturn
  cases hRead : (GeneralPaperBinaryAccuracy.read id A frame).1 with
  | none => simp only [hRead] at hReturn; cases hReturn
  | some result =>
    rcases result with ⟨parsed,suffix⟩
    simp only [hRead] at hReturn
    cases hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 with
    | none => simp only [hBuild] at hReturn; cases hReturn
    | some inner =>
      simp only [hBuild] at hReturn
      have hEq := Option.some.inj hReturn
      refine ⟨parsed,suffix,inner,rfl,hBuild,hEq.symm,?_⟩
      rw [← hEq]
      exact (on_parsed model A K values v hv budget frame suffix parsed hRead inner hBuild).2.symm

theorem rejected {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (frame : List Bool)
    (hRead : (GeneralPaperBinaryAccuracy.read id A frame).1 = none) :
    run model A K values v hv budget frame = (none,(GeneralPaperBinaryAccuracy.read id A frame).2 + 64 * (A + 1)) := by
  simp only [run,hRead]

theorem complete {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (accuracy : BinaryAccuracyInput) (suffix : List Bool) :
    ∃ (parsed : Parsed) (inner : Installed (width model A K values v hv budget parsed)),
      (GeneralPaperBinaryAccuracy.read id A (BinaryAccuracyFrame.encode accuracy ++ suffix)).1 = some (parsed,suffix) ∧
      parsed.words.numeric = accuracy ∧
      (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner ∧
      (run model A K values v hv budget (BinaryAccuracyFrame.encode accuracy ++ suffix)).1 =
        some (finish A (GeneralPaperBinaryAccuracy.read id A (BinaryAccuracyFrame.encode accuracy ++ suffix)).2 inner suffix) ∧
      (finish A (GeneralPaperBinaryAccuracy.read id A (BinaryAccuracyFrame.encode accuracy ++ suffix)).2 inner suffix).2.1.work =
        (run model A K values v hv budget (BinaryAccuracyFrame.encode accuracy ++ suffix)).2 := by
  obtain ⟨parsed,hRead,hNumeric⟩ := GeneralPaperBinaryAccuracy.read_complete id A accuracy suffix
  obtain ⟨inner,hBuild,_,_⟩ := GeneralPaperStoredParsedPreparation.source model A K values v hv budget parsed
  obtain ⟨hRun,hWork⟩ := on_parsed model A K values v hv budget _ suffix parsed hRead inner hBuild
  exact ⟨parsed,inner,hRead,hNumeric,hBuild,hRun,hWork.symm⟩

theorem finished_refines {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed)
    (inner : Installed (width model A K values v hv budget parsed))
    (hBuild : (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).1 = some inner)
    (prefixWork : ℕ) (suffix : List Bool) :
    GeneralPaperStoredSelectedDraw.Refines model (width model A K values v hv budget parsed)
      (finish A prefixWork inner suffix).2.1 (prepare model A K values v hv budget parsed).1.branch :=
  GeneralPaperStoredSelectedExt.attach model A _ prefixWork inner _
    (GeneralPaperStoredParsedPreparation.every_returned model A K values v hv budget parsed inner hBuild).2

end Blotto.GeneralPaperStoredFramedPreparation

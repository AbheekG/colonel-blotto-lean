import Blotto.GeneralPaperStoredOuterMarker

/-! The common runtime takes only actual retained memory and fresh-bit
inputs. It prices the stored marker read and invokes the corresponding
actual outer reader; an invalid marker or unfinished draw yields no output. -/
namespace Blotto.GeneralPaperStoredSelectedDraw
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def run {S : Type*} (model : RationalCostModel) (A : ℕ) (outer : Installed A) (cap : ℕ)
    (tape : ℕ → List Bool) (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result (Array ℚ) S :=
  let marker := GeneralPaperStoredOuterMarker.read model A outer
  match marker.1 with
  | none => ⟨none,state,0,marker.2 + 64 * (A + 1)⟩
  | some tag =>
    if tag = 0 then
      let actual := GeneralPaperStoredDominantOuterDraw.run model A outer
      ⟨actual.values,state,0,marker.2 + actual.work + 64 * (A + 1)⟩
    else if tag = 1 then
      let actual := GeneralPaperStoredGroupedOuterDraw.run model A outer cap tape next state
      ⟨actual.output,actual.state,actual.reads,marker.2 + actual.work + 64 * (A + 1)⟩
    else ⟨none,state,0,marker.2 + 64 * (A + 1)⟩

theorem dominant {S : Type*} (model : RationalCostModel) (A : ℕ) (outer : Installed A) (cap : ℕ)
    (tape : ℕ → List Bool) (next : S → Bool × S) (state : S)
    (hMarker : (GeneralPaperStoredOuterMarker.read model A outer).1 = some 0) :
    (run model A outer cap tape next state).output = (GeneralPaperStoredDominantOuterDraw.run model A outer).values ∧
      (run model A outer cap tape next state).state = state ∧ (run model A outer cap tape next state).reads = 0 ∧
      (run model A outer cap tape next state).work = (GeneralPaperStoredOuterMarker.read model A outer).2 +
        (GeneralPaperStoredDominantOuterDraw.run model A outer).work + 64 * (A + 1) := by
  simp [run,hMarker]

theorem grouped {S : Type*} (model : RationalCostModel) (A : ℕ) (outer : Installed A) (cap : ℕ)
    (tape : ℕ → List Bool) (next : S → Bool × S) (state : S)
    (hMarker : (GeneralPaperStoredOuterMarker.read model A outer).1 = some 1) :
    (run model A outer cap tape next state).output = (GeneralPaperStoredGroupedOuterDraw.run model A outer cap tape next state).output ∧
      (run model A outer cap tape next state).state = (GeneralPaperStoredGroupedOuterDraw.run model A outer cap tape next state).state ∧
      (run model A outer cap tape next state).reads = (GeneralPaperStoredGroupedOuterDraw.run model A outer cap tape next state).reads ∧
      (run model A outer cap tape next state).work = (GeneralPaperStoredOuterMarker.read model A outer).2 +
        (GeneralPaperStoredGroupedOuterDraw.run model A outer cap tape next state).work + 64 * (A + 1) := by
  simp [run,hMarker]

def Refines {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : GeneralPaperEqualBitBranch.Prepared v k budget → Prop
  | .dominant _ _ row _ => ∀ cap tape (fresh : List Bool),
      (run model A outer cap tape GeneralPaperBooleanFreshWord.nextList fresh).output = some row.data ∧
        (run model A outer cap tape GeneralPaperBooleanFreshWord.nextList fresh).reads = 0
  | .grouped _ sampler _ _ => ∀ cap tape fresh,
      (run model A outer cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
        GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
          (GeneralPaperEqualFullBitDraw.run sampler.categorical model sampler.address cap tape fresh).output.map RationalResourceArray.data ∧
        (run model A outer cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
          GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads =
            (GeneralPaperEqualFullBitDraw.run sampler.categorical model sampler.address cap tape fresh).reads

theorem from_contract {n : ℕ} (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : GeneralPaperEqualBitBranch.Prepared v k budget)
    (hCore : GeneralPaperStoredSelectedConstruction.Contract model A outer p)
    (hMarker : (GeneralPaperStoredOuterMarker.read model A outer).1 = some (GeneralPaperStoredOuterMarker.branchTag p)) :
    Refines model A outer p := by
  cases p with
  | dominant chosen heavy row correct =>
    intro cap tape fresh
    have h := dominant model A outer cap tape GeneralPaperBooleanFreshWord.nextList fresh hMarker
    exact ⟨h.1.trans hCore.1,h.2.2.1⟩
  | grouped small sampler hK hB =>
    intro cap tape fresh
    have h := grouped model A outer cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh) hMarker
    have hSource := hCore cap tape fresh
    exact ⟨h.1.trans hSource.1,h.2.2.1.trans hSource.2⟩

theorem every_returned {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S a).1 = some returned) :
    Refines model a.address returned a.branch :=
  from_contract model a.address returned a.branch
    (GeneralPaperStoredSelectedConstruction.every_returned model W S k values v hv budget a returned hReturn)
    (GeneralPaperStoredOuterMarker.selected_return model W S k values v hv budget a returned hReturn)

end Blotto.GeneralPaperStoredSelectedDraw

import Blotto.GeneralPaperStoredFreshDecoder

/-! An actual prepared-root midpoint draw loads its retained controls, reads
exactly the stored fresh-bit count and assembles using the stored denominator
count. Source objects below are correctness observers only. -/
namespace Blotto.GeneralPaperStoredMidpointRead
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def run {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result ℚ S :=
  let controls := GeneralPaperStoredPreparedRead.controls model A installed
  match controls.values with
  | some (_ :: _ :: bits :: count :: _) =>
    let decoded := GeneralPaperStoredFreshDecoder.run model A bits next state
    let assembled := GeneralPaperStoredMidpointAssembly.run model A count decoded.value
    ⟨some assembled.1,decoded.state,decoded.reads,controls.work + decoded.work + assembled.2 + 128 * (A + 1)⟩
  | _ => ⟨none,state,0,controls.work + 64 * (A + 1)⟩

theorem on_controls {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) (D range bits count : ℕ)
    (hControls : (GeneralPaperStoredPreparedRead.controls model A installed).values = some [D,range,bits,count]) :
    (run model A installed next state).output = some (GeneralPaperStoredMidpointAssembly.run model A count
      (GeneralPaperStoredFreshDecoder.run model A bits next state).value).1 ∧
      (run model A installed next state).state = (GeneralPaperStoredFreshDecoder.run model A bits next state).state ∧
      (run model A installed next state).reads = bits ∧
      (run model A installed next state).work = (GeneralPaperStoredPreparedRead.controls model A installed).work +
        (GeneralPaperStoredFreshDecoder.run model A bits next state).work +
        (GeneralPaperStoredMidpointAssembly.run model A count (GeneralPaperStoredFreshDecoder.run model A bits next state).value).2 + 128 * (A + 1) := by
  simp only [run,hControls,GeneralPaperStoredFreshDecoder.reads,and_self]

theorem source {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference)
    (fresh : Fin prepared.midpointBits → Bool) :
    (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
      some (GeneralPaperEqualPreparedCache.midpoint prepared fresh) ∧
      (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = prepared.midpointBits ∧
      (run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work =
        (GeneralPaperStoredPreparedRead.controls model A installed).work +
        (GeneralPaperStoredFreshDecoder.run model A prepared.midpointBits GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work +
        (GeneralPaperStoredMidpointAssembly.run model A prepared.midpointCount (balancedBitIndex prepared.midpointBits fresh).val).2 + 128 * (A + 1) := by
  obtain ⟨_,hControls,_,_⟩ := GeneralPaperStoredPreparedRead.controls_source model S A start installed full hContract prepared hRead hHeaders hRoot
  obtain ⟨hv,hs,hr,hw⟩ := on_controls model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)
    prepared.D prepared.rangeBits prepared.midpointBits prepared.midpointCount hControls
  obtain ⟨hRank,hState,_⟩ := GeneralPaperStoredFreshDecoder.source model A prepared.midpointBits fresh
  rw [hRank,GeneralPaperStoredMidpointAssembly.source] at hv
  rw [hRank] at hw
  exact ⟨hv,hs.trans hState,hr,hw⟩

end Blotto.GeneralPaperStoredMidpointRead

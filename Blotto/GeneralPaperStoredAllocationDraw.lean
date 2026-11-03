import Blotto.GeneralPaperStoredPostselection

/-! Complete actual stored draw: first-success rejection, loaded midpoint,
selected endpoint interpolation and stored-route full allocation emission.
The observation cap never causes a fallback allocation. -/
namespace Blotto.GeneralPaperStoredAllocationDraw
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (cap : ℕ) (tape : ℕ → List Bool)
    (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result (Array ℚ) S :=
  let categorical := GeneralPaperStoredSamplerRejection.run model A installed cap tape
  match categorical.output with
  | none => ⟨none,state,categorical.reads,categorical.work + 64 * (A + 1)⟩
  | some index =>
    let produced := GeneralPaperStoredPostselection.run model A installed index next state
    ⟨produced.output,produced.state,categorical.reads + produced.reads,categorical.work + produced.work + 128 * (A + 1)⟩

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler).sizes.sum < 2 ^ A)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool)
    (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
        (GeneralPaperEqualFullBitDraw.run sampler.categorical model A cap tape fresh).output.map RationalResourceArray.data ∧
      (run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
        GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads =
          (GeneralPaperEqualFullBitDraw.run sampler.categorical model A cap tape fresh).reads := by
  obtain ⟨_,hStored,hReads,_⟩ := GeneralPaperStoredSamplerRejection.source model S A start installed sampler hContract hRoot hA hCap cap tape
  obtain ⟨hOld,hOldReads⟩ := GeneralPaperEqualBooleanRejection.data sampler.categorical cap tape
  have hData : (GeneralPaperStoredSamplerRejection.run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).output =
      (GeneralPaperEqualBooleanRejection.run sampler.categorical cap tape).output.map Fin.val := by
    rw [hOld,Option.map_map]
    exact hStored
  have hCount := hReads.trans hOldReads.symm
  simp only [run,hData]
  cases h : (GeneralPaperEqualBooleanRejection.run sampler.categorical cap tape).output with
  | none => simp only [h,Option.map_none,GeneralPaperEqualFullBitDraw.run,hCount,and_self]
  | some index =>
    obtain ⟨hp,_,hr,_⟩ := GeneralPaperStoredPostselection.source model S A start installed sampler hContract hRoot index fresh
    simp only [h,Option.map_some,hp,hr,GeneralPaperEqualFullBitDraw.run,GeneralPaperEqualBitPostprocessing.data,
      GeneralPaperEqualBitPostprocessing.reads,hCount,and_self]

def Refines (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) : Prop :=
  ∀ cap tape fresh,
    (run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
        (GeneralPaperEqualFullBitDraw.run sampler.categorical model A cap tape fresh).output.map RationalResourceArray.data ∧
      (run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
        GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads =
          (GeneralPaperEqualFullBitDraw.run sampler.categorical model A cap tape fresh).reads

theorem every_returned (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned) :
    Refines model sampler.address returned sampler := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact source model S sampler.address 0 returned sampler hContract hRoot hA (by simpa only [Nat.zero_add] using hCap)

end Blotto.GeneralPaperStoredAllocationDraw

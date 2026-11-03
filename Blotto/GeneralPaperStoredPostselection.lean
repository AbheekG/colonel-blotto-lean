import Blotto.GeneralPaperStoredSamplerEmission

/-! Actual sampler-root postselection now produces the whole rational
allocation: loaded midpoint controls, selected endpoints, original budget,
materialized groups, stored routes and every output coordinate. -/
namespace Blotto.GeneralPaperStoredPostselection
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ)
    (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result (Array ℚ) S :=
  let groups := GeneralPaperStoredSamplerGroups.draw model A installed index next state
  match groups.output with
  | none => ⟨none,groups.state,groups.reads,groups.work + 64 * (A + 1)⟩
  | some values =>
    let emitted := GeneralPaperStoredSamplerEmission.run model A installed values
    ⟨emitted.values,groups.state,groups.reads,groups.work + emitted.work + 128 * (A + 1)⟩

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (run model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
      some (GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) A index fresh).1.data ∧
      (run model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (run model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = sampler.prepared.midpointBits ∧
      (run model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work =
        (GeneralPaperStoredSamplerGroups.draw model A installed index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work +
        (GeneralPaperStoredSamplerEmission.run model A installed (GeneralPaperEqualCachedEmission.scaledPoint sampler.prepared index fresh).data).work + 128 * (A + 1) := by
  obtain ⟨hGroups,hState,hReads,_⟩ := GeneralPaperStoredSamplerGroups.draw_source model S A start installed sampler hContract hRoot index fresh
  obtain ⟨_,hOutput,_,_⟩ := GeneralPaperStoredSamplerEmission.source model S A start installed sampler hContract hRoot
    (GeneralPaperEqualCachedEmission.scaledPoint sampler.prepared index fresh)
  simp only [run,hGroups,hState,hReads,hOutput,GeneralPaperEqualCachedEmission.emit_data,and_self]

theorem every_returned (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned)
    (index : Fin (count l)) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (run model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
      some (GeneralPaperEqualCachedEmission.emit sampler.prepared model (fun w => w) sampler.address index fresh).1.data ∧
      (run model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).state = [] ∧
      (run model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads = sampler.prepared.midpointBits ∧
      (run model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work =
        (GeneralPaperStoredSamplerGroups.draw model sampler.address returned index.val GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work +
        (GeneralPaperStoredSamplerEmission.run model sampler.address returned (GeneralPaperEqualCachedEmission.scaledPoint sampler.prepared index fresh).data).work +
          128 * (sampler.address + 1) := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact source model S sampler.address 0 returned sampler hContract hRoot index fresh

end Blotto.GeneralPaperStoredPostselection

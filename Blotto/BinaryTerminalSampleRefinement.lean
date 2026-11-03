import Blotto.BinaryTerminalBudget
import Blotto.BinaryGroupSamplerTransport
import Blotto.GroupEmissionTransport
import Blotto.AllocationProgramMappedSample
import Blotto.RationalTerminalProgram

/-! The native terminal output is exactly the retained original grouping
program sample, including its selected small coupling and syntactic fallback.
All original fields are emitted through the computed native route table. -/

namespace Blotto.BinaryTerminalSampleRefinement
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping BinaryTerminalGroupInputs BinaryTerminalPromises

theorem sample_value {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin n) :
    value ((BinaryTerminalSampler.sample input hC hAd K N outer scalar bits).read j) =
      (source.program K outer scalar).sample N bits j := by
  rw [source.program_refines]
  unfold BinaryTerminalSampler.sample RationalTerminalLotto.programReference
  dsimp only
  have hRoutes := BinaryTerminalRoutes.prepare_refines input source hC hr
  have hCanon := BinaryTerminalRoutes.prepare_canonical input hC
  have hPivot := pivot_refines input source hC hr
  split
  · rename_i hp
    have hs : source.pivot=none := hPivot.symm.trans hp
    split
    · rename_i hsNone
      rw [RationalAllocationProgram.widen_sample,RationalAllocationProgram.mapped_sample]
      rw [PreparedGroupOutput.emit_allocation]
      rw [BinaryGroupRoutes.emit_refines _ _ _ hCanon (BinaryGroupSamplers.uniformSample_canonical _ _ _ _ K N scalar bits) hRoutes]
      rw [BinaryTerminalRoutes.sourcePartition,BinaryTerminalRoutes.transport_emit]
      apply congrArg (fun y => (source.partition.emit source.partition.routes y).allocation j)
      funext g
      exact BinaryGroupSamplerTransport.uniform_value (congrArg List.length (groups_refines input source hC hr)).symm
        (BinaryTerminalGroupInputs.uniform input) (source.uniformSpec (source.pivot_none hs)) (uniform_canonical input hC)
        (uniform_refines input source hC hr hs) (uniformAdmissible input hC hAd hp) source.groups_count (groupCount input hC hAd) K N scalar bits _
    · rename_i pivot bad
      rw [hs] at bad
      cases bad
  · rename_i selected hp
    have hs : source.pivot=some selected := hPivot.symm.trans hp
    split
    · rename_i bad
      rw [hs] at bad
      cases bad
    · rename_i pivot hSource
      have he : pivot=selected := Option.some.inj (hSource.symm.trans hs)
      subst pivot
      rw [RationalAllocationProgram.mapped_sample,PreparedGroupOutput.emitMixed_allocation]
      rw [BinaryGroupRoutes.emitMixed_refines _ selected _ _ hCanon (BinaryGroupSamplers.mixedSample_canonical _ _ _ _ K N outer scalar bits) hRoutes]
      rw [BinaryTerminalRoutes.sourcePartition,BinaryTerminalRoutes.transport_emitMixed]
      apply congrArg (fun y => (source.partition.emitMixed source.partition.routes selected y).allocation j)
      funext g
      exact BinaryGroupSamplerTransport.mixed_value (congrArg List.length (groups_refines input source hC hr)).symm
        (mixed input selected) (source.mixedSpec selected (source.pivot_some hs)) (mixed_canonical input hC selected)
        (mixed_refines input source hC hr selected hs) (mixedAdmissible input hC hAd selected hp) source.groups_count (groupCount input hC hAd) K N outer scalar bits _

end Blotto.BinaryTerminalSampleRefinement

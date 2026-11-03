import Blotto.BinaryTerminalSampler

/-! The computed terminal sampler preserves its original hard budget on every
bit path, including each small coupling's exact lower-leaf fallback. Source
validity supplies erased group promises; the runtime computes its partition. -/

namespace Blotto.BinaryTerminalBudget
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping BinaryTerminalGroupInputs BinaryTerminalPromises

noncomputable def uniformSource {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (hp : source.pivot=none) :
    RationalUniformGroupSpec (groups input).length :=
  transportUniform (congrArg List.length (groups_refines input source hC hr)).symm (source.uniformSpec (source.pivot_none hp))

noncomputable def mixedSource {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (pivot : Fin n) (hp : source.pivot=some pivot) :
    RationalMixedGroupSpec (groups input).length :=
  transportMixed (congrArg List.length (groups_refines input source hC hr)).symm (source.mixedSpec pivot (source.pivot_some hp))

theorem transportUniform_budget {m k : ℕ} (he : m=k) (source : RationalUniformGroupSpec m) :
    (transportUniform he source).B=source.B := by cases he; rfl

theorem transportMixed_budget {m k : ℕ} (he : m=k) (source : RationalMixedGroupSpec m) :
    (transportMixed he source).B=source.B := by cases he; rfl

theorem sample_fullBudget {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((BinaryTerminalSampler.sample input hC hAd K N outer scalar bits).read j) : ℝ)) := by
  unfold BinaryTerminalSampler.sample
  dsimp only
  split
  · rename_i hp
    have hs : source.pivot=none := (pivot_refines input source hC hr).symm.trans hp
    have hRef : (BinaryTerminalGroupInputs.uniform input).Refines (uniformSource input source hC hr hs) :=
      uniform_transport_refines _ _ _ (uniform_refines input source hC hr hs)
    have hb := BinaryGroupSamplers.uniformSample_fullBudget (BinaryTerminalGroupInputs.uniform input) (uniformSource input source hC hr hs)
      (uniform_canonical input hC) hRef (uniformAdmissible input hC hAd hp) (groupCount input hC hAd) K N scalar bits
    have hB : (uniformSource input source hC hr hs).B=source.B := transportUniform_budget _ _
    rw [hB] at hb
    exact BinaryGroupRoutes.emit_fullBudget _ _ (BinaryTerminalRoutes.sourcePartition input source hC hr)
      (BinaryTerminalRoutes.prepare_canonical input hC) (BinaryGroupSamplers.uniformSample_canonical _ _ _ _ K N scalar bits)
      (BinaryTerminalRoutes.prepare_refines input source hC hr) source.B hb
  · rename_i pivot hp
    have hs : source.pivot=some pivot := (pivot_refines input source hC hr).symm.trans hp
    have hRef : (mixed input pivot).Refines (mixedSource input source hC hr pivot hs) :=
      mixed_transport_refines _ _ _ (mixed_refines input source hC hr pivot hs)
    have hb := BinaryGroupSamplers.mixedSample_fullBudget (mixed input pivot) (mixedSource input source hC hr pivot hs)
      (mixed_canonical input hC pivot) hRef (mixedAdmissible input hC hAd pivot hp) (groupCount input hC hAd) K N outer scalar bits
    have hB : (mixedSource input source hC hr pivot hs).B=source.B := transportMixed_budget _ _
    rw [hB] at hb
    exact BinaryGroupRoutes.emitMixed_fullBudget _ pivot _ (BinaryTerminalRoutes.sourcePartition input source hC hr)
      (BinaryTerminalRoutes.prepare_canonical input hC) (BinaryGroupSamplers.mixedSample_canonical _ _ _ _ K N outer scalar bits)
      (BinaryTerminalRoutes.prepare_refines input source hC hr) source.B hb

end Blotto.BinaryTerminalBudget

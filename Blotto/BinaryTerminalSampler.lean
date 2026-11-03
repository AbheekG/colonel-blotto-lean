import Blotto.BinaryTerminalPromises
import Blotto.BinaryTerminalRoutes

/-! Native terminal coupling builds its actual grouped input, samples one whole
small-group allocation and emits original fields through cached proportional
routes. The actual pivot word is added only on its original field. This terminal
output API has its own caller cap; global serial none/position composition remains
separate until an indexed partial-run interface is joined. -/

namespace Blotto.BinaryTerminalSampler
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping BinaryTerminalGroupInputs BinaryTerminalPromises

def sample {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable n SignedWord :=
  let routes := BinaryTerminalRoutes.prepare input
  match hp : pivot input with
  | none =>
      let row := BinaryGroupSamplers.uniformSample (uniform input) (uniform_canonical input hC)
        (uniformAdmissible input hC hAd hp) (groupCount input hC hAd) K N scalar bits
      BinaryGroupRoutes.emit routes row
  | some selected =>
      let row := BinaryGroupSamplers.mixedSample (mixed input selected) (mixed_canonical input hC selected)
        (mixedAdmissible input hC hAd selected hp) (groupCount input hC hAd) K N outer scalar bits
      BinaryGroupRoutes.emitMixed routes selected row

theorem sample_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : ∀ j, CanonicalWord ((sample input hC hAd K N outer scalar bits).read j) := by
  unfold sample
  dsimp only
  split
  · exact BinaryGroupRoutes.emit_canonical _ _ (BinaryTerminalRoutes.prepare_canonical input hC)
      (BinaryGroupSamplers.uniformSample_canonical _ _ _ _ K N scalar bits)
  · exact BinaryGroupRoutes.emitMixed_canonical _ _ _ (BinaryTerminalRoutes.prepare_canonical input hC)
      (BinaryGroupSamplers.mixedSample_canonical _ _ _ _ K N outer scalar bits)

end Blotto.BinaryTerminalSampler

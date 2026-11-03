import Blotto.BinaryTerminalPromises

/-! Erased group-size transports retain exact small-group programs and every
stored coordinate value. These proof joins do not construct runtime semantic
source inputs or change any branch/fallback. -/

namespace Blotto.BinaryGroupSamplerTransport
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs BinaryGroupSamplers
open BinaryTerminalGroupInputs BinaryTerminalPromises

theorem uniform_value {m k : ℕ} (he : m=k) (input : UniformInput k) (source : RationalUniformGroupSpec m)
    (hC : input.Canonical) (hr : (castUniform he.symm input).Refines source) (hAd : UniformAdmissible input)
    (hm : m=2 ∨ m=3) (hk : k=2 ∨ k=3) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (g : Fin k) :
    value ((uniformSample input hC hAd hk K N scalar bits).read g) =
      (source.program hm K scalar).sample N bits (g.cast he.symm) := by
  cases he
  exact uniformSample_value input source hC hr hAd hm K N scalar bits g

theorem mixed_value {m k : ℕ} (he : m=k) (input : MixedInput k) (source : RationalMixedGroupSpec m)
    (hC : input.Canonical) (hr : (castMixed he.symm input).Refines source) (hAd : MixedAdmissible input)
    (hm : m=2 ∨ m=3) (hk : k=2 ∨ k=3) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (g : Fin (k+1)) :
    value ((mixedSample input hC hAd hk K N outer scalar bits).read g) =
      (source.program hm K outer scalar).sample N bits (g.cast (congrArg (fun v => v+1) he).symm) := by
  cases he
  exact mixedSample_value input source hC hr hAd hm K N outer scalar bits g

end Blotto.BinaryGroupSamplerTransport

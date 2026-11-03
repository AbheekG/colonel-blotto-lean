import Blotto.BinaryTerminalGroupInputs
import Blotto.BinaryGroupSamplers

/-! Native computed groups receive their two/three-group promises and actual
small-input validity from a terminal witness inside Prop only. Runtime factories
and semantic source descriptors are absent. -/

namespace Blotto.BinaryTerminalPromises
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping BinaryTerminalGroupInputs

def Admissible {n : ℕ} (input : Input n) : Prop := ∃ source : RationalTerminalLotto n, input.Refines source

theorem groupCount {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input) :
    (groups input).length=2 ∨ (groups input).length=3 := by
  obtain ⟨source,hr⟩ := hAd
  exact groups_count input source hC hr

def transportUniform {m k : ℕ} (he : m=k) (source : RationalUniformGroupSpec m) : RationalUniformGroupSpec k := he ▸ source

def transportMixed {m k : ℕ} (he : m=k) (source : RationalMixedGroupSpec m) : RationalMixedGroupSpec k := he ▸ source

theorem uniform_transport_refines {m k : ℕ} (he : m=k) (input : BinaryGroupInputs.UniformInput k)
    (source : RationalUniformGroupSpec m) (hr : (castUniform he.symm input).Refines source) :
    input.Refines (transportUniform he source) := by cases he; exact hr

theorem mixed_transport_refines {m k : ℕ} (he : m=k) (input : BinaryGroupInputs.MixedInput k)
    (source : RationalMixedGroupSpec m) (hr : (castMixed he.symm input).Refines source) :
    input.Refines (transportMixed he source) := by cases he; exact hr

theorem uniformAdmissible {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input) (hNone : pivot input=none) :
    BinaryGroupSamplers.UniformAdmissible (uniform input) := by
  obtain ⟨source,hr⟩ := hAd
  have hs : source.pivot=none := (pivot_refines input source hC hr).symm.trans hNone
  let equality := congrArg List.length (groups_refines input source hC hr)
  exact ⟨transportUniform equality.symm (source.uniformSpec (source.pivot_none hs)),
    uniform_transport_refines equality.symm _ _ (uniform_refines input source hC hr hs)⟩

theorem mixedAdmissible {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (selected : Fin n) (hPivot : pivot input=some selected) :
    BinaryGroupSamplers.MixedAdmissible (mixed input selected) := by
  obtain ⟨source,hr⟩ := hAd
  have hs : source.pivot=some selected := (pivot_refines input source hC hr).symm.trans hPivot
  let equality := congrArg List.length (groups_refines input source hC hr)
  exact ⟨transportMixed equality.symm (source.mixedSpec selected (source.pivot_some hs)),
    mixed_transport_refines equality.symm _ _ (mixed_refines input source hC hr selected hs)⟩

end Blotto.BinaryTerminalPromises

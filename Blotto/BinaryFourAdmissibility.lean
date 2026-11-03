import Blotto.BinaryFourParentCompiler
import Blotto.BinaryReflectedSerialRun

/-! The deterministic stored-word four-case guard transfers valid input
certificates into the selected branch in Prop. Numerical recognition and its
complete price remain separate; no semantic source is a runtime argument. -/

namespace Blotto.BinaryFourAdmissibility
open BinaryRationalNormalization BinaryRationalEncoding

def Admissible (input : BinaryFourParameters.Input) : Prop := ∃ source : RationalFourInput, input.Refines source

def Gluing (input : BinaryFourParameters.Input) : Prop :=
  ∃ source : RationalFourInput, input.Refines source ∧ (1-source.p)*source.ell ≤ source.w

theorem gluing_guard (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (hGuard : BinaryFourParentCompiler.gluingCase input=true) : Gluing input := by
  obtain ⟨source,hr⟩ := hAd
  exact ⟨source,hr,(BinaryFourParentCompiler.gluingCase_iff input source hC hr).mp hGuard⟩

theorem small_guard (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase input=true) : BinaryReflectedSerialRun.Admissible input := by
  obtain ⟨source,hr⟩ := hAd
  exact ⟨source,hr,lt_of_not_ge (fun he => hGuard ((BinaryFourParentCompiler.gluingCase_iff input source hC hr).mpr he))⟩

end Blotto.BinaryFourAdmissibility

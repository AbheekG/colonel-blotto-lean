import Blotto.RationalAllocationProgram
import Blotto.WordMappedIndexedRefinement
import Blotto.WordMachineLowerLeaf

/-! Mapping an allocation program commutes exactly with its selected output
and syntactic fallback, including exhausted bit paths. -/

namespace Blotto.RationalAllocationProgram

theorem mapped_sample {n m C : ℕ} (program : RationalAllocationProgram n C)
    (f : (Fin n → ℚ) → (Fin m → ℚ)) (N : ℕ) (bits : Fin N → Bool) :
    (program.mapped f).sample N bits = f (program.sample N bits) := by
  unfold sample mapped WordStateMachine.output fallback
  rw [WordMappedIndexedRefinement.run_refines,WordStateMachine.mapped_chooseLeaf]
  unfold WordMappedIndexedRefinement.mapResult
  cases hs : (program.machine.run N program.start bits).1 <;> rfl

theorem widen_sample {n C D : ℕ} (program : RationalAllocationProgram n C) (he : C≤D) (N : ℕ) (bits : Fin N → Bool) :
    (program.widen he).sample N bits = program.sample N bits := rfl

end Blotto.RationalAllocationProgram

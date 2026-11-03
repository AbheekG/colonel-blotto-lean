import Blotto.RationalStoredAllocationProgram
import Blotto.RationalTerminalProgram

/-! Terminal group controllers emit an actual resource array as their leaf,
instead of delaying full-array emission inside a coordinate function. -/

namespace Blotto.RationalTerminalLotto

def storedProgram {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : RationalStoredAllocationProgram n 80 :=
  let packed := RationalTerminalPacking.prepare i
  let output := packed.prepareOutput
  match h : i.pivot with
  | none =>
    (RationalStoredAllocationProgram.ofProgram
      ((packed.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits)
      output.emit).widen (by decide)
  | some pivot =>
    RationalStoredAllocationProgram.ofProgram
      ((packed.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits)
      (output.emitMixed pivot)

theorem storedProgram_reference {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    (i.storedProgram K outerBits scalarBits).reference = i.program K outerBits scalarBits := by
  unfold storedProgram program
  dsimp only
  split
  · rename_i h
    rw [RationalStoredAllocationProgram.reference_widen,
      RationalStoredAllocationProgram.reference_from]
    split
    · rfl
    · rename_i pivot hOther
      cases h.symm.trans hOther
  · rename_i pivot h
    rw [RationalStoredAllocationProgram.reference_from]
    split
    · rename_i hOther
      cases h.symm.trans hOther
    · rename_i other hOther
      have he : pivot = other := Option.some.inj (h.symm.trans hOther)
      subst other
      rfl

end Blotto.RationalTerminalLotto

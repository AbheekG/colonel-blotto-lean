import Blotto.GeneralPaperEqualSegmentCallerCapacity

/-! Local unsigned primitive storage: actual operand/result words, primitive
scratch and control/price fields. The scalar price bounds word lengths, not
the magnitudes of the represented integers. -/
namespace Blotto.GeneralPaperNaturalScalarLifetime
open GeneralPaperNaturalScalarStep (run word)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem counter_word (x : ℕ) : natBits x ≤ x + 2 := by
  have h := Nat.log2_le_self x
  change 1 + (x.log2 + 1) ≤ x + 2
  omega

theorem words (model : RationalCostModel) (A : ℕ) (op : GeneralPaperNaturalScalarStep.Op) (a b : ℕ) :
    word a + word b + word (run model A op a b).1 + 16 * A + 16 ≤ (run model A op a b).2 := by
  unfold run
  dsimp only
  omega

def footprint (model : RationalCostModel) (A : ℕ) (op : GeneralPaperNaturalScalarStep.Op) (a b : ℕ) : ℕ :=
  let actual := run model A op a b
  word a + word b + word actual.1 + actual.2 + fields A [actual.2, 16 * A, 16] + 64 * A

theorem bounded (model : RationalCostModel) (A : ℕ) (op : GeneralPaperNaturalScalarStep.Op) (a b : ℕ) :
    footprint model A op a b ≤ 32 * (run model A op a b).2 := by
  have hWords := words model A op a b
  let F := (run model A op a b).2
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A F [F, 16 * A, 16] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  change fields A [F, 16 * A, 16] ≤ 3 * (natBits F + A) + 32 * A at hFields
  have hBits : natBits F ≤ F + 2 := by
    have h := Nat.log2_le_self F
    change 1 + (F.log2 + 1) ≤ F + 2
    omega
  change word a + word b + word (run model A op a b).1 + F + fields A [F, 16 * A, 16] + 64 * A ≤ 32 * F
  omega

theorem written (model : RationalCostModel) (A : ℕ) (op : GeneralPaperNaturalScalarStep.Op) (a b : ℕ) :
    natBits (run model A op a b).1 ≤ (run model A op a b).2 := by
  have h := words model A op a b
  change word (run model A op a b).1 ≤ _
  omega

end Blotto.GeneralPaperNaturalScalarLifetime

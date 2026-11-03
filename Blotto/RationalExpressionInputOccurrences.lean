import Blotto.RationalReflectionOutputCost
import Blotto.RationalFourPermutationCost

/-! Input occurrence counts expose uncached function-reader multiplicities.
Both branches of an arithmetic conditional are retained conservatively. Dense
reflection/permutation rows contain one occurrence of every input coordinate. -/

namespace Blotto.RationalExpression

def inputOccurrences {k : ℕ} : RationalExpression k → Fin k → ℕ
  | .input j, r => if r = j then 1 else 0
  | .literal _, _ => 0
  | .add a b, r | .sub a b, r | .mul a b, r | .div a b, r | .minimum a b, r | .maximum a b, r =>
    a.inputOccurrences r + b.inputOccurrences r
  | .ifLe a b yes no, r => a.inputOccurrences r + b.inputOccurrences r + yes.inputOccurrences r + no.inputOccurrences r

end Blotto.RationalExpression
namespace Blotto.RationalReflectionCode
open scoped BigOperators

theorem row_inputOccurrences (j : Fin 4) (k : Fin 3) : (row j).inputOccurrences k.castSucc = 1 := by
  fin_cases j <;> fin_cases k <;> decide

theorem output_inputOccurrences (k : Fin 3) : (∑ j : Fin 4, (row j).inputOccurrences k.castSucc) = 4 := by
  simp [row_inputOccurrences]

end Blotto.RationalReflectionCode
namespace Blotto.RationalFourPermutationCode
open scoped BigOperators

theorem row_inputOccurrences (k j : Fin 4) : (row k).inputOccurrences j = 1 := by
  fin_cases k <;> fin_cases j <;> decide

theorem output_inputOccurrences (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    (∑ j : Fin 4, (row (π j)).inputOccurrences k) = 4 := by
  simp [row_inputOccurrences]

end Blotto.RationalFourPermutationCode

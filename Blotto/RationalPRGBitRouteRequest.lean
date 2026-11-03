import Blotto.RationalPRGBitRouteSampler
import Blotto.RationalPRGRequestSuccess

/-! The integrated bit-route sampler has the same portable binary request
interface. Exact output equality preserves parsing, failure branches and
returned-budget guarantees. Computational-model cost composition is separate. -/

namespace Blotto.RationalPRGBinaryRequest

def runBitRoutes (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (readWords request).bind (fun parsed => if parsed.2.2 = [] then
    let K := parsed.2.1.precision
    (seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed).map (fun table =>
      BinaryRatListFrame.encodeRow (if rich then parsed.1.2.richBitRouteSample K table.read else
        parsed.1.2.poorBitRouteSample K table.read)) else none)

theorem runBitRoutes_eq (rich : Bool) (request seed : List Bool) : runBitRoutes rich request seed = run rich request seed := by
  unfold runBitRoutes run
  congr 1
  funext parsed
  split
  · dsimp only
    congr 1
    funext table
    cases rich with
    | false => simp only [Bool.false_eq_true, ite_false, RationalPRGOriginalInput.poorBitRouteSample_eq,
        RationalPRGOriginalInput.poorOutputBits]
    | true => simp only [ite_true, RationalPRGOriginalInput.richBitRouteSample_eq,
        RationalPRGOriginalInput.richOutputBits]
  · rfl

theorem runBitRoutes_failure_iff (rich : Bool) (request seed : List Bool) :
    runBitRoutes rich request seed = none ↔ run rich request seed = none := by rw [runBitRoutes_eq]

end Blotto.RationalPRGBinaryRequest

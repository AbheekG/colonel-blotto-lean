import Blotto.RationalPRGArrayRouteSampler
import Blotto.RationalPRGRequestSuccess

/-! The streamed array sampler retains the portable binary request interface.
Complete output equality preserves acceptance, rejection and returned allocations.
Time/space composition and primitive realization remain separate. -/

namespace Blotto.RationalPRGBinaryRequest

def runArrayRoutes (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (readWords request).bind (fun parsed => if parsed.2.2 = [] then
    let K := parsed.2.1.precision
    (seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed).map (fun table =>
      BinaryRatListFrame.encodeRow (if rich then parsed.1.2.richArrayRouteSample K table.read else
        parsed.1.2.poorArrayRouteSample K table.read)) else none)

theorem runArrayRoutes_eq (rich : Bool) (request seed : List Bool) : runArrayRoutes rich request seed = run rich request seed := by
  unfold runArrayRoutes run
  congr 1
  funext parsed
  split
  · dsimp only
    congr 1
    funext table
    cases rich with
    | false => simp only [Bool.false_eq_true, ite_false, RationalPRGOriginalInput.poorArrayRouteSample_eq,
        RationalPRGOriginalInput.poorOutputBits]
    | true => simp only [ite_true, RationalPRGOriginalInput.richArrayRouteSample_eq,
        RationalPRGOriginalInput.richOutputBits]
  · rfl

theorem runArrayRoutes_failure_iff (rich : Bool) (request seed : List Bool) :
    runArrayRoutes rich request seed = none ↔ run rich request seed = none := by rw [runArrayRoutes_eq]

end Blotto.RationalPRGBinaryRequest

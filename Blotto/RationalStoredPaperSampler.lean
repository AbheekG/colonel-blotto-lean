import Blotto.RationalStoredSharedRun
import Blotto.RationalLottoPaperProgram

/-! Whole-array fixed and paper samplers retain the original fair-bit split,
global cap, exact consumed cursor and direct exhaustion fallback. -/

namespace Blotto.RationalLottoResourceSystem

def storedFixedRun {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    Option (RationalResourceArray n) × ℕ :=
  i.runStoredWithTerminalIndexed
    (fun value => (i.terminalData value).storedProgram K outer scalar)
    R choice (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem storedFixedRun_projection {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    WordMappedIndexedRefinement.mapResult RationalResourceArray.allocation
      (i.storedFixedRun K R outer scalar choice) = i.runShared K R outer scalar choice := by
  unfold storedFixedRun runShared
  exact (i.runStoredWithTerminalIndexed_projection _ R choice (.ready i.initialState)
    i.initial_invariant 0 (Nat.zero_le R)).trans
    (i.runSharedWithTerminalIndexed_eq _ K outer scalar
      (fun value => (i.terminalData value).storedProgram_reference K outer scalar)
      R choice (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R))

theorem storedFixedRun_position {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (i.storedFixedRun K R outer scalar choice).2 = (i.runShared K R outer scalar choice).2 :=
  congrArg Prod.snd (i.storedFixedRun_projection K R outer scalar choice)

theorem storedFixedRun_failure {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (i.storedFixedRun K R outer scalar choice).1 = none ↔
      (i.runShared K R outer scalar choice).1 = none := by
  have h := congrArg Prod.fst (i.storedFixedRun_projection K R outer scalar choice)
  change Option.map RationalResourceArray.allocation _ = _ at h
  rw [← h, Option.map_eq_none_iff]

def storedFixedSample {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outer scalar : Fin K → Bool) (choice : Fin R → Bool) : RationalResourceArray n :=
  match (i.storedFixedRun K R outer scalar choice).1 with
  | none => RationalResourceArray.ofAllocation i.fallbackAllocation
  | some row => row

theorem storedFixedSample_allocation {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (i.storedFixedSample K R outer scalar choice).allocation =
      i.paperFixedSample K R outer scalar choice := by
  have h := congrArg Prod.fst (i.storedFixedRun_projection K R outer scalar choice)
  change Option.map RationalResourceArray.allocation _ = _ at h
  unfold storedFixedSample paperFixedSample sharedFixedSample
  rw [← h]
  cases (i.storedFixedRun K R outer scalar choice).1 <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
      RationalResourceArray.allocation_ofAllocation]

def storedPaperSample {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : RationalResourceArray n :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.storedFixedSample K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem storedPaperSample_allocation {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) :
    (i.storedPaperSample K bits).allocation = i.paperSample K bits := by
  unfold storedPaperSample
  rw [i.storedFixedSample_allocation]
  rfl

theorem storedPaperSample_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) :
    FullBudget (i.B : ℝ) (i.storedPaperSample K bits).realAllocation := by
  change FullBudget (i.B : ℝ) (fun j => ((i.storedPaperSample K bits).allocation j : ℝ))
  rw [i.storedPaperSample_allocation]
  exact i.paperSample_fullBudget K bits

end Blotto.RationalLottoResourceSystem

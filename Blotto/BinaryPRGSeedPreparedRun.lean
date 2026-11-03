import Blotto.BinaryPRGSeedRequestBound

/-! The full raw runner retains the existing priced request, prepares exact
choice/scalar/outer seed arrays once, then uses the direct block output entry.
Every original output/ledger/rejection/readback/hard-budget scope remains.
Incoming frame length derives recorded input plus seed cell preparation work;
scalar/controller/backend/physical/full execution/space scopes are separate. -/

namespace Blotto.BinaryPRGSeedPreparedRun

structure Ledger where
  input : BinaryPRGAccuracyRulerRequest.Ledger
  seed : BinaryPRGSeedBlocks.Ledger
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.input.recorded + ledger.seed.recorded

def run (rich : Bool) (request seed : List Bool) : Option (List Bool × BinaryPRGOutputRun.Ledger) × Ledger :=
  let decoded := BinaryPRGAccuracyRulerRequest.read request
  match decoded.1 with
  | none => (none,⟨decoded.2,⟨0,0,0⟩⟩)
  | some parsed =>
      if parsed.2 = [] then
        let blocks := BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed
        (blocks.1.map (BinaryPRGSeedBlockOutput.output parsed.1.2 rich),⟨decoded.2,blocks.2⟩)
      else (none,⟨decoded.2,⟨0,0,0⟩⟩)

theorem run_state (rich : Bool) (request seed : List Bool) : (run rich request seed).1 = BinaryPRGOutputRun.run rich request seed := by
  have hs : (run rich request seed).1 = (BinaryPRGAccuracyRulerRequest.run rich request seed).1 := by
    unfold run BinaryPRGAccuracyRulerRequest.run
    dsimp only
    cases hd : (BinaryPRGAccuracyRulerRequest.read request).1 with
    | none => rfl
    | some parsed =>
        simp only [Option.bind_some]
        split
        · exact BinaryPRGSeedBlockOutput.output_map_state (n := parsed.1.1) parsed.1.2 rich seed
        · rfl
  exact hs.trans (BinaryPRGAccuracyRulerRequest.run_state rich request seed)

theorem run_input_ledger (rich : Bool) (request seed : List Bool) : (run rich request seed).2.input = (BinaryPRGAccuracyRulerRequest.read request).2 := by
  unfold run
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem run_seed_bound (rich : Bool) (request seed : List Bool) : (run rich request seed).2.seed.recorded ≤
    BinaryPRGSeedRequestBound.preparationBound request.length := by
  unfold run
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hd
    split
    · exact BinaryPRGSeedRequestBound.read_seed_preparation_bound request seed parsed hd
    · exact Nat.zero_le _

def bound (length : ℕ) : ℕ := BinaryPRGAccuracyRulerRequest.inputBound length + BinaryPRGSeedRequestBound.preparationBound length

theorem run_bound (rich : Bool) (request seed : List Bool) : (run rich request seed).2.recorded ≤ bound request.length := by
  have hi := BinaryPRGAccuracyRulerRequest.read_input_bound request
  rw [← run_input_ledger rich request seed] at hi
  exact Nat.add_le_add hi (run_seed_bound rich request seed)

def polynomialBound (length : ℕ) : ℕ := 8623936008 * (length + 1) ^ 4

theorem bound_polynomial (length : ℕ) : bound length ≤ polynomialBound length := by
  have hp := Nat.pow_le_pow_right (by omega : 0 < length + 1) (by decide : 2 ≤ 4)
  have hs := BinaryPRGSeedRequestBound.preparationBound_square length
  have hScale : (8 * length + 3030) ^ 2 ≤ 9180900 * (length + 1) ^ 4 := by
    calc
      _ ≤ (3030 * (length + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 9180900 * (length + 1) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left 9180900 hp
  unfold bound polynomialBound
  calc
    _ ≤ BinaryPRGAccuracyRulerRequest.polynomialBound length + 9180900 * (length + 1) ^ 4 :=
      Nat.add_le_add (BinaryPRGAccuracyRulerRequest.inputBound_polynomial length) (hs.trans hScale)
    _ = _ := by unfold BinaryPRGAccuracyRulerRequest.polynomialBound; ring

theorem run_polynomial (rich : Bool) (request seed : List Bool) : (run rich request seed).2.recorded ≤ polynomialBound request.length :=
  (run_bound rich request seed).trans (bound_polynomial request.length)

theorem run_returned_budget (rich : Bool) (request seed : List Bool) (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (run rich request seed).1 = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords request = some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1 (if rich then parsed.2.source.a else parsed.2.source.b) returned.1 := by
  rw [run_state] at h
  exact BinaryPRGOutputRun.run_returned_budget rich request seed returned h

theorem run_output_recorded_bound (rich : Bool) (request seed : List Bool) (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (run rich request seed).1 = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      BinaryPRGRequest.read request = some (parsed,[]) ∧ returned.2.recorded ≤ BinaryPRGOutputRun.bound parsed.2 := by
  rw [run_state] at h
  exact BinaryPRGOutputRun.run_recorded_bound rich request seed returned h

end Blotto.BinaryPRGSeedPreparedRun

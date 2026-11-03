import Blotto.GeneralPaperIntervalOutputValidity

/-! Execute a list of integer half-open range increments on one sparse
tree. The root code span is constructed once and passed to every update.
Exact batch levels and output-cap validity include all partial batches.
-/
namespace Blotto.GeneralPaperIntervalBatch
open GeneralPaperIntervalCache GeneralPaperIntervalUpdate GeneralPaperIntervalLevels GeneralPaperPreparedPowers
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Instruction where
  lo : ℕ
  hi : ℕ
  amount : ℕ

def increment (entry : Instruction) (i : ℕ) : ℕ :=
  if entry.lo≤ i ∧ i<entry.hi then entry.amount else 0

def effect : List Instruction → ℕ → ℕ
  | [],_ => 0
  | entry::rest,i => increment entry i+effect rest i

structure Result (height : ℕ) where
  node : Node height
  work : ℕ
  visits : ℕ

def run (prepared : Prepared) (height : ℕ) (span : ℚ) (node : Node height) : List Instruction → Result height
  | [] => ⟨node,8,0⟩
  | entry::rest =>
    let updated := GeneralPaperIntervalUpdate.run prepared entry.lo entry.hi entry.amount height node 0 span
    let tail := run prepared height span updated.node rest
    ⟨tail.node,updated.work+tail.work+16,updated.visits+tail.visits⟩

theorem effect_append (left right : List Instruction) (i : ℕ) :
    effect (left++right) i=effect left i+effect right i := by
  induction left with
  | nil => simp [effect]
  | cons entry rest ih => simp only [List.cons_append,effect,ih,Nat.add_assoc]

theorem step_levels (prepared : Prepared) (height : ℕ) (span : ℚ) (node : Node height)
    (entry : Instruction) (hSpan : span=(2:ℚ)^height) (i : ℕ) (hI : i<2^height) :
    levelAt (GeneralPaperIntervalUpdate.run prepared entry.lo entry.hi entry.amount height node 0 span).node i=
      levelAt node i+increment entry i := by
  have he := GeneralPaperIntervalLevels.update_level prepared entry.lo entry.hi entry.amount height node 0 i hI
  simpa only [hSpan,Nat.cast_zero,Nat.zero_add,increment] using he

theorem run_levels (prepared : Prepared) (height : ℕ) (span : ℚ) (node : Node height)
    (entries : List Instruction) (hSpan : span=(2:ℚ)^height) (i : ℕ) (hI : i<2^height) :
    levelAt (run prepared height span node entries).node i=levelAt node i+effect entries i := by
  induction entries generalizing node with
  | nil => simp only [run,effect,Nat.add_zero]
  | cons entry rest ih =>
    dsimp only [run]
    rw [ih]
    rw [step_levels prepared height span node entry hSpan i hI]
    simp only [effect,Nat.add_assoc]

theorem run_valid (lambda k height : ℕ) (span : ℚ) (node : Node height) (entries : List Instruction)
    (hSpan : span=(2:ℚ)^height) (hValid : Valid lambda k node)
    (hFinal : ∀ i<2^height, levelAt node i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    Valid lambda k (run (prepare lambda k) height span node entries).node := by
  induction entries generalizing node with
  | nil => exact hValid
  | cons entry rest ih =>
    have hStep : ∀ i<2^height,
        levelAt (GeneralPaperIntervalUpdate.run (prepare lambda k) entry.lo entry.hi entry.amount height node 0 span).node i≤
          GeneralPaperPowerPrecision.levelBound lambda k := by
      intro i hi
      have hc := hFinal i hi
      rw [step_levels _ height span node entry hSpan i hi]
      dsimp only [effect] at hc
      omega
    have hUpdated := GeneralPaperIntervalOutputValidity.run_valid_of_output lambda k entry.lo entry.hi entry.amount
      height node 0 span hValid hStep
    dsimp only [run]
    apply ih _ hUpdated
    intro i hi
    have hc := hFinal i hi
    rw [step_levels _ height span node entry hSpan i hi]
    dsimp only [effect] at hc
    omega

end Blotto.GeneralPaperIntervalBatch

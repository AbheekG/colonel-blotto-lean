import Blotto.PairStoreMemory
import Blotto.RationalHeightBudget
import Blotto.RationalExpressionWordWidth

/-! Every prefix of the actual pair-store program has bounded rational cells
and registers. Copies preserve height; only its two arithmetic instructions
increase the expression level. No branch or denominator promise is needed. -/

namespace Blotto.PairStoreState

def HeightAt {n : ℕ} (s : PairStoreState n ℚ) (height : ℕ) : Prop :=
  (∀ i, RationalHeight (s.cells.read i) height) ∧ ∀ r, RationalHeight (s.registers.read r) height

theorem HeightAt.mono {n a b : ℕ} {s : PairStoreState n ℚ} (h : s.HeightAt a) (hab : a ≤ b) :
    s.HeightAt b := ⟨fun i => (h.1 i).mono hab, fun r => (h.2 r).mono hab⟩

end Blotto.PairStoreState
namespace Blotto.PairStoreInstruction

theorem execute_height {n : ℕ} (instruction : PairStoreInstruction n) (state : PairStoreState n ℚ)
    (s level : ℕ) (h : state.HeightAt (expressionHeightBudget s level)) :
    (instruction.execute state).HeightAt (expressionHeightBudget s (level + instruction.arithmeticCalls)) := by
  cases instruction with
  | load cell destination =>
    simp only [execute, arithmeticCalls, Nat.add_zero, PairStoreState.HeightAt]
    refine ⟨h.1, ?_⟩
    intro r
    rw [PairStoreBuffer.read_write]
    split
    · exact h.1 cell
    · exact h.2 r
  | store cell source =>
    simp only [execute, arithmeticCalls, Nat.add_zero, PairStoreState.HeightAt]
    refine ⟨?_, h.2⟩
    intro r
    rw [PairStoreBuffer.read_write]
    split
    · exact h.2 source
    · exact h.1 r
  | add destination left right =>
    have hm := expressionHeightBudget_mono s (by omega : level ≤ level + 1)
    simp only [execute, arithmeticCalls, PairStoreState.HeightAt]
    refine ⟨fun i => (h.1 i).mono hm, ?_⟩
    intro r
    rw [PairStoreBuffer.read_write]
    split
    · exact (h.2 left).add_level (h.2 right)
    · exact (h.2 r).mono hm
  | sub destination left right =>
    have hm := expressionHeightBudget_mono s (by omega : level ≤ level + 1)
    simp only [execute, arithmeticCalls, PairStoreState.HeightAt]
    refine ⟨fun i => (h.1 i).mono hm, ?_⟩
    intro r
    rw [PairStoreBuffer.read_write]
    split
    · exact (h.2 left).sub_level (h.2 right)
    · exact (h.2 r).mono hm

end Blotto.PairStoreInstruction
namespace Blotto.PairStoreProgram

theorem run_height {n : ℕ} (program : List (PairStoreInstruction n)) (state : PairStoreState n ℚ)
    (s level : ℕ) (h : state.HeightAt (expressionHeightBudget s level)) :
    (run program state).HeightAt
      (expressionHeightBudget s (level + (program.map PairStoreInstruction.arithmeticCalls).sum)) := by
  induction program generalizing state level with
  | nil => simpa only [run, List.map_nil, List.sum_nil, Nat.add_zero] using h
  | cons instruction rest ih =>
    have hn := instruction.execute_height state s level h
    have hr := ih (instruction.execute state) (level + instruction.arithmeticCalls) hn
    simpa only [run, List.map_cons, List.sum_cons, Nat.add_assoc] using hr

theorem arithmeticCalls_prefix {n : ℕ} (i j : Fin n) (k : ℕ) :
    (((code i j).take k).map PairStoreInstruction.arithmeticCalls).sum ≤ 2 := by
  by_cases hk : k ≤ 6
  · interval_cases k <;> simp [code, PairStoreInstruction.arithmeticCalls]
  · have hlen : (code i j).length ≤ k := by simp only [code, List.length_cons, List.length_nil]; omega
    rw [List.take_of_length_le hlen, arithmeticCalls]

theorem initial_height {n : ℕ} (cells : PairStoreBuffer n ℚ) (z : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCells : ∀ i, RationalHeight (cells.read i) s) (hZ : RationalHeight z s) :
    (initial cells z).HeightAt s := by
  refine ⟨hCells, ?_⟩
  intro r
  have hZero : RationalHeight (0 : ℚ) s :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  fin_cases r
  · simpa [initial, PairStoreBuffer.read_ofFn] using hZ
  all_goals simpa [initial, PairStoreBuffer.read_ofFn] using hZero

theorem prefixes_height {n : ℕ} (cells : PairStoreBuffer n ℚ) (i j : Fin n) (z : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hCells : ∀ r, RationalHeight (cells.read r) s)
    (hZ : RationalHeight z s) (k : ℕ) :
    (run ((code i j).take k) (initial cells z)).HeightAt (expressionHeightBudget s 2) := by
  have h0 : (initial cells z).HeightAt (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using initial_height cells z s hs hCells hZ
  have h := run_height ((code i j).take k) (initial cells z) s 0 h0
  simp only [Nat.zero_add] at h
  exact h.mono (expressionHeightBudget_mono s (arithmeticCalls_prefix i j k))

theorem prefixes_wordWidth {n : ℕ} (cells : PairStoreBuffer n ℚ) (i j : Fin n) (z : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hCells : ∀ r, RationalHeight (cells.read r) s)
    (hZ : RationalHeight z s) (k : ℕ) :
    (∀ r, rationalWordWidth ((run ((code i j).take k) (initial cells z)).cells.read r) ≤ 8 * s + 7) ∧
      ∀ r, rationalWordWidth ((run ((code i j).take k) (initial cells z)).registers.read r) ≤ 8 * s + 7 := by
  have h := prefixes_height cells i j z s hs hCells hZ k
  have hConvert : ∀ q : ℚ, RationalHeight q (expressionHeightBudget s 2) → rationalWordWidth q ≤ 8 * s + 7 := by
    intro q hq
    have hw := rationalWordWidth_of_height hq
    norm_num [expressionHeightBudget] at hw
    omega
  exact ⟨fun r => hConvert _ (h.1 r), fun r => hConvert _ (h.2 r)⟩

end Blotto.PairStoreProgram

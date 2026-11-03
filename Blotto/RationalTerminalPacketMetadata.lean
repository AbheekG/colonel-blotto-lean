import Blotto.RationalTerminalGroupInputCost
import Blotto.RationalLotteryAssemblyMetadata

/-! Cached group packet metadata retains all written fields, full-prefix
copies and index control. A mixed packet evaluates its pivot ratio using its
own environment. Packing scans and output-route construction remain separate. -/

namespace Blotto.RationalTerminalLotto

def groupPacketFields {n : ℕ} (i : RationalTerminalLotto n) : List ℚ :=
  (i.B :: List.ofFn (fun g : Fin i.groups.length => i.partition.total g)) ++
    match i.pivot with
    | none => []
    | some pivot => [i.length pivot, i.resource pivot / i.length pivot]

theorem groupPacketFields_length {n : ℕ} (i : RationalTerminalLotto n) : i.groupPacketFields.length ≤ 6 := by
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  unfold groupPacketFields
  cases i.pivot <;> simp only [List.length_append, List.length_cons, List.length_ofFn, List.length_nil] <;> omega

theorem OnLattice.groupPacketFields_height {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s) :
    ∀ q ∈ i.groupPacketFields, RationalHeight q (expressionHeightBudget s 1) := by
  intro q hq
  have hm := expressionHeightBudget_ge_input s 1
  unfold groupPacketFields at hq
  cases hp : i.pivot with
  | none =>
    rw [hp] at hq
    simp only [List.append_nil, List.mem_cons, List.mem_ofFn] at hq
    rcases hq with rfl | ⟨g, rfl⟩
    · exact hBudget.mono hm
    · exact (h.total_height hD hB g).mono (hWidth.trans hm)
  | some pivot =>
    rw [hp] at hq
    simp only [List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | ⟨g, rfl⟩) | (rfl | rfl)
    · exact hBudget.mono hm
    · exact (h.total_height hD hB g).mono (hWidth.trans hm)
    · exact (h.length_height hD hB pivot).mono (hWidth.trans hm)
    · have hLength : RationalHeight (i.length pivot) (expressionHeightBudget s 0) := by
        simpa only [expressionHeightBudget_zero] using (h.length_height hD hB pivot).mono hWidth
      have hResource : RationalHeight (i.resource pivot) (expressionHeightBudget s 0) := by
        simpa only [expressionHeightBudget_zero] using (h.resource_height hD hB pivot).mono hWidth
      exact hResource.div_level hLength

def groupRatioMetadataWork {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (c : ℕ) : ℕ :=
  match i.pivot with
  | none => 0
  | some pivot =>
      let env := RationalLotteryAssemblyCode.environment (i.resource pivot) (i.length pivot)
      rationalEnvironmentMetadataWork primitive env + RationalExpression.metadataAllowance c
        (RationalExpression.div (.input 0) (.input 1) : RationalExpression 2) env

def groupPacketMetadataWork {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (c : ℕ) : ℕ :=
  rationalArrayCopyWork i.groupPacketFields 0 + indexedLoopMetadataBitWork primitive 0 i.groupPacketFields.length +
    i.groupRatioMetadataWork primitive c

def groupPacketMetadataBound (c s : ℕ) : ℕ :=
  72 * (1 + 2 * expressionHeightBudget s 1) + indexedLoopMetadataBound c 6 +
    rationalEnvironmentMetadataBound c 2 (1 + 2 * s) + 4 * RationalExpression.metadataInstructionBound c 2 4

theorem OnLattice.groupRatioMetadataWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.groupRatioMetadataWork primitive c ≤ rationalEnvironmentMetadataBound c 2 (1 + 2 * s) +
      4 * RationalExpression.metadataInstructionBound c 2 4 := by
  unfold groupRatioMetadataWork
  split
  · exact Nat.zero_le _
  · rename_i pivot hSome
    have hEnv := RationalLotteryAssemblyCode.environmentMetadataWork_bound primitive c hPrimitive _ _ s
      ((h.resource_height hD hB pivot).mono hWidth) ((h.length_height hD hB pivot).mono hWidth)
    have hExpr := RationalExpression.metadataAllowance_uniform_bound c
      (RationalExpression.div (.input 0) (.input 1) : RationalExpression 2)
      (RationalLotteryAssemblyCode.environment (i.resource pivot) (i.length pivot)) 2 4 le_rfl (by decide)
    exact Nat.add_le_add hEnv hExpr

theorem OnLattice.groupPacketMetadataWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.groupPacketMetadataWork primitive c ≤ groupPacketMetadataBound c s := by
  have hWords := rationalWordWidth_sum_bound i.groupPacketFields (1 + 2 * expressionHeightBudget s 1)
    (fun q hq => rationalWordWidth_of_height (h.groupPacketFields_height hD hB s hBudget hWidth q hq))
  have hLength := i.groupPacketFields_length
  have hCopy := rationalArrayCopyWork_bound i.groupPacketFields 0
  simp only [Nat.zero_add] at hCopy
  have hWords6 := hWords.trans (Nat.mul_le_mul_right _ hLength)
  have hCopy6 : rationalArrayCopyWork i.groupPacketFields 0 ≤ 72 * (1 + 2 * expressionHeightBudget s 1) := by
    have hp := hCopy.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hLength) hWords6)
    exact hp.trans_eq (by ring)
  have hLoop := (indexedLoopMetadataBitWork_bound primitive c hPrimitive i.groupPacketFields.length).trans
    (indexedLoopMetadataBound_mono c hLength)
  have hRatio := h.groupRatioMetadataWork_bound hD hB s hWidth primitive c hPrimitive
  unfold groupPacketMetadataWork groupPacketMetadataBound
  omega

end Blotto.RationalTerminalLotto

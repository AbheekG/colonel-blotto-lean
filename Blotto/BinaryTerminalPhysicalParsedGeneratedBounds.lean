import Blotto.BinaryTerminalPhysicalParsedGeneratedMeasured

/-! Complete measured source bounds include actual physical parsing, bit
generation, validation/store preparation, terminal/global fallback/output and
the encoded allowance. They hold on every frame and entropy state, with every
retained trace prefix. Native machine and observer/allocator joins remain. -/
namespace Blotto.BinaryTerminalPhysicalParsedGeneratedBounds
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalParsedGeneratedMeasured
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S),
    (run next rich frame state).2+BinaryBigEndian.littleValue (run next rich frame state).1.1.2+
      usage (run next rich frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hWork⟩ := BinaryTerminalPhysicalCompleteGeneratedBounds.uniform_work
  obtain ⟨U,e,hUsage⟩ := BinaryTerminalPhysicalCompleteGeneratedBounds.uniform_usage
  obtain ⟨P,f,hParser⟩ := BinaryPRGPhysicalRawRequestMeasured.uniform_joint
  let D := max (max d e) f
  refine ⟨C+U+P,D,?_⟩
  intro S next rich frame state
  have hW := hWork next rich frame state
  have hU := hUsage next rich frame state
  have hP := hParser frame
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ D by dsimp [D]; omega))
  have he := Nat.mul_le_mul_left U (Nat.pow_le_pow_right hX (show e ≤ D by dsimp [D]; omega))
  have hf := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (show f ≤ D by dsimp [D]; omega))
  rw [run_charge,run_erases]
  nlinarith only [hW,hU,hP,hd,he,hf]

theorem all_prefixes : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length) (run next rich frame state).1.2 steps ≤ borrowed+frame.length+B ∧
      framePeak ((run next rich frame state).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := uniform_joint
  refine ⟨C,d,?_⟩
  intro S next rich frame state borrowed steps
  have hu : usage (run next rich frame state).1.2 ≤ C*(frame.length+1)^d := by
    have h := hBound next rich frame state
    omega
  exact all_prefix _ _ hu (borrowed+frame.length) steps

theorem pair_uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    (pair next frame state).2+BinaryBigEndian.littleValue (pair next frame state).1.1.2.1+
      BinaryBigEndian.littleValue (pair next frame state).1.1.2.2+usage (pair next frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_joint
  refine ⟨2*C+128,d,?_⟩
  intro S next frame state
  have hr := hBound next true frame state
  have hp := hBound next false frame (run next true frame state).1.1.1.2
  have hw := wrap_usage 64 2 [(run next true frame state).1.2,
    (run next false frame (run next true frame state).1.1.1.2).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  have hOne := Nat.one_le_pow d (frame.length+1) (by omega)
  rw [pair_eq_reference]
  unfold pairReference
  dsimp only
  nlinarith only [hr,hp,hw,hOne]

theorem pair_all_prefixes : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length) (pair next frame state).1.2 steps ≤ borrowed+frame.length+B ∧
      framePeak ((pair next frame state).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := pair_uniform_joint
  refine ⟨C,d,?_⟩
  intro S next frame state borrowed steps
  have hu : usage (pair next frame state).1.2 ≤ C*(frame.length+1)^d := by
    have h := hBound next frame state
    omega
  exact all_prefix _ _ hu (borrowed+frame.length) steps

end Blotto.BinaryTerminalPhysicalParsedGeneratedBounds

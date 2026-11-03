import Blotto.BinaryGroupRetainedPrimitiveRun
import Blotto.RationalGroupProgramHeight

/-! Successful indexed group rows inherit specification-leaf height bounds.
No tree or semantic source is constructed by the native runtime; source and
leaf certificates are used only to derive original-cached-field prices. -/

namespace Blotto.WordStateMachine

theorem success_forLeaves {S α : Type*} (machine : WordStateMachine S α) (state : S)
    (P : α → Prop) (hLeaves : (machine.specification state).decode.ForLeaves P)
    (N : ℕ) (bits : Fin N → Bool) (row : α) (h : (machine.run N state bits).1 = some row) : P row := by
  rw [machine.run_refines,(machine.specification state).sample_refines] at h
  exact (machine.specification state).decode.sample_forLeaves N bits P hLeaves h

theorem indexed_success_forLeaves {S α : Type*} (machine : WordStateMachine S α) (state : S)
    (P : α → Prop) (hLeaves : (machine.specification state).decode.ForLeaves P)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) (row : α)
    (h : (machine.runCursorIndexed N bits (.state state) pos hp).1 = some row) : P row := by
  rw [machine.runCursorIndexed_window N bits (.state state) pos (N - pos) (by omega)] at h
  change (machine.runCursor (N - pos) (.state state) (WordStateMachine.inputWindow bits pos (N - pos) (by omega))).1 = some row at h
  have he := machine.run_eq_numeric (N - pos) state (WordStateMachine.inputWindow bits pos (N - pos) (by omega))
  rw [WordStateMachine.runNumeric,WordStateMachine.runCursorIndexed_zero] at he
  rw [← he] at h
  exact machine.success_forLeaves state P hLeaves _ _ row h

end Blotto.WordStateMachine
namespace Blotto.BinaryGroupReachedHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs BinaryGroupSamplers
open BinaryCachedThreeDescriptorWork

theorem uniform_success_height {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 2 ≤ s) (hH : UniformHeights input s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N)
    (row : FixedArrayTable m SignedWord)
    (h : (BinaryGroupPartialRun.uniformRun input hC hAd hm K N scalar bits pos hp).1 = some row) :
    ∀ j, RationalHeight (value (row.read j)) (expressionHeightBudget (max s (K + 2)) 21) := by
  obtain ⟨source,hr⟩ := hAd
  have hSource : source.FieldsHeight s := by
    refine ⟨?_,?_⟩
    · rw [← hr.1]; exact hH.1
    · intro j; rw [← hr.2 j]; exact hH.2 j
  have he := BinaryGroupPartialRun.uniformRun_refines input source hC hr ⟨source,hr⟩ hm K N scalar bits pos hp
  have hSome : ((source.program hm K scalar).machine.runCursorIndexed N bits (.state (source.program hm K scalar).start) pos hp).1 =
      some (BinaryGroupPartialRun.sourceRow row) := by
    rw [← he,h,Option.map_some]
  exact (source.program hm K scalar).machine.indexed_success_forLeaves _ _ (hSource.program_leaves hs hm K scalar) N bits pos hp _ hSome

theorem mixed_success_height {m : ℕ} (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights input s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N)
    (row : FixedArrayTable (m+1) SignedWord)
    (h : (BinaryGroupPartialRun.mixedRun input hC hAd hm K N outer scalar bits pos hp).1 = some row) :
    ∀ j, RationalHeight (value (row.read j)) (expressionHeightBudget (max s (K + 2)) 72) := by
  obtain ⟨source,hr⟩ := hAd
  have hSource : source.FieldsHeight s := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [← hr.1]; exact hH.1
    · intro j; rw [← hr.2.1 j]; exact hH.2.1 j
    · rw [← hr.2.2.1]; exact hH.2.2.1
    · rw [← hr.2.2.2]; exact hH.2.2.2
  have he := BinaryGroupPartialRun.mixedRun_refines input source hC hr ⟨source,hr⟩ hm K N outer scalar bits pos hp
  have hSome : ((source.program hm K outer scalar).machine.runCursorIndexed N bits (.state (source.program hm K outer scalar).start) pos hp).1 =
      some (BinaryGroupPartialRun.sourceRow row) := by
    rw [← he,h,Option.map_some]
  exact (source.program hm K outer scalar).machine.indexed_success_forLeaves _ _ (hSource.program_leaves hs hm K outer scalar) N bits pos hp _ hSome

end Blotto.BinaryGroupReachedHeight

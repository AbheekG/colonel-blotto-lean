import Blotto.PreparedProductTransition

/-! Raw rational observations keep the runtime free of real-number casts.
Exact label decoding defines the ideal rational whole-row law; injective cast
transport extends arbitrary bounded tests without enumerating support. -/

namespace Blotto
open scoped BigOperators Classical

namespace PreparedProductSampler

noncomputable def rationalTargetRow {m : ℕ} (prepared : PreparedProductSampler m)
    (label : Fin prepared.tree.guideTree.real.trueSize) : Fin m → ℚ :=
  prepared.tree.decode (label.cast (prepared.tree.guideTree.real_trueSize.trans prepared.tree.guideTree_trueSize))
    ∘ (fun field => field.cast prepared.fields_eq.symm)

noncomputable def rationalNativeKernel {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) :
    BoundedExpectationKernel (Fin m → ℚ) :=
  (fairBitKernel (prepared.bitBudget epsilon)).map (prepared.sample epsilon)

noncomputable def rationalTargetKernel {m : ℕ} (prepared : PreparedProductSampler m) :
    BoundedExpectationKernel (Fin m → ℚ) :=
  (prepared.tree.guideTree.targetKernel prepared.budget prepared.positive_mass).map prepared.rationalTargetRow

def castRow {m : ℕ} (row : Fin m → ℚ) : Allocation m := fun field => (row field : ℝ)

theorem castRow_injective (m : ℕ) : Function.Injective (@castRow m) := by
  intro first second he
  funext field
  exact Rat.cast_injective (congrFun he field)

noncomputable def rationalizeRow {m : ℕ} (row : Allocation m) : Fin m → ℚ :=
  if h : ∃ rational : Fin m → ℚ, castRow rational = row then Classical.choose h else fun _ => 0

theorem rationalizeRow_cast {m : ℕ} (row : Fin m → ℚ) : rationalizeRow (castRow row) = row := by
  unfold rationalizeRow
  have he : ∃ rational : Fin m → ℚ, castRow rational = castRow row := ⟨row, rfl⟩
  rw [dite_eq_left he]
  exact castRow_injective m (Classical.choose_spec he)

theorem rationalTargetRow_cast {m : ℕ} (prepared : PreparedProductSampler m)
    (label : Fin prepared.tree.guideTree.real.trueSize) :
    castRow (prepared.rationalTargetRow label) =
      fun field => prepared.tree.targetRow label (field.cast prepared.fields_eq.symm) := by
  funext field
  rfl

theorem rationalNativeKernel_close {m : ℕ} (prepared : PreparedProductSampler m)
    (epsilon : ℚ) (he : 0 < epsilon) :
    (prepared.rationalNativeKernel epsilon).Close prepared.rationalTargetKernel (epsilon : ℝ) := by
  intro test htest
  let extended := fun row : Allocation m => test (rationalizeRow row)
  have h := prepared.nativeKernel_close epsilon he extended (fun row => htest _)
  have ha : (prepared.nativeKernel epsilon).mean extended = (prepared.rationalNativeKernel epsilon).mean test := by
    change (fairBitKernel (prepared.bitBudget epsilon)).mean
      (fun bits => test (rationalizeRow (castRow (prepared.sample epsilon bits)))) = _
    simp only [rationalizeRow_cast]
    rfl
  have hb : prepared.targetKernel.mean extended = prepared.rationalTargetKernel.mean test := by
    change (prepared.tree.guideTree.targetKernel prepared.budget prepared.positive_mass).mean
      (fun label => test (rationalizeRow (fun field => prepared.tree.targetRow label (field.cast prepared.fields_eq.symm)))) = _
    have heq : (fun label => test (rationalizeRow (fun field =>
        prepared.tree.targetRow label (field.cast prepared.fields_eq.symm)))) =
        fun label => test (prepared.rationalTargetRow label) := by
      funext label
      rw [← rationalTargetRow_cast, rationalizeRow_cast]
    rw [heq]
    rfl
  rw [ha, hb] at h
  exact h

end PreparedProductSampler

namespace PreparedRationalTransition

abbrev Observation (m : ℕ) := (Fin m → ℚ) × (Fin m → ℚ) × Fin m

noncomputable def actualKernel {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (K : ℕ) : BoundedExpectationKernel (Observation m) :=
  (a.rationalNativeKernel epsilonA).bind (fun rowA => (b.rationalNativeKernel epsilonB).bind
    (fun rowB => (PreparedProductTransition.fieldNativeKernel values K).map (fun field => (rowA, rowB, field))))

noncomputable def idealKernel {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m) :
    BoundedExpectationKernel (Observation m) :=
  a.rationalTargetKernel.bind (fun rowA => b.rationalTargetKernel.bind
    (fun rowB => (PreparedProductTransition.fieldIdealKernel values).map (fun field => (rowA, rowB, field))))

theorem actualKernel_flat_mean {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (K : ℕ) (test : Observation m → ℝ) :
    (fairBitKernel (PreparedProductTransition.bitBudget a b values epsilonA epsilonB K)).mean
      (fun bits => test (PreparedProductTransition.sample a b values epsilonA epsilonB K bits)) =
      (actualKernel a b values epsilonA epsilonB K).mean test := by
  have hfirst := fairBitKernel_blocks (a.bitBudget epsilonA) (b.bitBudget epsilonB + values.attempt.bitBudget K)
    (fun first rest => test (a.sample epsilonA first,
      b.sample epsilonB (firstBitBlock (b.bitBudget epsilonB) (values.attempt.bitBudget K) rest),
      PreparedProductTransition.fieldSample values K
        (secondBitBlock (b.bitBudget epsilonB) (values.attempt.bitBudget K) rest)))
  apply hfirst.trans
  apply congrArg (fun f => (fairBitKernel (a.bitBudget epsilonA)).mean f)
  funext first
  exact fairBitKernel_blocks (b.bitBudget epsilonB) (values.attempt.bitBudget K)
    (fun second fieldBits => test (a.sample epsilonA first, b.sample epsilonB second,
      PreparedProductTransition.fieldSample values K fieldBits))

theorem kernel_close {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K : ℕ) :
    (actualKernel a b values epsilonA epsilonB K).Close (idealKernel a b values)
      ((epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
  have hfield := PreparedProductTransition.fieldKernel_close values K
  have hInner : ∀ rowA : Fin m → ℚ,
      ((b.rationalNativeKernel epsilonB).bind (fun rowB =>
        (PreparedProductTransition.fieldNativeKernel values K).map (fun field => (rowA, rowB, field)))).Close
      (b.rationalTargetKernel.bind (fun rowB =>
        (PreparedProductTransition.fieldIdealKernel values).map (fun field => (rowA, rowB, field))))
      ((epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
    intro rowA
    exact BoundedExpectationKernel.bind_close _ _ _ _ _ _ (b.rationalNativeKernel_close epsilonB hB)
      (fun rowB => BoundedExpectationKernel.map_close _ _ _ _ hfield)
  have he := BoundedExpectationKernel.bind_close _ _ _ _ _ _ (a.rationalNativeKernel_close epsilonA hA) hInner
  intro f hf
  simpa only [actualKernel, idealKernel, add_assoc] using he f hf

end PreparedRationalTransition
end Blotto

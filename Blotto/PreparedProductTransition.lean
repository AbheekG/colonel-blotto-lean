import Blotto.PreparedProductBatch
import Blotto.RationalRejectionOutputLaw

/-! Prepared native whole-row and field blocks realize one training
observation. Bounded-test error adds across independent player/field blocks;
coordinates inside each player row remain jointly selected. -/

namespace Blotto
open scoped BigOperators Classical

namespace PreparedProductSampler

noncomputable def nativeKernel {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) :
    BoundedExpectationKernel (Allocation m) :=
  (fairBitKernel (prepared.bitBudget epsilon)).map (fun bits field => (prepared.sample epsilon bits field : ℝ))

noncomputable def targetKernel {m : ℕ} (prepared : PreparedProductSampler m) : BoundedExpectationKernel (Allocation m) :=
  (prepared.tree.guideTree.targetKernel prepared.budget prepared.positive_mass).map
    (fun label field => prepared.tree.targetRow label (field.cast prepared.fields_eq.symm))

theorem nativeKernel_close {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) (he : 0 < epsilon) :
    (prepared.nativeKernel epsilon).Close prepared.targetKernel (epsilon : ℝ) := by
  intro f hf
  let tree := prepared.tree.guideTree
  let E := RationalWeightedGuideTree.epsilonPrecision epsilon
  let K := tree.scheduledPrecision E
  let attempts := tree.scheduledAttempts E
  let fallback := prepared.fallback.cast (tree.real_trueSize.trans prepared.tree.guideTree_trueSize).symm
  let test : Fin tree.real.trueSize → ℝ :=
    fun label => f (fun field => prepared.tree.targetRow label (field.cast prepared.fields_eq.symm))
  have hn := tree.rejectionOutput_mean_error prepared.certified prepared.budget prepared.positive_mass
    K attempts fallback test (fun label => hf _)
  have htail := tree.idealFailure_factor_bound prepared.certified prepared.budget prepared.positive_mass attempts
  have hfactor : (1 : ℚ) ≤ tree.factor := by
    have h := tree.real.factor_ge_one prepared.certified
    rw [← tree.factor_real] at h
    exact_mod_cast h
  have hs := rejectionSchedule_total_error tree.factor hfactor tree.nodes E
  have hg := RationalWeightedGuideTree.epsilonPrecision_guard epsilon he
  have hbound : (attempts : ℝ) * (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) +
      rejectionFailure (tree.idealAcceptance prepared.budget) attempts ≤ (epsilon : ℝ) :=
    (add_le_add (le_refl _) htail).trans (hs.trans hg)
  have hrows : ∀ bits : Fin (prepared.bitBudget epsilon) → Bool,
      (fun field => (prepared.sample epsilon bits field : ℝ)) =
        (fun field => prepared.tree.targetRow
          (tree.rejectionOutput prepared.certified prepared.budget prepared.positive_mass K attempts fallback bits)
          (field.cast prepared.fields_eq.symm)) := by
    intro bits
    have ht := prepared.tree.scheduledRow_eq_targetRow prepared.certified prepared.budget prepared.positive_mass E
      prepared.fallback bits
    unfold RationalWeightedGuideTree.scheduledOutput at ht
    have hn := tree.rejectionNativeOutput_eq prepared.certified prepared.budget prepared.positive_mass K attempts
      (prepared.fallback.cast prepared.tree.guideTree_trueSize.symm) bits
    have hfb : ((prepared.fallback.cast prepared.tree.guideTree_trueSize.symm).cast tree.real_trueSize.symm) =
        fallback := Fin.ext rfl
    rw [hfb] at hn
    have hrow := congrArg prepared.tree.targetRow hn
    funext field
    exact (congrFun ht (field.cast prepared.fields_eq.symm)).trans
      (congrFun hrow (field.cast prepared.fields_eq.symm))
  change |(fairBitKernel (prepared.bitBudget epsilon)).mean
      (fun bits => f (fun field => (prepared.sample epsilon bits field : ℝ))) -
        (tree.targetKernel prepared.budget prepared.positive_mass).mean test| ≤ _
  simp_rw [hrows]
  exact hn.trans hbound

end PreparedProductSampler

namespace PreparedProductTransition

def fieldSample {m : ℕ} (values : RationalFieldSelector m) (K : ℕ)
    (bits : Fin (values.attempt.bitBudget K) → Bool) : Fin m := values.attempt.sampleLabel K bits

noncomputable def fieldNativeKernel {m : ℕ} (values : RationalFieldSelector m) (K : ℕ) :
    BoundedExpectationKernel (Fin m) :=
  (fairBitKernel (values.attempt.bitBudget K)).map (fieldSample values K)

noncomputable def fieldIdealKernel {m : ℕ} (values : RationalFieldSelector m) : BoundedExpectationKernel (Fin m) where
  mean := fun f => ∑ j, (values.weight j : ℝ) * f j
  constant := by
    intro c
    rw [← Finset.sum_mul]
    have hs : (∑ j, (values.weight j : ℝ)) = 1 := by exact_mod_cast values.sum_one
    rw [hs, one_mul]
  monotone := by intro f g h; exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (by exact_mod_cast (values.positive j).le))
  add := by intro f g; simp only [mul_add, Finset.sum_add_distrib]

theorem fieldKernel_close {m : ℕ} (values : RationalFieldSelector m) (K : ℕ) :
    (fieldNativeKernel values K).Close (fieldIdealKernel values) (1 / (2 : ℝ) ^ K) := by
  intro f hf
  have he := values.attempt.sampleMean_error K (fun result => f (result.getD values.attempt.fallbackLabel))
    (fun result => hf _)
  exact he

def bitBudget {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (K : ℕ) : ℕ :=
  a.bitBudget epsilonA + (b.bitBudget epsilonB + values.attempt.bitBudget K)

def sample {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (K : ℕ)
    (bits : Fin (bitBudget a b values epsilonA epsilonB K) → Bool) :
    (Fin m → ℚ) × (Fin m → ℚ) × Fin m :=
  let first := firstBitBlock (a.bitBudget epsilonA) (b.bitBudget epsilonB + values.attempt.bitBudget K) bits
  let rest := secondBitBlock (a.bitBudget epsilonA) (b.bitBudget epsilonB + values.attempt.bitBudget K) bits
  (a.sample epsilonA first,
    b.sample epsilonB (firstBitBlock (b.bitBudget epsilonB) (values.attempt.bitBudget K) rest),
    fieldSample values K (secondBitBlock (b.bitBudget epsilonB) (values.attempt.bitBudget K) rest))

theorem sample_feasible {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (K : ℕ)
    (bits : Fin (bitBudget a b values epsilonA epsilonB K) → Bool) :
    Feasible (a.budget : ℝ) (fun field => ((sample a b values epsilonA epsilonB K bits).1 field : ℝ)) ∧
      Feasible (b.budget : ℝ) (fun field => ((sample a b values epsilonA epsilonB K bits).2.1 field : ℝ)) :=
  ⟨a.sample_feasible _ _, b.sample_feasible _ _⟩

noncomputable def actualKernel {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (K : ℕ) : BoundedExpectationKernel (Allocation m × Allocation m × Fin m) :=
  (a.nativeKernel epsilonA).bind (fun rowA => (b.nativeKernel epsilonB).bind
    (fun rowB => (fieldNativeKernel values K).map (fun field => (rowA, rowB, field))))

noncomputable def idealKernel {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m) :
    BoundedExpectationKernel (Allocation m × Allocation m × Fin m) :=
  a.targetKernel.bind (fun rowA => b.targetKernel.bind
    (fun rowB => (fieldIdealKernel values).map (fun field => (rowA, rowB, field))))

theorem actualKernel_flat_mean {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (K : ℕ) (f : Allocation m × Allocation m × Fin m → ℝ) :
    (fairBitKernel (bitBudget a b values epsilonA epsilonB K)).mean
      (fun bits => f (fun field => ((sample a b values epsilonA epsilonB K bits).1 field : ℝ),
        (fun field => ((sample a b values epsilonA epsilonB K bits).2.1 field : ℝ)),
        (sample a b values epsilonA epsilonB K bits).2.2)) =
      (actualKernel a b values epsilonA epsilonB K).mean f := by
  have hfirst := fairBitKernel_blocks (a.bitBudget epsilonA) (b.bitBudget epsilonB + values.attempt.bitBudget K)
    (fun first rest => f (fun field => (a.sample epsilonA first field : ℝ),
      (fun field => (b.sample epsilonB (firstBitBlock (b.bitBudget epsilonB) (values.attempt.bitBudget K) rest) field : ℝ)),
      fieldSample values K (secondBitBlock (b.bitBudget epsilonB) (values.attempt.bitBudget K) rest)))
  apply hfirst.trans
  apply congrArg (fun test => (fairBitKernel (a.bitBudget epsilonA)).mean test)
  funext first
  exact fairBitKernel_blocks (b.bitBudget epsilonB) (values.attempt.bitBudget K)
    (fun second fieldBits => f (fun field => (a.sample epsilonA first field : ℝ),
      (fun field => (b.sample epsilonB second field : ℝ)), fieldSample values K fieldBits))

theorem kernel_close {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K : ℕ) :
    (actualKernel a b values epsilonA epsilonB K).Close (idealKernel a b values)
      ((epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
  have hfield := fieldKernel_close values K
  have hInner : ∀ rowA : Allocation m,
      ((b.nativeKernel epsilonB).bind (fun rowB =>
        (fieldNativeKernel values K).map (fun field => (rowA, rowB, field)))).Close
      (b.targetKernel.bind (fun rowB =>
        (fieldIdealKernel values).map (fun field => (rowA, rowB, field))))
      ((epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
    intro rowA
    exact BoundedExpectationKernel.bind_close _ _ _ _ _ _ (b.nativeKernel_close epsilonB hB)
      (fun rowB => BoundedExpectationKernel.map_close _ _ _ _ hfield)
  have he := BoundedExpectationKernel.bind_close _ _ _ _ _ _ (a.nativeKernel_close epsilonA hA) hInner
  intro f hf
  simpa only [actualKernel, idealKernel, add_assoc] using he f hf

theorem flat_mean_error {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K : ℕ)
    (f : Allocation m × Allocation m × Fin m → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(fairBitKernel (bitBudget a b values epsilonA epsilonB K)).mean
      (fun bits => f (fun field => ((sample a b values epsilonA epsilonB K bits).1 field : ℝ),
        (fun field => ((sample a b values epsilonA epsilonB K bits).2.1 field : ℝ)),
        (sample a b values epsilonA epsilonB K bits).2.2)) - (idealKernel a b values).mean f| ≤
      (epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K := by
  rw [actualKernel_flat_mean]
  exact kernel_close a b values epsilonA epsilonB hA hB K f hf

noncomputable def opposingLossA {m : ℕ} (candidate : Allocation m)
    (observation : Allocation m × Allocation m × Fin m) : ℝ :=
  share (observation.2.1 observation.2.2) (candidate observation.2.2)

noncomputable def opposingLossB {m : ℕ} (candidate : Allocation m)
    (observation : Allocation m × Allocation m × Fin m) : ℝ :=
  share (observation.1 observation.2.2) (candidate observation.2.2)

theorem opposingLossA_unit {m : ℕ} (candidate : Allocation m) :
    ∀ observation, 0 ≤ opposingLossA candidate observation ∧ opposingLossA candidate observation ≤ 1 :=
  fun _ => ⟨share_nonneg _ _, share_le_one _ _⟩

theorem opposingLossB_unit {m : ℕ} (candidate : Allocation m) :
    ∀ observation, 0 ≤ opposingLossB candidate observation ∧ opposingLossB candidate observation ≤ 1 :=
  fun _ => ⟨share_nonneg _ _, share_le_one _ _⟩

theorem ideal_opposingLossA {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (candidate : Allocation m) :
    (idealKernel a b values).mean (opposingLossA candidate) =
      b.targetKernel.mean (fun row => payoff values.values row candidate) := by
  change a.targetKernel.mean (fun rowA => b.targetKernel.mean (fun rowB =>
    ∑ field, (values.weight field : ℝ) * share (rowB field) (candidate field))) = _
  have he : (fun rowA : Allocation m => b.targetKernel.mean (fun rowB =>
      ∑ field, (values.weight field : ℝ) * share (rowB field) (candidate field))) =
      fun _ => b.targetKernel.mean (fun row => payoff values.values row candidate) := rfl
  rw [he, a.targetKernel.constant]

theorem ideal_opposingLossB {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (candidate : Allocation m) :
    (idealKernel a b values).mean (opposingLossB candidate) =
      a.targetKernel.mean (fun row => payoff values.values row candidate) := by
  change a.targetKernel.mean (fun rowA => b.targetKernel.mean (fun _rowB =>
    ∑ field, (values.weight field : ℝ) * share (rowA field) (candidate field))) = _
  simp only [b.targetKernel.constant]
  rfl

theorem opposingLossA_mean_error {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K : ℕ)
    (candidate : Allocation m) :
    |(actualKernel a b values epsilonA epsilonB K).mean (opposingLossA candidate) -
      b.targetKernel.mean (fun row => payoff values.values row candidate)| ≤
      (epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K := by
  rw [← ideal_opposingLossA a b values candidate]
  exact kernel_close a b values epsilonA epsilonB hA hB K (opposingLossA candidate) (opposingLossA_unit candidate)

theorem opposingLossB_mean_error {m : ℕ} (a b : PreparedProductSampler m) (values : RationalFieldSelector m)
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K : ℕ)
    (candidate : Allocation m) :
    |(actualKernel a b values epsilonA epsilonB K).mean (opposingLossB candidate) -
      a.targetKernel.mean (fun row => payoff values.values row candidate)| ≤
      (epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K := by
  rw [← ideal_opposingLossB a b values candidate]
  exact kernel_close a b values epsilonA epsilonB hA hB K (opposingLossB candidate) (opposingLossB_unit candidate)

end PreparedProductTransition
end Blotto

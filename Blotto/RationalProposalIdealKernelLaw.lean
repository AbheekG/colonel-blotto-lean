import Blotto.NormalizedKernelMean

/-! The actual recursive ideal kernel has the normalized augmented R160
record law on certified positive conditional support. Zero-weight branches
are removed algebraically before any child positive-prefix law is invoked. -/

namespace Blotto
open scoped BigOperators Classical

namespace RationalWeightedGuideTree

theorem forkWeights_sum (left right : RationalWeightedGuideTree) (B : ℚ) :
    (∑ i, forkWeights left right B i) = left.guide.convolution right.guide B := by
  exact (left.guide.convolution_prefix_right right.guide B).symm

theorem certified_true_prefix_of_guide (tree : RationalWeightedGuideTree)
    (hc : tree.real.LowerCertified) (B : ℚ) (hg : 0 < tree.guidePrefix B) :
    0 < tree.real.trueFamily.prefixMass (B : ℝ) := by
  have hgr : 0 < (tree.guidePrefix B : ℝ) := by exact_mod_cast hg
  rw [guidePrefix_real] at hgr
  exact (tree.real.prefix_positive_iff hc _).mp hgr

theorem certified_fork_normalizer_positive {p : ℕ} (guide : RationalWeightedFamily p)
    (gamma : ℚ) (left right : RationalWeightedGuideTree)
    (hc : (fork guide gamma left right).real.LowerCertified) (B : ℚ)
    (hm : 0 < (fork guide gamma left right).real.trueFamily.prefixMass (B : ℝ)) :
    0 < left.guide.convolution right.guide B := by
  have hm' : 0 < left.real.trueFamily.convolution right.real.trueFamily (B : ℝ) := by
    change 0 < (left.real.trueFamily.product right.real.trueFamily).prefixMass (B : ℝ) at hm
    rw [WeightedResourceFamily.product_prefix] at hm
    exact hm
  have hz := (WeightedGuideTree.root_synthetic_positive_iff left.real right.real
    hc.2.1 hc.2.2.1 (B : ℝ)).mpr hm'
  rw [← guideConvolution_real] at hz
  exact_mod_cast hz

theorem positive_right_residual_guide (left right : RationalWeightedGuideTree)
    (hc : right.real.LowerCertified) (B : ℚ) (i : Fin left.guideSize) (r : right.Record)
    (hselected : 0 < forkWeights left right B i)
    (hq : 0 < right.probability (B - left.guide.resource i) r) :
    0 < left.guidePrefix (B - right.resource r) := by
  have hm : 0 < left.guide.mass i := by
    by_contra hn
    have hz : left.guide.mass i = 0 :=
      le_antisymm (le_of_not_gt hn) (left.guide.mass_nonnegative i)
    simp only [forkWeights, hz, zero_mul, lt_self_iff_false] at hselected
  have hr := right.positive_feasible hc _ r hq
  have he : left.guide.resource i ≤ B - right.resource r := by linarith
  have hn : ∀ j ∈ (Finset.univ : Finset (Fin left.guideSize)),
      0 ≤ if left.guide.resource j ≤ B - right.resource r then left.guide.mass j else 0 := by
    intro j _
    split_ifs
    · exact left.guide.mass_nonnegative j
    · exact le_rfl
  have hp := Finset.single_le_sum hn (Finset.mem_univ i)
  change 0 < left.guide.prefixMass (B - right.resource r)
  exact hm.trans_le (by simpa only [RationalWeightedFamily.prefixMass, he, ite_true] using hp)

theorem proposalKernel_ideal_mean (tree : RationalWeightedGuideTree)
    (hc : tree.real.LowerCertified) (B : ℚ) (K : ℕ)
    (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (f : Option tree.Record → ℝ) :
    (tree.proposalKernel false B K).mean f =
      ∑ record : tree.Record, (tree.probability B record : ℝ) * f (some record) := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    have hp : 0 < family.prefixMass B := by
      have he := family.prefixMass_real B
      change 0 < family.real.prefixMass (B : ℝ) at hm
      rw [← he] at hm
      exact_mod_cast hm
    exact leafKernel_mean family guide gamma B K hp f
  | fork guide gamma left right ihLeft ihRight =>
    let f' : Option (Fin left.guideSize × right.Record × left.Record) → ℝ := f
    have hz := certified_fork_normalizer_positive guide gamma left right hc B hm
    have hsum : 0 < ∑ i, forkWeights left right B i := by rw [forkWeights_sum]; exact hz
    change (totalNormalizedKernel (forkWeights left right B) _).mean
      (fun selected =>
        (match selected with
        | none => BoundedExpectationKernel.point none
        | some i => (right.proposalKernel false (B - left.guide.resource i) K).bind (fun r =>
            match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.proposalKernel false (B - right.resource r) K).map
                (fun l => l.map (fun l => (i, r, l))))).mean f) = _
    rw [totalNormalizedKernel_mean _ _ hsum]
    have hright : ∀ i : Fin left.guideSize,
        ((forkWeights left right B i / ∑ j, forkWeights left right B j : ℚ) : ℝ) *
          (right.proposalKernel false (B - left.guide.resource i) K).mean
            (fun r => match r with
              | none => f' none
              | some r => (left.proposalKernel false (B - right.resource r) K).mean
                  (fun l => f' (l.map (fun l => (i, r, l))))) =
        ∑ r : right.Record, ∑ l : left.Record,
          (((forkWeights left right B i / ∑ j, forkWeights left right B j : ℚ) : ℝ) *
            (right.probability (B - left.guide.resource i) r : ℝ) *
            (left.probability (B - right.resource r) l : ℝ)) * f' (some (i, r, l)) := by
      intro i
      by_cases hi : forkWeights left right B i = 0
      · simp only [hi, zero_div, Rat.cast_zero, zero_mul, Finset.sum_const_zero]
      have hiPos : 0 < forkWeights left right B i :=
        lt_of_le_of_ne (forkWeights_nonnegative left right B i) (Ne.symm hi)
      have hgRight : 0 < right.guidePrefix (B - left.guide.resource i) := by
        by_contra hn
        have he : right.guidePrefix (B - left.guide.resource i) = 0 :=
          le_antisymm (le_of_not_gt hn) (right.guide.prefixMass_nonnegative _)
        simp only [forkWeights, he, mul_zero, lt_self_iff_false] at hiPos
      rw [ihRight hc.2.2.1 _ (certified_true_prefix_of_guide right hc.2.2.1 _ hgRight)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : right.probability (B - left.guide.resource i) r = 0
      · simp only [hr, Rat.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero]
      have hrPos : 0 < right.probability (B - left.guide.resource i) r := by
        have he : 0 ≤ (right.probability (B - left.guide.resource i) r : ℝ) := by
          rw [right.probability_real]
          exact right.real.proposalProbability_nonnegative _ _
        have he' : 0 ≤ right.probability (B - left.guide.resource i) r := by exact_mod_cast he
        exact lt_of_le_of_ne he' (Ne.symm hr)
      have hgLeft := positive_right_residual_guide left right hc.2.2.1 B i r hiPos hrPos
      dsimp only
      rw [ihLeft hc.2.1 _ (certified_true_prefix_of_guide left hc.2.1 _ hgLeft)]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      simp only [Option.map_some]
      ring
    calc
      _ = ∑ i : Fin left.guideSize, ∑ r : right.Record, ∑ l : left.Record,
          (((forkWeights left right B i / ∑ j, forkWeights left right B j : ℚ) : ℝ) *
            (right.probability (B - left.guide.resource i) r : ℝ) *
            (left.probability (B - right.resource r) l : ℝ)) * f' (some (i, r, l)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hn : (fun r : Option right.Record =>
            (match r with
            | none => BoundedExpectationKernel.point (none : Option (Fin left.guideSize × right.Record × left.Record))
            | some r => (left.proposalKernel false (B - right.resource r) K).map
                (fun l => l.map (fun l => (i, r, l)))).mean f') =
          (fun r : Option right.Record => match r with
            | none => f' none
            | some r => (left.proposalKernel false (B - right.resource r) K).mean
                (fun l => f' (l.map (fun l => (i, r, l))))) := by
          funext r
          cases r <;> rfl
        have hmEq := congrArg (fun test => (right.proposalKernel false (B - left.guide.resource i) K).mean test) hn
        calc
          _ = ((forkWeights left right B i / ∑ j, forkWeights left right B j : ℚ) : ℝ) *
              (right.proposalKernel false (B - left.guide.resource i) K).mean
                (fun r => match r with
                | none => f' none
                | some r => (left.proposalKernel false (B - right.resource r) K).mean
                    (fun l => f' (l.map (fun l => (i, r, l))))) := by
            exact congrArg (fun x => ((forkWeights left right B i / ∑ j, forkWeights left right B j : ℚ) : ℝ) * x) hmEq
          _ = _ := hright i
      _ = _ := ?_
    rw [forkWeights_sum]
    symm
    rw [show (∑ record : (fork guide gamma left right).Record,
        ((fork guide gamma left right).probability B record : ℝ) * f (some record)) =
      ∑ i : Fin left.guideSize, ∑ r : right.Record, ∑ l : left.Record,
        ((fork guide gamma left right).probability B (i, r, l) : ℝ) * f (some (i, r, l)) by
          calc
            _ = ∑ record : Fin left.guideSize × right.Record × left.Record,
                ((fork guide gamma left right).probability B record : ℝ) * f (some record) := by
              apply @Fintype.sum_equiv (fork guide gamma left right).Record
                (Fin left.guideSize × right.Record × left.Record) ℝ
                (recordFintype (fork guide gamma left right)) (inferInstance) _
                (Equiv.refl (Fin left.guideSize × right.Record × left.Record))
              intro record
              rfl
            _ = _ := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro i _
              exact Fintype.sum_prod_type _]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro l _
    simp only [probability, forkWeights, Rat.cast_mul, f']
    rfl

theorem proposalKernel_ideal_failure (tree : RationalWeightedGuideTree)
    (hc : tree.real.LowerCertified) (B : ℚ) (K : ℕ)
    (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) :
    (tree.proposalKernel false B K).mean (fun record => if record = none then 1 else 0) = 0 := by
  rw [proposalKernel_ideal_mean tree hc B K hm]
  simp only [Option.some_ne_none, ite_false, mul_zero, Finset.sum_const_zero]

theorem proposalKernel_ideal_event (tree : RationalWeightedGuideTree)
    (hc : tree.real.LowerCertified) (B : ℚ) (K : ℕ)
    (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (event : Set (Option tree.Record)) :
    (tree.proposalKernel false B K).mean (fun record => if record ∈ event then 1 else 0) =
      ∑ record : tree.Record, if some record ∈ event then (tree.probability B record : ℝ) else 0 := by
  rw [proposalKernel_ideal_mean tree hc B K hm]
  apply Finset.sum_congr rfl
  intro record _
  split_ifs <;> simp

end RationalWeightedGuideTree
end Blotto

import Blotto.RationalProposalAcceptance

/-! Exact target law of the ideal complete rational proposal/acceptance
attempt. Output labels are the true Cartesian labels in the exact real view;
target weights are truncated at the closed budget before normalization. -/

namespace Blotto
open scoped BigOperators Classical

namespace SparseImportanceProposal

theorem accepted_output_mean {r n : ℕ} (q : SparseImportanceProposal r n)
    (bound : ℝ) (f : Fin n → ℝ) :
    (∑ p, q.acceptedWeight bound p * f (q.output p)) =
      ∑ x, (q.targetWeight x / bound) * f x := by
  rw [← show (∑ x, q.outputWeight bound x * f x) =
      ∑ p, q.acceptedWeight bound p * f (q.output p) by
        unfold outputWeight
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        simp only [ite_mul, zero_mul]
        simp]
  simp_rw [q.outputWeight_eq]

end SparseImportanceProposal

namespace RationalWeightedGuideTree

noncomputable def trueOutput (tree : RationalWeightedGuideTree) (record : tree.Record) :
    Fin tree.real.trueSize := tree.real.proposalOutput (tree.recordReal record)

noncomputable def targetKernel (tree : RationalWeightedGuideTree) (B : ℚ)
    (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) : BoundedExpectationKernel (Fin tree.real.trueSize) where
  mean := fun f => ∑ x, tree.real.feasibleTargetWeight (B : ℝ) x /
    tree.real.trueFamily.prefixMass (B : ℝ) * f x
  constant := by
    intro c
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    change (tree.real.trueFamily.prefixMass (B : ℝ) *
      (tree.real.trueFamily.prefixMass (B : ℝ))⁻¹) * c = c
    rw [mul_inv_cancel₀ (ne_of_gt hm), one_mul]
  monotone := by
    intro f g h
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left (h x)
    apply div_nonneg _ hm.le
    unfold WeightedGuideTree.feasibleTargetWeight
    split_ifs
    · exact tree.real.trueFamily.mass_nonnegative x
    · exact le_rfl
  add := by intro f g; simp only [mul_add, Finset.sum_add_distrib]

noncomputable def idealAcceptance (tree : RationalWeightedGuideTree) (B : ℚ) : ℝ :=
  tree.real.trueFamily.prefixMass (B : ℝ) / (tree.acceptanceBound B : ℝ)

theorem acceptance_output_sum (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ))
    (f : Fin tree.real.trueSize → ℝ) :
    (∑ record : tree.Record, (tree.probability B record : ℝ) *
        (tree.acceptanceProbability B record : ℝ) * f (tree.trueOutput record)) =
      ∑ x, tree.real.feasibleTargetWeight (B : ℝ) x / (tree.acceptanceBound B : ℝ) * f x := by
  let cert := tree.real.importanceCertificate hc (B : ℝ) hm
  have he := cert.accepted_output_mean (tree.acceptanceBound B : ℝ) f
  have hrecord : (∑ record : tree.Record, (tree.probability B record : ℝ) *
      (tree.acceptanceProbability B record : ℝ) * f (tree.trueOutput record)) =
      ∑ record : tree.real.ProposalRecord,
        tree.real.proposalProbability (B : ℝ) record *
          (tree.real.proposalImportance (B : ℝ) record / (tree.acceptanceBound B : ℝ)) *
          f (tree.real.proposalOutput record) := by
    simp only [acceptanceProbability, Rat.cast_div, probability_real, importance_real, trueOutput]
    exact Equiv.sum_comp tree.recordEquivReal (fun record =>
      tree.real.proposalProbability (B : ℝ) record *
        (tree.real.proposalImportance (B : ℝ) record / (tree.acceptanceBound B : ℝ)) *
        f (tree.real.proposalOutput record))
  rw [hrecord]
  have hcert : (∑ p, cert.acceptedWeight (tree.acceptanceBound B : ℝ) p * f (cert.output p)) =
      ∑ record : tree.real.ProposalRecord,
        tree.real.proposalProbability (B : ℝ) record *
          (tree.real.proposalImportance (B : ℝ) record / (tree.acceptanceBound B : ℝ)) *
          f (tree.real.proposalOutput record) := by
    rw [← Equiv.sum_comp tree.real.recordEquiv]
    simp only [cert, WeightedGuideTree.importanceCertificate, SparseImportanceProposal.acceptedWeight,
      Equiv.symm_apply_apply]
  rw [← hcert]
  exact he

theorem acceptance_sum_eq (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) :
    (∑ record : tree.Record, (tree.probability B record : ℝ) *
      (tree.acceptanceProbability B record : ℝ)) = tree.idealAcceptance B := by
  have he := tree.acceptance_output_sum hc B hm (fun _ => 1)
  simp only [mul_one] at he
  rw [he]
  simp only [idealAcceptance, div_eq_mul_inv, ← Finset.sum_mul]
  rfl

theorem idealAcceptance_bounds (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) :
    0 < tree.idealAcceptance B ∧ tree.idealAcceptance B ≤ 1 ∧
      1 / (tree.factor : ℝ) ≤ tree.idealAcceptance B := by
  have hbq := tree.acceptanceBound_positive hc B hm
  have hb : 0 < (tree.acceptanceBound B : ℝ) := by exact_mod_cast hbq
  have hfactor : 0 < (tree.factor : ℝ) := by
    rw [factor_real]
    linarith [tree.real.factor_ge_one hc]
  have hguide : 0 < (tree.guidePrefix B : ℝ) := by
    rw [guidePrefix_real]
    exact (tree.real.prefix_positive_iff hc (B : ℝ)).mpr hm
  refine ⟨div_pos hm hb, ?_, ?_⟩
  · rw [← acceptance_sum_eq tree hc B hm]
    calc
      _ ≤ ∑ record : tree.Record, (tree.probability B record : ℝ) := by
        apply Finset.sum_le_sum
        intro record _
        have hq : 0 ≤ (tree.probability B record : ℝ) := by
          rw [probability_real]
          exact tree.real.proposalProbability_nonnegative _ _
        have hp : (tree.acceptanceProbability B record : ℝ) ≤ 1 := by
          exact_mod_cast (tree.acceptanceProbability_unit hc B hm record).2
        exact mul_le_of_le_one_right hq hp
      _ = 1 := by exact_mod_cast tree.probability_sum hc B hm
  · have hl : (tree.guidePrefix B : ℝ) ≤ tree.real.trueFamily.prefixMass (B : ℝ) := by
      rw [guidePrefix_real]
      exact (tree.real.lower_envelope hc (B : ℝ)).1
    have he : 1 / (tree.factor : ℝ) =
        (tree.guidePrefix B : ℝ) / ((tree.guidePrefix B : ℝ) * (tree.factor : ℝ)) := by
      field_simp
    rw [he]
    unfold idealAcceptance acceptanceBound
    rw [Rat.cast_mul]
    exact div_le_div_of_nonneg_right hl (mul_nonneg hguide.le hfactor.le)

theorem attemptKernel_ideal_target_mean (tree : RationalWeightedGuideTree)
    (hc : tree.real.LowerCertified) (B : ℚ)
    (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (f : Option (Fin tree.real.trueSize) → ℝ) :
    ((tree.attemptKernel false hc B hm K).map (fun record => record.map tree.trueOutput)).mean f =
      tree.idealAcceptance B * (tree.targetKernel B hm).mean (fun x => f (some x)) +
        (1 - tree.idealAcceptance B) * f none := by
  change (tree.proposalKernel false B K).mean
    (fun record => (acceptanceKernel (fun record => (tree.acceptanceProbability B record : ℝ))
      (fun record => by exact_mod_cast tree.acceptanceProbability_unit hc B hm record) record).mean
        (fun result => f (result.map tree.trueOutput))) = _
  rw [proposalKernel_ideal_mean tree hc B K hm]
  change (∑ record : tree.Record, (tree.probability B record : ℝ) *
    ((tree.acceptanceProbability B record : ℝ) * f (some (tree.trueOutput record)) +
      (1 - (tree.acceptanceProbability B record : ℝ)) * f none)) = _
  simp only [mul_add, Finset.sum_add_distrib]
  have haccept := tree.acceptance_output_sum hc B hm (fun x => f (some x))
  have hsum : (∑ record : tree.Record, (tree.probability B record : ℝ)) = 1 := by
    exact_mod_cast tree.probability_sum hc B hm
  have hreject : (∑ record : tree.Record, (tree.probability B record : ℝ) *
      ((1 - (tree.acceptanceProbability B record : ℝ)) * f none)) =
      (1 - tree.idealAcceptance B) * f none := by
    have he : (∑ record : tree.Record, (tree.probability B record : ℝ) *
        ((1 - (tree.acceptanceProbability B record : ℝ)) * f none)) =
      ((∑ record : tree.Record, (tree.probability B record : ℝ)) -
        ∑ record : tree.Record, (tree.probability B record : ℝ) *
          (tree.acceptanceProbability B record : ℝ)) * f none := by
      rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro record _
      ring
    rw [he, hsum, tree.acceptance_sum_eq hc B hm]
  have hfirst : (∑ record : tree.Record, (tree.probability B record : ℝ) *
      ((tree.acceptanceProbability B record : ℝ) * f (some (tree.trueOutput record)))) =
      tree.idealAcceptance B * (tree.targetKernel B hm).mean (fun x => f (some x)) := by
    simp only [← mul_assoc]
    rw [haccept]
    unfold idealAcceptance targetKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    field_simp
  rw [hfirst, hreject]

end RationalWeightedGuideTree
end Blotto

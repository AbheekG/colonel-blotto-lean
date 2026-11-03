import Blotto.ImplicitConstructedDirectAccess
import Blotto.ImplicitZeroFallback
import Blotto.ExactSizedDraw

/-! Actual prepared native access trees use direct leaf guides, cap queries and
block-prefix importance. Repeated draws use the stored tree/access only. The
old prepared model and exact Sized draw refinement are derived, preserving all
budget and conditional target-law guarantees. -/

namespace Blotto.ImplicitLeafCounts

namespace TreeAccess

def nativeOutput (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.trueSize)
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) : Fin tree.projected.trueSize :=
  ((rejection tree access hc budget hm K leafAttempts attempts bits).map tree.nativeOutputLabel).getD fallback

theorem nativeOutput_eq (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.trueSize) (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) :
    nativeOutput tree access hc budget hm K leafAttempts attempts fallback bits =
      tree.nativeOutput hc budget hm K leafAttempts attempts fallback bits := by
  unfold nativeOutput ProposalTree.nativeOutput
  rw [rejection_eq]

def epsilonOutput (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.projected.trueSize) (bits : Fin (tree.epsilonSeedBudget epsilon) → Bool) : Fin tree.projected.trueSize :=
  let E := RationalWeightedGuideTree.epsilonPrecision epsilon
  nativeOutput tree access hc budget hm (tree.rejectionPrecision E) (tree.rejectionPrecision E)
    (tree.rejectionAttempts E) fallback bits

theorem epsilonOutput_eq (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.projected.trueSize) (bits : Fin (tree.epsilonSeedBudget epsilon) → Bool) :
    epsilonOutput tree access hc budget hm epsilon fallback bits = tree.epsilonOutput hc budget hm epsilon fallback bits :=
  nativeOutput_eq tree access hc budget hm _ _ _ fallback bits

end TreeAccess

structure PreparedAccessSampler where
  model : PreparedImplicitSampler
  access : TreeAccess model.tree

namespace PreparedAccessSampler

def bitBudget (prepared : PreparedAccessSampler) (epsilon : ℚ) : ℕ := prepared.model.bitBudget epsilon

def drawLabel (prepared : PreparedAccessSampler) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : Fin prepared.model.tree.projected.trueSize :=
  TreeAccess.epsilonOutput prepared.model.tree prepared.access prepared.model.certified prepared.model.budget
    (prepared.model.tree.prefix_positive_of_feasible_label prepared.model.budget prepared.model.fallback prepared.model.fallback_feasible)
    epsilon prepared.model.fallback bits

def drawRow (prepared : PreparedAccessSampler) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : Fin (prepared.model.tree.allocationTree prepared.model.nonnegative).fields → ℚ :=
  prepared.model.tree.decodeLabel prepared.model.nonnegative (prepared.drawLabel epsilon bits)

theorem drawLabel_eq (prepared : PreparedAccessSampler) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : prepared.drawLabel epsilon bits = prepared.model.drawLabel epsilon bits :=
  TreeAccess.epsilonOutput_eq _ _ _ _ _ _ _ _

theorem drawRow_eq (prepared : PreparedAccessSampler) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : prepared.drawRow epsilon bits = prepared.model.drawRow epsilon bits := by
  unfold drawRow PreparedImplicitSampler.drawRow
  rw [prepared.drawLabel_eq]

def sized {m : ℕ} (prepared : PreparedAccessSampler)
    (fields : (prepared.model.tree.allocationTree prepared.model.nonnegative).fields = m) : ExactSizedDraw m where
  model := ⟨prepared.model, fields⟩
  draw := fun epsilon bits field => prepared.drawRow epsilon bits (field.cast fields.symm)
  refines := by
    intro epsilon bits
    unfold SizedImplicitSampler.sample SizedImplicitSampler.reindex
    funext field
    change prepared.drawRow epsilon bits (field.cast fields.symm) = prepared.model.drawRow epsilon bits (field.cast fields.symm)
    exact congrFun (prepared.drawRow_eq epsilon bits) (field.cast fields.symm)

theorem resource_cast_congr (first second : ProposalTree) (h : first = second) (n : ℕ) (label : Fin n)
    (hf : first.projected.trueSize = n) (hs : second.projected.trueSize = n) :
    first.projected.real.trueFamily.resource ((label.cast hf.symm).cast first.projected.real_trueSize.symm) =
      second.projected.real.trueFamily.resource ((label.cast hs.symm).cast second.projected.real_trueSize.symm) := by
  cases h
  rfl

def prepare (tree : ProposalTree) (access : TreeAccess tree) (hn : tree.NonnegativeResources) (budget : ℚ)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    PreparedAccessSampler :=
  let built := constructAccess tree access
  have hEq : built.model = tree.constructed := constructAccess_model_eq tree access
  have hSize : built.model.projected.trueSize = tree.projected.trueSize :=
    (congrArg (fun model : ProposalTree => model.projected.trueSize) hEq).trans tree.constructed_trueSize
  { model :=
      { tree := built.model
        budget := budget
        nonnegative := by rw [hEq]; exact tree.rebuild_nonnegativeResources hn tree.constructionGamma tree.constructionGamma_ge_one
        certified := by rw [hEq]; exact tree.constructed_certified
        fallback := fallback.cast hSize.symm
        fallback_feasible := (resource_cast_congr built.model tree.constructed hEq _ fallback hSize tree.constructed_trueSize).trans_le
          (tree.constructed_fallback_feasible budget fallback hf) }
    access := built.access }

def prepareZero (tree : ProposalTree) (access : TreeAccess tree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (budget : ℚ) (hb : 0 ≤ budget) : PreparedAccessSampler :=
  prepare tree access hn budget tree.zeroLabel (tree.zeroLabel_feasible hz budget hb)

theorem prepared_model_congr (first second : ProposalTree) (h : first = second) (budget : ℚ)
    (hnf : first.NonnegativeResources) (hns : second.NonnegativeResources)
    (hcf : first.projected.real.LowerCertified) (hcs : second.projected.real.LowerCertified)
    (n : ℕ) (label : Fin n) (hf : first.projected.trueSize = n) (hs : second.projected.trueSize = n)
    (hff : first.projected.real.trueFamily.resource ((label.cast hf.symm).cast first.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (hfs : second.projected.real.trueFamily.resource ((label.cast hs.symm).cast second.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    (⟨first, budget, hnf, hcf, label.cast hf.symm, hff⟩ : PreparedImplicitSampler) =
      (⟨second, budget, hns, hcs, label.cast hs.symm, hfs⟩ : PreparedImplicitSampler) := by
  cases h
  rfl

theorem prepare_model_eq (tree : ProposalTree) (access : TreeAccess tree) (hn : tree.NonnegativeResources) (budget : ℚ)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    (prepare tree access hn budget fallback hf).model = PreparedImplicitSampler.prepare tree hn budget fallback hf := by
  exact prepared_model_congr (constructAccess tree access).model tree.constructed (constructAccess_model_eq tree access)
    budget _ _ _ _ _ fallback
    ((congrArg (fun model : ProposalTree => model.projected.trueSize) (constructAccess_model_eq tree access)).trans tree.constructed_trueSize)
    tree.constructed_trueSize _ _

theorem prepareZero_model_eq (tree : ProposalTree) (access : TreeAccess tree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (budget : ℚ) (hb : 0 ≤ budget) : (prepareZero tree access hn hz budget hb).model = tree.prepareZero hn hz budget hb :=
  prepare_model_eq tree access hn budget tree.zeroLabel (tree.zeroLabel_feasible hz budget hb)

theorem drawRow_contract (prepared : PreparedAccessSampler) (epsilon : ℚ) (he : 0 < epsilon) :
    (∀ bits : Fin (prepared.bitBudget epsilon) → Bool, Feasible (prepared.model.budget : ℝ)
      (fun field => (prepared.drawRow epsilon bits field : ℝ))) ∧
    (∀ test : Allocation (prepared.model.tree.allocationTree prepared.model.nonnegative).fields → ℝ,
      (∀ row, 0 ≤ test row ∧ test row ≤ 1) →
      |(fairBitKernel (prepared.bitBudget epsilon)).mean (fun bits => test (fun field => (prepared.drawRow epsilon bits field : ℝ))) -
        (prepared.model.tree.projected.targetKernel prepared.model.budget
          (prepared.model.tree.prefix_positive_of_feasible_label prepared.model.budget prepared.model.fallback prepared.model.fallback_feasible)).mean
          (fun label => test (prepared.model.tree.targetAllocation prepared.model.nonnegative label))| ≤ (epsilon : ℝ)) := by
  simp_rw [prepared.drawRow_eq]
  exact prepared.model.drawRow_contract epsilon he

end PreparedAccessSampler
end Blotto.ImplicitLeafCounts

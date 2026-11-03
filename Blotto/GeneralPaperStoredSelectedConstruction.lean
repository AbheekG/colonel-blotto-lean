import Blotto.GeneralPaperStoredDominantOuterContract

/-! One actual selected source constructor dispatches the retained branch
and returns one combined memory. Native capacities are derived in both
branches; grouped roots retain their smaller inner width. -/
namespace Blotto.GeneralPaperStoredSelectedConstruction
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def recast {I A : ℕ} (h : I = A) (value : Installed I) : Installed A := h ▸ value

theorem grouped_address {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (small : ∀ j,2 * v.weight j ≤ 1)
    (source : GeneralPaperEqualStoredBitSampler.Sampler (GeneralPaperEqualFiniteKernel.terminal v small).partition
      (GeneralPaperEqualFiniteKernel.lottery v small)) (hK : source.exponent = k) (hB : source.prepared.budget = budget)
    (hBranch : a.branch = .grouped small source hK hB) : source.address + 1 = a.address := by
  rw [a.address_correct,hBranch]
  rfl

def run {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : Option (Installed a.address) × ℕ :=
  match hBranch : a.branch with
  | .dominant chosen _ row _ =>
    let actual := GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row
    (actual.values,actual.work)
  | .grouped small source hK hB =>
    let actual := GeneralPaperStoredGroupedOuterConstruction.run model S source
    (actual.values.map (recast (grouped_address a small source hK hB hBranch)),actual.work)

def Contract {n : ℕ} (model : RationalCostModel) (A : ℕ) (returned : Installed A)
    {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : GeneralPaperEqualBitBranch.Prepared v k budget → Prop
  | .dominant _ _ row _ => (GeneralPaperStoredDominantOuterDraw.run model A returned).values = some row.data ∧
      (GeneralPaperStoredDominantOuterDraw.run model A returned).count = n
  | .grouped _ source _ _ => GeneralPaperStoredGroupedOuterDraw.Refines model A returned source

theorem source {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    ∃ returned : Installed a.address,(run model S a).1 = some returned ∧ returned.work = (run model S a).2 ∧
      Contract model a.address returned a.branch := by
  rcases a with ⟨branch,A,hAddress⟩
  cases branch with
  | dominant chosen heavy row correct =>
    let a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget :=
      ⟨.dominant chosen heavy row correct,A,hAddress⟩
    obtain ⟨returned,hReturn,_,hWork,hDraw⟩ := GeneralPaperStoredDominantOuterContract.constructed model W S k values v hv budget a chosen heavy row correct rfl
    refine ⟨returned,?_,hWork,hDraw⟩
    simpa only [run,a] using hReturn
  | grouped small sampler hK hB =>
    dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
    subst A
    let a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget :=
      ⟨.grouped small sampler hK hB,sampler.address + 1,rfl⟩
    have hI := GeneralPaperEqualMeasuredLayout.inner_capacity model W S k values v hv budget a
    have hT := GeneralPaperEqualMeasuredLayout.total_capacity model W S k values v hv budget a
    obtain ⟨returned,hReturn,_,hWork,hDraw⟩ := GeneralPaperStoredGroupedOuterConstruction.source model S sampler hI hT
    refine ⟨returned,?_,hWork,hDraw⟩
    simp only [run,hReturn,Option.map_some,recast]

theorem every_returned {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (run model S a).1 = some returned) :
    Contract model a.address returned a.branch := by
  obtain ⟨actual,hActual,_,hContract⟩ := source model W S k values v hv budget a
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact hContract

end Blotto.GeneralPaperStoredSelectedConstruction

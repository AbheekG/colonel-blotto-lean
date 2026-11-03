import Blotto.GeneralPaperPairSegmentPreparation

/-! The stored group-array size selects the complementary pair or three-input
factory. Both return the exact existing nine-slot descriptor with complete
bit prices, including all zero slots. Type transports and certificates erase. -/
namespace Blotto.GeneralPaperUniformSegmentPreparation
set_option autoImplicit false
set_option maxHeartbeats 1400000

def pair {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h2 : m = 2)
    (model : RationalCostModel) (A : ℕ) : PreparedSegmentDescriptor (i.lottery hm) × ℕ := by
  subst m
  exact GeneralPaperPairSegmentPreparation.run i.B model A

def triple {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h3 : m = 3)
    (model : RationalCostModel) (A : ℕ) : PreparedSegmentDescriptor (i.lottery hm) × ℕ := by
  subst m
  exact GeneralPaperThreeSegmentPreparation.run i.threeInput model A

def run {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A : ℕ) : PreparedSegmentDescriptor (i.lottery hm) × ℕ :=
  let header := 64 * (A + binaryWordWidth (size + 1) + 1)
  if h2 : size = 2 then
    let actual := pair i hm (hSize.symm.trans h2) model A
    (actual.1, actual.2 + header)
  else
    let h3 := hm.resolve_left (fun h => h2 (hSize.trans h))
    let actual := triple i hm h3 model A
    (actual.1, actual.2 + header)

theorem data {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A : ℕ) :
    (run i size hSize hm model A).1 = PreparedSegmentDescriptor.prepare (i.lottery hm) :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

theorem pair_work {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h2 : m = 2)
    (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) :
    (pair i hm h2 model A).2 ≤ GeneralPaperPairSegmentPreparation.bound model A s := by
  subst m
  exact GeneralPaperPairSegmentPreparation.work i.B model A s hs h.1

theorem triple_work {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h3 : m = 3)
    (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) :
    (triple i hm h3 model A).2 ≤ GeneralPaperThreeSegmentPreparation.bound model A s := by
  subst m
  exact GeneralPaperThreeSegmentPreparation.work i.threeInput model A s hs (h.three_environment hs)

def bound (model : RationalCostModel) (A s : ℕ) : ℕ :=
  GeneralPaperPairSegmentPreparation.bound model A s + GeneralPaperThreeSegmentPreparation.bound model A s + 256 * (A + 1)

theorem work {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) :
    (run i size hSize hm model A).2 ≤ bound model A s := by
  have hm3 : m ≤ 3 := by rcases hm with h | h <;> omega
  have hWord : binaryWordWidth (size + 1) ≤ 3 := by
    have h4 : binaryWordWidth 4 = 3 := by decide
    exact (binaryWordWidth_mono (by omega : size + 1 ≤ 4)).trans_eq h4
  unfold run bound
  dsimp only
  split
  · rename_i h2
    have hp := pair_work i hm (hSize.symm.trans h2) model A s hs h
    omega
  · rename_i h2
    have ht := triple_work i hm (hm.resolve_left (fun h => h2 (hSize.trans h))) model A s hs h
    omega

theorem headline (model : RationalCostModel) (A s : ℕ) :
    bound model A s ≤ 4294967296 * (model.rat (1 + 2 * expressionHeightBudget s 20) + A + 1) := by
  have hp := GeneralPaperPairSegmentPreparation.headline model A s
  have ht := GeneralPaperThreeSegmentPreparation.headline model A s
  unfold bound
  omega

end Blotto.GeneralPaperUniformSegmentPreparation

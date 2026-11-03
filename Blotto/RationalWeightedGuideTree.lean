import Blotto.WeightedProposalRejection
import Blotto.RationalSparseAttempt

/-! Rational weighted-resource families and guide trees. Their real view has
the exact retained semantic tree; no resource grid or mass normalization is
introduced. This data representation is executable, apart from proof erasure. -/

namespace Blotto
open scoped BigOperators

structure RationalWeightedFamily (n : ℕ) where
  resource : Fin n → ℚ
  mass : Fin n → ℚ
  mass_nonnegative : ∀ i, 0 ≤ mass i

namespace RationalWeightedFamily

noncomputable def real {n : ℕ} (a : RationalWeightedFamily n) : WeightedResourceFamily n :=
  ⟨fun i => (a.resource i : ℝ), fun i => (a.mass i : ℝ), by intro i; exact_mod_cast a.mass_nonnegative i⟩

def prefixMass {n : ℕ} (a : RationalWeightedFamily n) (B : ℚ) : ℚ :=
  ∑ i, if a.resource i ≤ B then a.mass i else 0

def convolution {n m : ℕ} (a : RationalWeightedFamily n) (b : RationalWeightedFamily m) (B : ℚ) : ℚ :=
  ∑ i, ∑ j, if a.resource i + b.resource j ≤ B then a.mass i * b.mass j else 0

theorem prefixMass_real {n : ℕ} (a : RationalWeightedFamily n) (B : ℚ) :
    (a.prefixMass B : ℝ) = a.real.prefixMass (B : ℝ) := by
  unfold prefixMass real WeightedResourceFamily.prefixMass
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  have he : (a.resource i : ℝ) ≤ (B : ℝ) ↔ a.resource i ≤ B := by norm_cast
  simp only [he]
  split_ifs <;> simp

theorem convolution_real {n m : ℕ} (a : RationalWeightedFamily n) (b : RationalWeightedFamily m) (B : ℚ) :
    (a.convolution b B : ℝ) = a.real.convolution b.real (B : ℝ) := by
  unfold convolution real WeightedResourceFamily.convolution
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (a.resource i : ℝ) + (b.resource j : ℝ) ≤ (B : ℝ) ↔ a.resource i + b.resource j ≤ B := by norm_cast
  simp only [he]
  split_ifs <;> simp

end RationalWeightedFamily

inductive RationalWeightedGuideTree where
  | leaf {n p : ℕ} (trueFamily : RationalWeightedFamily n) (guide : RationalWeightedFamily p) (gamma : ℚ)
  | fork {p : ℕ} (guide : RationalWeightedFamily p) (gamma : ℚ) (left right : RationalWeightedGuideTree)

namespace RationalWeightedGuideTree

noncomputable def real : RationalWeightedGuideTree → WeightedGuideTree
  | .leaf family guide gamma => .leaf family.real guide.real gamma
  | .fork guide gamma left right => .fork guide.real gamma left.real right.real

def trueSize : RationalWeightedGuideTree → ℕ
  | .leaf (n := n) _ _ _ => n
  | .fork _ _ left right => left.trueSize * right.trueSize

def guideSize : RationalWeightedGuideTree → ℕ
  | .leaf (p := p) _ _ _ => p
  | .fork (p := p) _ _ _ _ => p

theorem real_trueSize (tree : RationalWeightedGuideTree) : tree.real.trueSize = tree.trueSize := by
  induction tree with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR => simp only [real, WeightedGuideTree.trueSize, trueSize, ihL, ihR]

theorem real_guideSize (tree : RationalWeightedGuideTree) : tree.real.guideSize = tree.guideSize := by
  cases tree <;> rfl

def Record : RationalWeightedGuideTree → Type
  | .leaf (n := n) _ _ _ => Fin n
  | .fork _ _ left right => Fin left.guideSize × right.Record × left.Record

noncomputable def recordReal : (tree : RationalWeightedGuideTree) → tree.Record → tree.real.ProposalRecord
  | .leaf _ _ _, record => record
  | .fork _ _ left right, record => (record.1.cast left.real_guideSize.symm,
      right.recordReal record.2.1, left.recordReal record.2.2)

def output : (tree : RationalWeightedGuideTree) → tree.Record → Fin tree.trueSize
  | .leaf _ _ _, record => record
  | .fork _ _ left right, record => finProdFinEquiv (left.output record.2.2, right.output record.2.1)

def resource : (tree : RationalWeightedGuideTree) → tree.Record → ℚ
  | .leaf family _ _, record => family.resource record
  | .fork _ _ left right, record => left.resource record.2.2 + right.resource record.2.1

def weight : (tree : RationalWeightedGuideTree) → tree.Record → ℚ
  | .leaf family _ _, record => family.mass record
  | .fork _ _ left right, record => left.weight record.2.2 * right.weight record.2.1

def factor : RationalWeightedGuideTree → ℚ
  | .leaf _ _ gamma => gamma
  | .fork _ gamma left right => left.factor * right.factor * gamma

def guide : (tree : RationalWeightedGuideTree) → RationalWeightedFamily tree.guideSize
  | .leaf _ guide _ => guide
  | .fork guide _ _ _ => guide

def guidePrefix (tree : RationalWeightedGuideTree) (B : ℚ) : ℚ := tree.guide.prefixMass B

def syntheticMass : RationalWeightedGuideTree → ℚ → ℚ
  | .leaf family _ _, B => family.prefixMass B
  | .fork _ _ left right, B => left.guide.convolution right.guide B

def probability : (tree : RationalWeightedGuideTree) → ℚ → tree.Record → ℚ
  | .leaf family _ _, B, record =>
      if family.resource record ≤ B then family.mass record / family.prefixMass B else 0
  | .fork _ _ left right, B, record =>
      (left.guide.mass record.1 * right.guidePrefix (B - left.guide.resource record.1) /
        left.guide.convolution right.guide B) *
      right.probability (B - left.guide.resource record.1) record.2.1 *
      left.probability (B - right.resource record.2.1) record.2.2

def importance : (tree : RationalWeightedGuideTree) → ℚ → tree.Record → ℚ
  | .leaf family _ _, B, _ => family.prefixMass B
  | .fork _ _ left right, B, record =>
      left.guide.convolution right.guide B *
        left.importance (B - right.resource record.2.1) record.2.2 *
        right.importance (B - left.guide.resource record.1) record.2.1 /
          (left.guidePrefix (B - right.resource record.2.1) *
            right.guidePrefix (B - left.guide.resource record.1))

def auxiliary : (tree : RationalWeightedGuideTree) → ℚ → tree.Record → ℚ
  | .leaf family _ _, B, record => if family.resource record ≤ B then 1 else 0
  | .fork _ _ left right, B, record =>
      (if left.guide.resource record.1 ≤ B - right.resource record.2.1 then
        left.guide.mass record.1 / left.guidePrefix (B - right.resource record.2.1) else 0) *
      right.auxiliary (B - left.guide.resource record.1) record.2.1 *
      left.auxiliary (B - right.resource record.2.1) record.2.2

def nodes : RationalWeightedGuideTree → ℕ
  | .leaf _ _ _ => 1
  | .fork _ _ left right => 1 + left.nodes + right.nodes

def recordEvaluationVisits : (tree : RationalWeightedGuideTree) → tree.Record → ℕ
  | .leaf _ _ _, _ => 1
  | .fork _ _ left right, record => 1 + right.recordEvaluationVisits record.2.1 + left.recordEvaluationVisits record.2.2

theorem recordEvaluationVisits_eq (tree : RationalWeightedGuideTree) (record : tree.Record) :
    tree.recordEvaluationVisits record = tree.nodes := by
  induction tree with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    simp only [recordEvaluationVisits, nodes, ihL, ihR]
    omega

end RationalWeightedGuideTree
end Blotto

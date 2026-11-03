import Blotto.FareyDirectBlockHistory
import Blotto.ImplicitLeafProposalInterface

/-! Native leaf preparation/sampling accepts exact weak and strict callbacks.
The concrete Farey constructor derives them from direct quotient inversion.
Sampling calls the stored direct cap before the block/offset sampler; old
conditional laws are retained by a proved pointwise execution equality. -/

namespace Blotto.ImplicitLeafCounts
open Farey

structure LeafAccess (leaf : ProposalLeaf) where
  weak : ℚ → ℕ
  strict : ℚ → ℕ
  weak_eq : ∀ budget, weak budget = (MonotoneResourceCuts.weak leaf.cap leaf.decode budget).1
  strict_eq : ∀ budget, strict budget = (MonotoneResourceCuts.strict leaf.cap leaf.decode budget).1

namespace LeafAccess

def cap {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) : ℤ := access.strict budget - (1 : ℤ)

theorem cap_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) :
    access.cap budget = MonotoneResourceCuts.cap leaf.cap leaf.decode budget := by
  unfold cap MonotoneResourceCuts.cap
  rw [access.strict_eq]

def sample {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (leaf.bitBudget K attempts) → Bool) : Option (Fin (leaf.cap + 1)) :=
  if hFirst : leaf.decode 0 ≤ budget then
    some (prefixSample leaf.cap leaf.blocks leaf.partition leaf.positive (access.cap budget)
      (by rw [access.cap_eq]; exact resourceCap_nonnegative leaf.cap leaf.decode leaf.monotone budget hFirst) K attempts bits)
  else none

theorem sample_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (leaf.bitBudget K attempts) → Bool) : access.sample budget K attempts bits = leaf.sample budget K attempts bits := by
  unfold sample ProposalLeaf.sample resourceSample
  split_ifs <;> simp only [access.cap_eq]

theorem sample_some_contract {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (leaf.bitBudget K attempts) → Bool) (label : Fin (leaf.cap + 1))
    (h : access.sample budget K attempts bits = some label) :
    leaf.family.resource label ≤ budget ∧ 0 < leaf.family.mass label := by
  rw [access.sample_eq] at h
  exact leaf.sample_some_contract budget K attempts bits label h

theorem sample_none_iff {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (leaf.bitBudget K attempts) → Bool) :
    access.sample budget K attempts bits = none ↔ leaf.family.prefixMass budget = 0 := by
  rw [access.sample_eq]
  exact leaf.sample_none_iff budget K attempts bits

theorem sample_mean_error {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) (K attempts : ℕ)
    (test : Option (Fin (leaf.cap + 1)) → ℝ) (hTest : ∀ outcome, 0 ≤ test outcome ∧ test outcome ≤ 1) :
    |(fairBitKernel (leaf.bitBudget K attempts)).mean (fun bits => test (access.sample budget K attempts bits)) -
      (leaf.idealKernel budget).mean test| ≤ 1 / (2 : ℝ) ^ K + 1 / (2 : ℝ) ^ attempts := by
  simp_rw [access.sample_eq]
  exact leaf.actualKernel_close budget K attempts test hTest

end LeafAccess

def fareyLeaf (spec : RankUniverse) (scale : ℚ) (hs : 0 ≤ scale) (blocks : List Block)
    (hp : Partition (rankCap spec.order) blocks) (hw : Positive blocks) : ProposalLeaf where
  cap := rankCap spec.order
  blocks := blocks
  partition := hp
  positive := hw
  decode := FareyDirectBlockHistory.decode spec scale
  monotone := FareyDirectBlockHistory.decode_ordered spec scale hs

def fareyLeafAccess (spec : RankUniverse) (scale : ℚ) (hs : 0 ≤ scale) (blocks : List Block)
    (hp : Partition (rankCap spec.order) blocks) (hw : Positive blocks) : LeafAccess (fareyLeaf spec scale hs blocks hp hw) where
  weak := fun budget => (FareyDirectBlockHistory.first spec scale false budget).1
  strict := fun budget => (FareyDirectBlockHistory.first spec scale true budget).1
  weak_eq := fun budget => FareyDirectBlockHistory.first_eq_binary spec scale hs false budget
  strict_eq := fun budget => FareyDirectBlockHistory.first_eq_binary spec scale hs true budget

theorem fareyLeafAccess_queries (spec : RankUniverse) (scale budget : ℚ) (strict : Bool) :
    (FareyDirectBlockHistory.first spec scale strict budget).2 ≤ 12 * binaryWordWidth spec.order + 3 :=
  FareyDirectBlockHistory.first_queries spec scale strict budget

end Blotto.ImplicitLeafCounts

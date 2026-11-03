import Blotto.RationalRecursiveProposalSampler

/-! Fixed per-node fair-bit blocks flatten into one finite seed. Block lengths
come from local categorical caps; out-of-range reader queries are false. This
is input layout/semantic refinement, not yet the full independent-block law. -/

namespace Blotto
namespace RationalWeightedGuideTree

def seedWidths : RationalWeightedGuideTree → ℕ → List ℕ
  | .leaf (n := n) _ _ _, K => [3 * (n - 1 + K)]
  | .fork _ _ left right, K =>
      [3 * (left.guideSize - 1 + K)] ++ right.seedWidths K ++ left.seedWidths K

theorem seedWidths_length (tree : RationalWeightedGuideTree) (K : ℕ) :
    (tree.seedWidths K).length = tree.nodes := by
  induction tree with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR => simp [seedWidths, nodes, ihL, ihR, Nat.add_comm, Nat.add_assoc]

theorem seedWidths_sum (tree : RationalWeightedGuideTree) (K : ℕ) :
    (tree.seedWidths K).sum = tree.totalBitBudget K := by
  induction tree with
  | leaf family guide gamma => simp [seedWidths, totalBitBudget]
  | fork guide gamma left right ihL ihR => simp [seedWidths, totalBitBudget, List.sum_append, ihL, ihR, Nat.add_assoc]

def blockOffset (widths : List ℕ) (node : ℕ) : ℕ := (widths.take node).sum

def readSeedBlock (widths : List ℕ) (bits : Fin widths.sum → Bool) (node pos : ℕ) : Bool :=
  if hn : node < widths.length then
    if hp : pos < widths[node] then
      let address := blockOffset widths node + pos
      if ha : address < widths.sum then bits ⟨address, ha⟩ else false
    else false
  else false

theorem blockAddress_bound (widths : List ℕ) (node pos : ℕ)
    (hn : node < widths.length) (hp : pos < widths[node]) :
    blockOffset widths node + pos < widths.sum := by
  induction widths generalizing node with
  | nil => simp at hn
  | cons width rest ih =>
    cases node with
    | zero =>
      simp only [blockOffset, List.take_zero, List.sum_nil, zero_add, List.getElem_cons_zero] at hp ⊢
      simp only [List.sum_cons]
      omega
    | succ node =>
      have hn' : node < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hn
      have hp' : pos < rest[node] := by simpa only [List.getElem_cons_succ] using hp
      have he := ih node hn' hp'
      simp only [blockOffset, List.take_succ_cons, List.sum_cons]
      unfold blockOffset at he
      omega

theorem readSeedBlock_eq (widths : List ℕ) (bits : Fin widths.sum → Bool) (node pos : ℕ)
    (hn : node < widths.length) (hp : pos < widths[node]) :
    readSeedBlock widths bits node pos = bits ⟨blockOffset widths node + pos, blockAddress_bound widths node pos hn hp⟩ := by
  unfold readSeedBlock
  rw [dite_eq_left hn, dite_eq_left hp]
  dsimp only
  rw [dite_eq_left (blockAddress_bound widths node pos hn hp)]

def sampleFinite (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (bits : Fin (tree.totalBitBudget K) → Bool) : Option tree.Record :=
  let widths := tree.seedWidths K
  let seed : Fin widths.sum → Bool := fun j => bits (j.cast (tree.seedWidths_sum K))
  tree.sampleRecord B K (readSeedBlock widths seed)

theorem sampleFinite_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (K : ℕ) (bits : Fin (tree.totalBitBudget K) → Bool) (record : tree.Record)
    (h : tree.sampleFinite B K bits = some record) : tree.resource record ≤ B :=
  tree.sampleRecord_feasible hc B K _ record h

theorem sampleFinite_positive (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (K : ℕ) (bits : Fin (tree.totalBitBudget K) → Bool) (record : tree.Record)
    (h : tree.sampleFinite B K bits = some record) : 0 < tree.probability B record :=
  tree.sampleRecord_positive hc B K _ record h

end RationalWeightedGuideTree
end Blotto

import Blotto.ImplicitLeafCounts
import Blotto.SparseMWStoredRounding

/-! Native sparse expanded leaf updates split only stored intervals at the two
signed loss boundaries. Labels below the weak boundary lose one, the complete
equality interval loses one half, and labels at/above the strict boundary lose
zero. Boundary correctness for actual decoded rational bids remains separate. -/

namespace Blotto
open scoped Classical
namespace ImplicitLeafCounts

def splitAt (cut : ℤ) : List Block → List Block
  | [] => []
  | block :: rest =>
    if (block.lo : ℤ) < cut ∧ cut ≤ (block.hi : ℤ) then
      ⟨block.lo, cut.toNat - 1, block.weight⟩ :: ⟨cut.toNat, block.hi, block.weight⟩ :: rest
    else block :: splitAt cut rest

def splitVisits (cut : ℤ) : List Block → ℕ
  | [] => 0
  | block :: rest =>
    if (block.lo : ℤ) < cut ∧ cut ≤ (block.hi : ℤ) then 1 else splitVisits cut rest + 1

def regionLoss (weak strict : ℤ) (code : ℕ) : ℚ :=
  if (code : ℤ) < weak then 1 else if (code : ℤ) < strict then 1 / 2 else 0

def aligned (cut : ℤ) (block : Block) : Prop :=
  cut ≤ (block.lo : ℤ) ∨ (block.hi : ℤ) < cut

def updateBlocks (weak strict : ℤ) (eta theta : ℚ) (blocks : List Block) : List Block :=
  (splitAt strict (splitAt weak blocks)).map (fun block =>
    ⟨block.lo, block.hi, SparseMW.storedUpdate block.weight eta (regionLoss weak strict block.lo) theta⟩)

def updateVisits (weak strict : ℤ) (blocks : List Block) : ℕ :=
  splitVisits weak blocks + splitVisits strict (splitAt weak blocks) + (splitAt strict (splitAt weak blocks)).length

theorem splitVisits_bound (cut : ℤ) (blocks : List Block) : splitVisits cut blocks ≤ blocks.length := by
  induction blocks with
  | nil => exact le_rfl
  | cons block rest ih =>
    unfold splitVisits
    split
    · simp
    · simpa only [List.length_cons] using Nat.add_le_add_right ih 1

theorem splitAt_length_bound (cut : ℤ) (blocks : List Block) : (splitAt cut blocks).length ≤ blocks.length + 1 := by
  induction blocks with
  | nil => simp [splitAt]
  | cons block rest ih =>
    unfold splitAt
    split
    · simp
    · simp only [List.length_cons]
      omega

theorem splitAt_positive (cut : ℤ) (blocks : List Block) (h : Positive blocks) : Positive (splitAt cut blocks) := by
  induction blocks with
  | nil => simp [Positive, splitAt]
  | cons block rest ih =>
    unfold splitAt
    split
    · intro atom ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · exact h block (by simp)
      · exact h block (by simp)
      · exact h atom (by simp [ha])
    · intro atom ha
      rcases List.mem_cons.mp ha with he | ha
      · subst atom
        exact h block (by simp)
      · exact ih (fun atom ha => h atom (by simp [ha])) atom ha

theorem splitAt_coversFrom (C next : ℕ) (cut : ℤ) (blocks : List Block)
    (h : CoversFrom C next blocks) : CoversFrom C next (splitAt cut blocks) := by
  induction blocks generalizing next with
  | nil => exact h
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    unfold splitAt
    split
    · rename_i hc
      simp only [CoversFrom]
      exact ⟨h.1, by omega, by omega, by omega, h.2.2⟩
    · exact ⟨h.1, h.2.1, ih _ h.2.2⟩

theorem splitAt_labelMass (cut : ℤ) (blocks : List Block) (code : ℕ) :
    labelMass (splitAt cut blocks) code = labelMass blocks code := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    unfold splitAt
    split
    · rename_i hc
      simp only [labelMass]
      simp only [contains, decide_eq_true_eq]
      split_ifs <;> first | omega | simp
    · simp only [labelMass, ih]

theorem splitAt_aligned (C next : ℕ) (cut : ℤ) (blocks : List Block)
    (h : CoversFrom C next blocks) : ∀ block ∈ splitAt cut blocks, aligned cut block := by
  induction blocks generalizing next with
  | nil => simp [splitAt]
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    unfold splitAt
    split
    · rename_i hc
      intro atom ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · unfold aligned
        dsimp only [Block.lo, Block.hi]
        right
        omega
      · unfold aligned
        dsimp only [Block.lo, Block.hi]
        left
        omega
      · have hb := coversFrom_bounds C (block.hi + 1) rest h.2.2 atom ha
        unfold aligned
        left
        omega
    · rename_i hc
      intro atom ha
      rcases List.mem_cons.mp ha with rfl | ha
      · unfold aligned
        omega
      · exact ih _ h.2.2 atom ha

theorem splitAt_preserves_aligned (first cut : ℤ) (blocks : List Block)
    (h : ∀ block ∈ blocks, aligned first block) : ∀ block ∈ splitAt cut blocks, aligned first block := by
  induction blocks with
  | nil => simp [splitAt]
  | cons block rest ih =>
    have hb := h block (by simp)
    unfold splitAt
    split
    · rename_i hc
      intro atom ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · unfold aligned at hb ⊢
        dsimp only [Block.lo, Block.hi]
        omega
      · unfold aligned at hb ⊢
        dsimp only [Block.lo, Block.hi]
        omega
      · exact h atom (by simp [ha])
    · intro atom ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hb
      · exact ih (fun atom ha => h atom (by simp [ha])) atom ha

theorem regionLoss_unit (weak strict : ℤ) (code : ℕ) :
    0 ≤ regionLoss weak strict code ∧ regionLoss weak strict code ≤ 1 := by
  unfold regionLoss
  split_ifs <;> norm_num

theorem regionLoss_block_constant (weak strict : ℤ) (block : Block) (code : ℕ)
    (hc : contains block code = true) (hw : aligned weak block) (hs : aligned strict block) :
    regionLoss weak strict block.lo = regionLoss weak strict code := by
  have hBounds : block.lo ≤ code ∧ code ≤ block.hi := by simpa only [contains, decide_eq_true_eq] using hc
  unfold aligned at hw hs
  unfold regionLoss
  split_ifs <;> first | omega | rfl

theorem coversFrom_map_weights (C next : ℕ) (blocks : List Block) (f : Block → ℚ)
    (h : CoversFrom C next blocks) :
    CoversFrom C next (blocks.map (fun block => (⟨block.lo, block.hi, f block⟩ : Block))) := by
  induction blocks generalizing next with
  | nil => exact h
  | cons block rest ih => exact ⟨h.1, h.2.1, ih _ h.2.2⟩

theorem labelMass_map_unique (C next : ℕ) (blocks : List Block) (f : Block → ℚ)
    (h : CoversFrom C next blocks) (code : ℕ) (hc : next ≤ code ∧ code ≤ C)
    (g : ℚ → ℚ) (hf : ∀ block ∈ blocks, contains block code = true → f block = g block.weight) :
    labelMass (blocks.map (fun block => (⟨block.lo, block.hi, f block⟩ : Block))) code = g (labelMass blocks code) := by
  induction blocks generalizing next with
  | nil => simp only [CoversFrom] at h; omega
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    by_cases hi : code ≤ block.hi
    · have hIn : contains block code = true := by simp only [contains, decide_eq_true_eq]; omega
      have hOut : contains (⟨block.lo, block.hi, f block⟩ : Block) code = true := hIn
      simp only [List.map_cons, labelMass, hIn, hOut, ite_true]
      rw [coversFrom_below C (block.hi + 1) rest h.2.2 code (by omega),
        coversFrom_below C (block.hi + 1) _ (coversFrom_map_weights C _ rest f h.2.2) code (by omega)]
      simp only [add_zero]
      exact hf block (by simp) hIn
    · have hMiss : contains block code = false := by simp only [contains, decide_eq_false_iff_not]; omega
      have hOut : contains (⟨block.lo, block.hi, f block⟩ : Block) code = false := hMiss
      simp only [List.map_cons, labelMass, hMiss, hOut, Bool.false_eq_true, ite_false, zero_add]
      exact ih (block.hi + 1) h.2.2 ⟨by omega, hc.2⟩ (fun atom ha => hf atom (by simp [ha]))

theorem updateBlocks_partition (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (weak strict : ℤ) (eta theta : ℚ) : Partition C (updateBlocks weak strict eta theta blocks) :=
  coversFrom_map_weights C 0 _ _ (splitAt_coversFrom C 0 strict _ (splitAt_coversFrom C 0 weak blocks hp))

theorem updateBlocks_positive (blocks : List Block) (hw : Positive blocks)
    (weak strict : ℤ) (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) :
    Positive (updateBlocks weak strict eta theta blocks) := by
  intro atom ha
  rcases List.mem_map.mp ha with ⟨block, hb, rfl⟩
  have hp := splitAt_positive strict _ (splitAt_positive weak blocks hw) block hb
  have hl := regionLoss_unit weak strict block.lo
  exact SparseMW.storedUpdate_positive _ _ _ _ hp
    ⟨mul_nonneg heta.1.le hl.1, (mul_le_of_le_one_right heta.1.le hl.2).trans heta.2⟩ htheta

theorem updateBlocks_labelMass (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (weak strict : ℤ) (eta theta : ℚ) (code : Fin (C + 1)) :
    labelMass (updateBlocks weak strict eta theta blocks) code.val =
      SparseMW.storedUpdate (labelMass blocks code.val) eta (regionLoss weak strict code.val) theta := by
  have hSplit := splitAt_coversFrom C 0 strict _ (splitAt_coversFrom C 0 weak blocks hp)
  unfold updateBlocks
  rw [labelMass_map_unique C 0 _ _ hSplit code.val ⟨Nat.zero_le _, by omega⟩
    (fun old => SparseMW.storedUpdate old eta (regionLoss weak strict code.val) theta)]
  · rw [splitAt_labelMass, splitAt_labelMass]
  · intro block hb hc
    rw [regionLoss_block_constant weak strict block code.val hc]
    · exact splitAt_preserves_aligned weak strict _ (splitAt_aligned C 0 weak blocks hp) block hb
    · exact splitAt_aligned C 0 strict _ (splitAt_coversFrom C 0 weak blocks hp) block hb

theorem updateBlocks_length (blocks : List Block) (weak strict : ℤ) (eta theta : ℚ) :
    (updateBlocks weak strict eta theta blocks).length ≤ blocks.length + 2 := by
  unfold updateBlocks
  rw [List.length_map]
  have h1 := splitAt_length_bound weak blocks
  have h2 := splitAt_length_bound strict (splitAt weak blocks)
  omega

theorem updateVisits_bound (blocks : List Block) (weak strict : ℤ) :
    updateVisits weak strict blocks ≤ 3 * blocks.length + 3 := by
  unfold updateVisits
  have hv1 := splitVisits_bound weak blocks
  have hv2 := splitVisits_bound strict (splitAt weak blocks)
  have hl1 := splitAt_length_bound weak blocks
  have hl2 := splitAt_length_bound strict (splitAt weak blocks)
  omega

end ImplicitLeafCounts
end Blotto

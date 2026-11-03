import Blotto.RationalWeightedGuideTree
import Mathlib.Order.Interval.Finset.Nat

/-! Exact expanded R162 leaf weights are stored as positive contiguous code
blocks. Prefix queries visit blocks, never the numerical code universe. Finite
label sums below are semantic proofs only. Resource decoding/Farey cutoff
correctness, cached binary searches and compact R165 arithmetic remain separate. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

structure Block where
  lo : ℕ
  hi : ℕ
  weight : ℚ
  deriving DecidableEq, Repr

def clippedCount (block : Block) (cutoff : ℤ) : ℕ :=
  (min (cutoff + 1) ((block.hi : ℤ) + 1) - block.lo).toNat

def blockMass (block : Block) (cutoff : ℤ) : ℚ := (clippedCount block cutoff : ℚ) * block.weight

def prefixMass : List Block → ℤ → ℚ
  | [], _ => 0
  | block :: rest, cutoff => blockMass block cutoff + prefixMass rest cutoff

def prefixMassWithVisits : List Block → ℤ → ℚ × ℕ
  | [], _ => (0, 0)
  | block :: rest, cutoff =>
    let tail := prefixMassWithVisits rest cutoff
    (blockMass block cutoff + tail.1, tail.2 + 1)

def contains (block : Block) (code : ℕ) : Bool := decide (block.lo ≤ code ∧ code ≤ block.hi)

def labelMass : List Block → ℕ → ℚ
  | [], _ => 0
  | block :: rest, code => (if contains block code then block.weight else 0) + labelMass rest code

def totalMass (blocks : List Block) : ℚ :=
  (blocks.map (fun block => ((block.hi + 1 - block.lo : ℕ) : ℚ) * block.weight)).sum

def Nonnegative (blocks : List Block) : Prop := ∀ block ∈ blocks, 0 ≤ block.weight

def Positive (blocks : List Block) : Prop := ∀ block ∈ blocks, 0 < block.weight

def CoversFrom (C : ℕ) : ℕ → List Block → Prop
  | next, [] => next = C + 1
  | next, block :: rest => block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest

def Partition (C : ℕ) (blocks : List Block) : Prop := CoversFrom C 0 blocks

theorem prefixMassWithVisits_refines (blocks : List Block) (cutoff : ℤ) :
    prefixMassWithVisits blocks cutoff = (prefixMass blocks cutoff, blocks.length) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [prefixMassWithVisits, ih, prefixMass, List.length_cons]

theorem clippedCount_negative (block : Block) (cutoff : ℤ) (h : cutoff < 0) : clippedCount block cutoff = 0 := by
  unfold clippedCount
  omega

theorem clippedCount_full (block : Block) (cutoff : ℤ) (h : (block.hi : ℤ) ≤ cutoff) :
    clippedCount block cutoff = block.hi + 1 - block.lo := by
  unfold clippedCount
  omega

theorem clippedCount_nat (block : Block) (cutoff : ℕ) :
    clippedCount block (cutoff : ℤ) = min cutoff block.hi + 1 - block.lo := by
  unfold clippedCount
  omega

theorem clippedCount_mono (block : Block) {first second : ℤ} (h : first ≤ second) :
    clippedCount block first ≤ clippedCount block second := by
  unfold clippedCount
  omega

theorem clippedCount_card (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C) :
    (Finset.univ.filter (fun code : Fin (C + 1) => contains block code.val ∧ (code.val : ℤ) ≤ cutoff)).card =
      clippedCount block cutoff := by
  by_cases hCut : cutoff < 0
  · have he : (Finset.univ.filter (fun code : Fin (C + 1) => contains block code.val ∧ (code.val : ℤ) ≤ cutoff)) = ∅ := by
      ext code
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      unfold contains
      omega
    rw [he, Finset.card_empty, clippedCount_negative block cutoff hCut]
  · have hNonnegative : 0 ≤ cutoff := by omega
    let upper := min cutoff.toNat block.hi
    have hMap : (Finset.univ.filter (fun code : Fin (C + 1) => contains block code.val ∧ (code.val : ℤ) ≤ cutoff)).map
        ⟨Fin.val, Fin.val_injective⟩ = Finset.Icc block.lo upper := by
      ext code
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
      constructor
      · rintro ⟨label, ⟨hBlock, hCutoff⟩, rfl⟩
        dsimp only [upper]
        have hBlock' : block.lo ≤ label.val ∧ label.val ≤ block.hi := by simpa only [contains, decide_eq_true_eq] using hBlock
        change block.lo ≤ label.val ∧ label.val ≤ min cutoff.toNat block.hi
        omega
      · intro hInterval
        have hCode : code < C + 1 := by dsimp only [upper] at hInterval; omega
        refine ⟨⟨code, hCode⟩, ?_, rfl⟩
        dsimp only [upper] at hInterval
        simp only [contains, decide_eq_true_eq]
        omega
    have he := congrArg Finset.card hMap
    rw [Finset.card_map, Nat.card_Icc] at he
    rw [he]
    unfold clippedCount
    dsimp only [upper]
    omega

theorem blockMass_labels (C : ℕ) (block : Block) (cutoff : ℤ) (hHi : block.hi ≤ C) :
    blockMass block cutoff = ∑ code : Fin (C + 1),
      if contains block code.val ∧ (code.val : ℤ) ≤ cutoff then block.weight else 0 := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [clippedCount_card C block cutoff hHi]
  rfl

theorem prefixMass_labels (C : ℕ) (blocks : List Block) (cutoff : ℤ)
    (hBounds : ∀ block ∈ blocks, block.hi ≤ C) :
    prefixMass blocks cutoff = ∑ code : Fin (C + 1),
      if (code.val : ℤ) ≤ cutoff then labelMass blocks code.val else 0 := by
  induction blocks with
  | nil => simp [prefixMass, labelMass]
  | cons block rest ih =>
    rw [prefixMass, blockMass_labels C block cutoff (hBounds block (by simp)),
      ih (fun atom ha => hBounds atom (by simp [ha]))]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro code _
    simp only [labelMass]
    split_ifs <;> simp_all

theorem blockMass_nonnegative (block : Block) (cutoff : ℤ) (h : 0 ≤ block.weight) : 0 ≤ blockMass block cutoff :=
  mul_nonneg (by positivity) h

theorem prefixMass_nonnegative (blocks : List Block) (cutoff : ℤ) (h : Nonnegative blocks) :
    0 ≤ prefixMass blocks cutoff := by
  induction blocks with
  | nil => exact le_rfl
  | cons block rest ih =>
    exact add_nonneg (blockMass_nonnegative block cutoff (h block (by simp)))
      (ih (fun atom ha => h atom (by simp [ha])))

theorem prefixMass_negative (blocks : List Block) (cutoff : ℤ) (h : cutoff < 0) : prefixMass blocks cutoff = 0 := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp [prefixMass, blockMass, clippedCount_negative block cutoff h, ih]

theorem prefixMass_full (blocks : List Block) (cutoff : ℤ)
    (h : ∀ block ∈ blocks, (block.hi : ℤ) ≤ cutoff) : prefixMass blocks cutoff = totalMass blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    simp only [prefixMass, totalMass, List.map_cons, List.sum_cons, blockMass,
      clippedCount_full block cutoff (h block (by simp))]
    exact congrArg (fun tail => ((block.hi + 1 - block.lo : ℕ) : ℚ) * block.weight + tail)
      (ih (fun atom ha => h atom (by simp [ha])))

theorem labelMass_nonnegative (blocks : List Block) (code : ℕ) (h : Nonnegative blocks) :
    0 ≤ labelMass blocks code := by
  induction blocks with
  | nil => exact le_rfl
  | cons block rest ih =>
    apply add_nonneg
    · split_ifs
      · exact h block (by simp)
      · exact le_rfl
    · exact ih (fun atom ha => h atom (by simp [ha]))

def family (C : ℕ) (blocks : List Block) (h : Nonnegative blocks) : RationalWeightedFamily (C + 1) where
  resource := fun code => code.val
  mass := fun code => labelMass blocks code.val
  mass_nonnegative := fun code => labelMass_nonnegative blocks code.val h

theorem family_prefixMass (C : ℕ) (blocks : List Block) (h : Nonnegative blocks) (cutoff : ℤ)
    (hBounds : ∀ block ∈ blocks, block.hi ≤ C) :
    (family C blocks h).prefixMass (cutoff : ℚ) = prefixMass blocks cutoff := by
  rw [prefixMass_labels C blocks cutoff hBounds]
  unfold RationalWeightedFamily.prefixMass family
  apply Finset.sum_congr rfl
  intro code _
  have he : (code.val : ℚ) ≤ (cutoff : ℚ) ↔ (code.val : ℤ) ≤ cutoff := by exact_mod_cast Iff.rfl
  simp only [he]

theorem coversFrom_start_bound (C next : ℕ) (blocks : List Block) (h : CoversFrom C next blocks) : next ≤ C + 1 := by
  induction blocks generalizing next with
  | nil => exact le_of_eq h
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    have ht := ih (block.hi + 1) h.2.2
    omega

theorem coversFrom_bounds (C next : ℕ) (blocks : List Block) (h : CoversFrom C next blocks) :
    ∀ block ∈ blocks, next ≤ block.lo ∧ block.lo ≤ block.hi ∧ block.hi ≤ C := by
  induction blocks generalizing next with
  | nil => simp
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    have ht := coversFrom_start_bound C (block.hi + 1) rest h.2.2
    intro atom ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨by omega, h.2.1, by omega⟩
    · have he := ih (block.hi + 1) h.2.2 atom ha
      exact ⟨by omega, he.2⟩

theorem coversFrom_below (C next : ℕ) (blocks : List Block) (h : CoversFrom C next blocks)
    (code : ℕ) (hCode : code < next) : labelMass blocks code = 0 := by
  induction blocks generalizing next with
  | nil => rfl
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    have hMiss : contains block code = false := by simp only [contains, decide_eq_false_iff_not]; omega
    simp only [labelMass, hMiss, Bool.false_eq_true, ite_false, zero_add]
    exact ih (block.hi + 1) h.2.2 (by omega)

theorem coversFrom_unique_weight (C next : ℕ) (blocks : List Block) (h : CoversFrom C next blocks)
    (code : ℕ) (hCode : next ≤ code ∧ code ≤ C) :
    ∃ block ∈ blocks, contains block code = true ∧ labelMass blocks code = block.weight := by
  induction blocks generalizing next with
  | nil => simp only [CoversFrom] at h; omega
  | cons block rest ih =>
    change block.lo = next ∧ block.lo ≤ block.hi ∧ CoversFrom C (block.hi + 1) rest at h
    by_cases hi : code ≤ block.hi
    · have hIn : contains block code = true := by simp only [contains, decide_eq_true_eq]; omega
      refine ⟨block, by simp, hIn, ?_⟩
      simp only [labelMass, hIn, ite_true]
      rw [coversFrom_below C (block.hi + 1) rest h.2.2 code (by omega), add_zero]
    · have hMiss : contains block code = false := by simp only [contains, decide_eq_false_iff_not]; omega
      rcases ih (block.hi + 1) h.2.2 ⟨by omega, hCode.2⟩ with ⟨atom, ha, hin, hw⟩
      refine ⟨atom, by simp [ha], hin, ?_⟩
      simp only [labelMass, hMiss, Bool.false_eq_true, ite_false, zero_add, hw]

theorem partition_labelMass_positive (C : ℕ) (blocks : List Block) (h : Partition C blocks)
    (hw : Positive blocks) (code : Fin (C + 1)) : 0 < labelMass blocks code.val := by
  rcases coversFrom_unique_weight C 0 blocks h code.val ⟨Nat.zero_le _, by omega⟩ with ⟨block, hb, _, he⟩
  rw [he]
  exact hw block hb

theorem partition_prefixMass_labels (C : ℕ) (blocks : List Block) (h : Partition C blocks) (cutoff : ℤ) :
    prefixMass blocks cutoff = ∑ code : Fin (C + 1),
      if (code.val : ℤ) ≤ cutoff then labelMass blocks code.val else 0 :=
  prefixMass_labels C blocks cutoff (fun block hb => (coversFrom_bounds C 0 blocks h block hb).2.2)

theorem partition_prefixMass_full (C : ℕ) (blocks : List Block) (h : Partition C blocks) (cutoff : ℤ)
    (hc : (C : ℤ) ≤ cutoff) : prefixMass blocks cutoff = totalMass blocks :=
  prefixMass_full blocks cutoff (fun block hb => by
    have he := (coversFrom_bounds C 0 blocks h block hb).2.2
    omega)

theorem partition_prefixMass_positive (C : ℕ) (blocks : List Block) (h : Partition C blocks)
    (hw : Positive blocks) (cutoff : ℤ) (hc : 0 ≤ cutoff) : 0 < prefixMass blocks cutoff := by
  rw [partition_prefixMass_labels C blocks h]
  have hNonnegative : Nonnegative blocks := fun block hb => (hw block hb).le
  apply Finset.sum_pos'
  · intro code _
    split_ifs
    · exact labelMass_nonnegative blocks code.val hNonnegative
    · exact le_rfl
  · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [Nat.cast_zero, hc, ite_true]
    exact partition_labelMass_positive C blocks h hw ⟨0, by omega⟩

theorem prefixMass_mono (blocks : List Block) (h : Nonnegative blocks) {first second : ℤ} (hs : first ≤ second) :
    prefixMass blocks first ≤ prefixMass blocks second := by
  induction blocks with
  | nil => exact le_rfl
  | cons block rest ih =>
    apply add_le_add
    · unfold blockMass
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast clippedCount_mono block hs) (h block (by simp))
    · exact ih (fun atom ha => h atom (by simp [ha]))

end ImplicitLeafCounts
end Blotto

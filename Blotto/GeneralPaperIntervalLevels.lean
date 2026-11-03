import Blotto.GeneralPaperIntervalUpdateWork

/-! Exact code-level meaning of the sparse traversal. Rational midpoint
arithmetic agrees with the integer dyadic code grid, so a singleton cannot
partially overlap an update with integer endpoints. Cache values never enter
the exact level semantics.
-/
namespace Blotto.GeneralPaperIntervalLevels
open GeneralPaperIntervalCache GeneralPaperIntervalGeometry GeneralPaperIntervalUpdate GeneralPaperPreparedPowers
set_option autoImplicit false
set_option maxHeartbeats 3000000

def leftChild {height : ℕ} : Node (height+1) → Node height
  | .uniform _ _ => .uniform height 0
  | .branch _ _ left _ => left

def rightChild {height : ℕ} : Node (height+1) → Node height
  | .uniform _ _ => .uniform height 0
  | .branch _ _ _ right => right

def levelAt : {height : ℕ} → Node height → ℕ → ℕ
  | _,.uniform _ level,_ => level
  | height+1,.branch level _ left right,index =>
    level+(if index<2^height then levelAt left index else levelAt right (index-2^height))

theorem split_level {height : ℕ} (node : Node (height+1)) (index : ℕ) :
    levelAt node index=offset node+
      (if index<2^height then levelAt (leftChild node) index else levelAt (rightChild node) (index-2^height)) := by
  cases node with
  | uniform h level => simp only [levelAt,offset,leftChild,rightChild]; split <;> omega
  | branch level cached left right => rfl

theorem rebuilt_level {height : ℕ} (prepared : Prepared) (level : ℕ) (left right : Node height) (index : ℕ) :
    levelAt (rebuild prepared level left right) index=
      level+(if index<2^height then levelAt left index else levelAt right (index-2^height)) := rfl

theorem raised_level {height : ℕ} (amount : ℕ) (node : Node height) (index : ℕ) :
    levelAt (raiseRoot amount node) index=levelAt node index+amount := by
  cases node <;> simp only [levelAt,raiseRoot] <;> omega

theorem expanded_level (prepared : Prepared) (height level index : ℕ) :
    levelAt (expand prepared height level) index=levelAt (.uniform (height+1) level) index := by
  simp only [expand,levelAt]
  split <;> omega

theorem offset_le_level {height : ℕ} (node : Node height) (index : ℕ) : offset node≤levelAt node index := by
  cases node with
  | uniform height level => exact le_refl _
  | branch level cached left right => dsimp only [offset,levelAt]; omega

theorem partial_node (prepared : Prepared) (lo hi : ℚ) (amount height : ℕ) (node : Node (height+1)) (start span : ℚ)
    (hD : ¬GeneralPaperIntervalGeometry.Disjoint start span lo hi) (hC : ¬Covered start span lo hi) :
    (run prepared lo hi amount (height+1) node start span).node=
      rebuild prepared (offset node)
        (run prepared lo hi amount height (leftChild node) start (span/2)).node
        (run prepared lo hi amount height (rightChild node) (start+span/2) (span/2)).node := by
  rw [run.eq_def,if_neg hD,if_neg hC]
  cases node <;> rfl

theorem disjoint_grid (height start lo hi : ℕ) :
    GeneralPaperIntervalGeometry.Disjoint (start:ℚ) ((2:ℚ)^height) lo hi ↔ hi≤start ∨ start+2^height≤lo := by
  unfold GeneralPaperIntervalGeometry.Disjoint
  norm_cast

theorem covered_grid (height start lo hi : ℕ) :
    Covered (start:ℚ) ((2:ℚ)^height) lo hi ↔ lo≤start ∧ start+2^height≤hi := by
  unfold Covered
  norm_cast

theorem update_level (prepared : Prepared) (lo hi amount height : ℕ) (node : Node height) (start index : ℕ)
    (hIndex : index<2^height) :
    levelAt (run prepared (lo:ℚ) hi amount height node (start:ℚ) ((2:ℚ)^height)).node index=
      levelAt node index+(if lo≤start+index ∧ start+index<hi then amount else 0) := by
  induction height generalizing start index with
  | zero =>
    have hI : index=0 := by simp only [pow_zero] at hIndex; omega
    subst index
    rw [run.eq_def]
    split
    · rename_i hD
      have hd := (disjoint_grid 0 start lo hi).mp hD
      have hm : ¬(lo≤start+0 ∧ start+0<hi) := by simp only [pow_zero] at hd; omega
      rw [if_neg hm]
      rfl
    · rename_i hD
      split
      · rename_i hC
        have hc := (covered_grid 0 start lo hi).mp hC
        have hm : lo≤start+0 ∧ start+0<hi := by simp only [pow_zero] at hc; omega
        rw [if_pos hm]
        exact raised_level amount node 0
      · rename_i hC
        have hd := (disjoint_grid 0 start lo hi).not.mp hD
        have hc := (covered_grid 0 start lo hi).not.mp hC
        simp only [pow_zero] at hd hc
        omega
  | succ height ih =>
    by_cases hD : GeneralPaperIntervalGeometry.Disjoint (start:ℚ) ((2:ℚ)^(height+1)) lo hi
    · rw [run.eq_def,if_pos hD]
      have hd := (disjoint_grid (height+1) start lo hi).mp hD
      have hm : ¬(lo≤start+index ∧ start+index<hi) := by omega
      rw [if_neg hm]
      rfl
    · by_cases hC : Covered (start:ℚ) ((2:ℚ)^(height+1)) lo hi
      · rw [run.eq_def,if_neg hD,if_pos hC]
        have hc := (covered_grid (height+1) start lo hi).mp hC
        have hm : lo≤start+index ∧ start+index<hi := by omega
        rw [if_pos hm]
        exact raised_level amount node index
      · rw [partial_node prepared (lo:ℚ) hi amount height node (start:ℚ) ((2:ℚ)^(height+1)) hD hC,rebuilt_level,split_level node index]
        have hHalf : (2:ℚ)^(height+1)/2=(2:ℚ)^height := by rw [pow_succ]; ring
        have hStart : (start:ℚ)+(2:ℚ)^height=((start+2^height:ℕ):ℚ) := by norm_cast
        rw [hHalf,hStart]
        by_cases hLeft : index<2^height
        · rw [if_pos hLeft,if_pos hLeft,ih (leftChild node) start index hLeft]
          omega
        · have hRight : index-2^height<2^height := by rw [pow_succ] at hIndex; omega
          rw [if_neg hLeft,if_neg hLeft,ih (rightChild node) (start+2^height) (index-2^height) hRight]
          have hPoint : start+2^height+(index-2^height)=start+index := by omega
          rw [hPoint]
          omega

theorem path_cap_implies_can_raise (cap amount height : ℕ) (node : Node height)
    (hCap : ∀ index<2^height, levelAt node index+amount≤cap) : CanRaise cap amount node := by
  induction node with
  | uniform height level =>
    have he := hCap 0 (Nat.two_pow_pos _)
    exact he
  | @branch height level cached left right ihl ihr =>
    have hz : 0<2^(height+1) := Nat.two_pow_pos _
    have hRoot := hCap 0 hz
    have hLevel := offset_le_level (.branch level cached left right) 0
    refine ⟨by change level≤_ at hLevel; omega,?_,?_⟩
    · apply ihl
      intro index hi
      have hTotal : index<2^(height+1) := by rw [pow_succ]; omega
      have he := hCap index hTotal
      simp only [levelAt,if_pos hi] at he
      omega
    · apply ihr
      intro index hi
      have hTotal : 2^height+index<2^(height+1) := by rw [pow_succ]; omega
      have he := hCap (2^height+index) hTotal
      have hNot : ¬2^height+index<2^height := by omega
      simp only [levelAt,if_neg hNot,Nat.add_sub_cancel_left] at he
      omega

end Blotto.GeneralPaperIntervalLevels

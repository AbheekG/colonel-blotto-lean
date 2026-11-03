import Blotto.GeneralPaperGlobalNodeQuery

/-! Reference code-prefix sums and the exact left/right decomposition used
by a single quantile descent. These sums are proof semantics; the algorithm
uses cached subtree masses and a running stored prefix.
-/
namespace Blotto.GeneralPaperTreePrefix
open scoped BigOperators Classical
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalMass
open GeneralPaperCachedMassJoin GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 2500000

def prefixWeights (b : ℚ) {height : ℕ} (node : Node height) (count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, b^levelAt node i

def weightedPrefix (k ancestor : ℕ) {height : ℕ} (node : Node height) (count : ℕ) : ℚ :=
  base k^ancestor*prefixWeights (base k) node count

theorem prefix_zero (b : ℚ) {height : ℕ} (node : Node height) : prefixWeights b node 0=0 := by simp [prefixWeights]

theorem prefix_total (b : ℚ) {height : ℕ} (node : Node height) : prefixWeights b node (2^height)=globalMass b node :=
  global_mass_sum b node

theorem prefix_nonnegative (b : ℚ) (hb : 0≤b) {height : ℕ} (node : Node height) (count : ℕ) :
    0≤prefixWeights b node count := Finset.sum_nonneg (fun _ _ => pow_nonneg hb _)

theorem prefix_monotone (b : ℚ) (hb : 0≤b) {height : ℕ} (node : Node height)
    (small large : ℕ) (hOrder : small≤large) : prefixWeights b node small≤prefixWeights b node large := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hOrder)
  intro i _ _
  exact pow_nonneg hb _

theorem prefix_bounds (b : ℚ) (hb : 0≤b) {height : ℕ} (node : Node height) (count : ℕ) (hCount : count≤2^height) :
    0≤prefixWeights b node count ∧ prefixWeights b node count≤globalMass b node := by
  exact ⟨prefix_nonnegative b hb node count,(prefix_monotone b hb node _ _ hCount).trans_eq (prefix_total b node)⟩

theorem uniform_prefix (b : ℚ) (height level count : ℕ) :
    prefixWeights b (.uniform height level) count=(count:ℚ)*b^level := by
  simp only [prefixWeights,levelAt,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem left_prefix (b : ℚ) {height : ℕ} (node : Node (height+1)) (count : ℕ) (hCount : count≤2^height) :
    prefixWeights b node count=b^offset node*prefixWeights b (leftChild node) count := by
  unfold prefixWeights
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hI : i<2^height := (Finset.mem_range.mp hi).trans_le hCount
  rw [split_level node i,if_pos hI,pow_add]

theorem right_prefix (b : ℚ) {height : ℕ} (node : Node (height+1)) (count : ℕ) (hCount : count≤2^height) :
    prefixWeights b node (2^height+count)=b^offset node*
      (globalMass b (leftChild node)+prefixWeights b (rightChild node) count) := by
  unfold prefixWeights
  rw [Finset.sum_range_add]
  have hLeft : (∑ i ∈ Finset.range (2^height), b^levelAt node i)=
      b^offset node*globalMass b (leftChild node) := left_prefix b node (2^height) (le_refl _) |>.trans
        (by rw [prefix_total])
  have hRight : (∑ i ∈ Finset.range count, b^levelAt node (2^height+i))=
      b^offset node*(∑ i ∈ Finset.range count, b^levelAt (rightChild node) i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [split_level node (2^height+i),if_neg (by omega),Nat.add_sub_cancel_left,pow_add]
  rw [hLeft,hRight]
  ring

theorem weighted_zero (k ancestor : ℕ) {height : ℕ} (node : Node height) : weightedPrefix k ancestor node 0=0 := by
  rw [weightedPrefix,prefix_zero,mul_zero]

theorem weighted_total (k ancestor : ℕ) {height : ℕ} (node : Node height) :
    weightedPrefix k ancestor node (2^height)=trueMass k ancestor node := by rw [weightedPrefix,prefix_total]; rfl

theorem weighted_bounds (k ancestor : ℕ) {height : ℕ} (node : Node height) (count : ℕ) (hCount : count≤2^height) :
    0≤weightedPrefix k ancestor node count ∧ weightedPrefix k ancestor node count≤trueMass k ancestor node := by
  have he := prefix_bounds (base k) (base_positive k).le node count hCount
  exact ⟨mul_nonneg (pow_nonneg (base_positive k).le _) he.1,
    mul_le_mul_of_nonneg_left he.2 (pow_nonneg (base_positive k).le _)⟩

theorem weighted_left (k ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (count : ℕ) (hCount : count≤2^height) :
    weightedPrefix k ancestor node count=weightedPrefix k (ancestor+offset node) (leftChild node) count := by
  unfold weightedPrefix
  rw [left_prefix (base k) node count hCount,pow_add]
  ring

theorem weighted_right (k ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (count : ℕ) (hCount : count≤2^height) :
    weightedPrefix k ancestor node (2^height+count)=trueMass k (ancestor+offset node) (leftChild node)+
      weightedPrefix k (ancestor+offset node) (rightChild node) count := by
  unfold weightedPrefix trueMass globalMass
  rw [right_prefix (base k) node count hCount,pow_add]
  dsimp only [globalMass]
  ring

end Blotto.GeneralPaperTreePrefix

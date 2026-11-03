import Blotto.GeneralPaperIntervalLevels

/-! The cached base-mass recurrence represents the sum of the selected
geometric weights over every code of the represented interval. This joins
the structural cache theorem to the actual full-code law, without enumerating
that sum at runtime.
-/
namespace Blotto.GeneralPaperIntervalMass
open scoped BigOperators Classical
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperCachedMassJoin
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalUpdate
set_option autoImplicit false
set_option maxHeartbeats 2500000

def globalMass (b : ℚ) {height : ℕ} (node : Node height) : ℚ := b^offset node*exactMass b node

theorem global_mass_sum (b : ℚ) {height : ℕ} (node : Node height) :
    (∑ index ∈ Finset.range (2^height), b^levelAt node index)=globalMass b node := by
  induction node with
  | uniform height level =>
    simp only [levelAt,Finset.sum_const,Finset.card_range,nsmul_eq_mul,globalMass,offset,exactMass,Nat.cast_pow,Nat.cast_ofNat]
    ring
  | @branch height level cached left right ihl ihr =>
    have hSize : 2^(height+1)=2^height+2^height := by rw [pow_succ]; omega
    rw [hSize,Finset.sum_range_add]
    have hLeft : (∑ i ∈ Finset.range (2^height), b^levelAt (.branch level cached left right) i)=
        b^level*(∑ i ∈ Finset.range (2^height), b^levelAt left i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [levelAt,if_pos (Finset.mem_range.mp hi),pow_add]
    have hRight : (∑ i ∈ Finset.range (2^height), b^levelAt (.branch level cached left right) (2^height+i))=
        b^level*(∑ i ∈ Finset.range (2^height), b^levelAt right i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hNot : ¬2^height+i<2^height := by omega
      simp only [levelAt,if_neg hNot,Nat.add_sub_cancel_left,pow_add]
    rw [hLeft,hRight,ihl,ihr]
    dsimp only [globalMass,offset,exactMass]
    ring

theorem global_mass_positive (b : ℚ) (hb : 0<b) {height : ℕ} (node : Node height) : 0<globalMass b node :=
  mul_pos (pow_pos hb _) (exact_mass_positive b hb node)

theorem raised_global_mass (b : ℚ) {height : ℕ} (amount : ℕ) (node : Node height) :
    globalMass b (raiseRoot amount node)=b^amount*globalMass b node := by
  have ho : offset (raiseRoot amount node)=offset node+amount := by cases node <;> rfl
  unfold globalMass
  rw [ho,raised_exact_mass,pow_add]
  ring

theorem expanded_global_mass (b : ℚ) (prepared : Prepared) (height level : ℕ) :
    globalMass b (expand prepared height level)=globalMass b (.uniform (height+1) level) := by
  unfold globalMass
  rw [expanded_exact_mass]
  rfl

theorem updated_weight (b : ℚ) (prepared : Prepared) (lo hi amount height : ℕ) (node : Node height) (start index : ℕ)
    (hIndex : index<2^height) :
    b^levelAt (run prepared (lo:ℚ) hi amount height node (start:ℚ) ((2:ℚ)^height)).node index=
      b^levelAt node index*(if lo≤start+index ∧ start+index<hi then b^amount else 1) := by
  rw [update_level prepared lo hi amount height node start index hIndex,pow_add]
  split <;> simp

theorem rounded_root_bounds (lambda k : ℕ) {height : ℕ} (node : Node height) (hValid : Valid lambda k node) :
    retention (prepare lambda k).format.unit^((GeneralPaperPowerPrecision.levelBound lambda k+2)*height+
        GeneralPaperPowerPrecision.levelBound lambda k+1)*globalMass (base k) node≤
      value (applyOffset (prepare lambda k) (offset node) (mass (prepare lambda k) node)).number ∧
    value (applyOffset (prepare lambda k) (offset node) (mass (prepare lambda k) node)).number≤globalMass (base k) node := by
  have hc := valid_cache lambda k node hValid
  exact apply_bounds lambda k (offset node) _ (mass (prepare lambda k) node) (exactMass (base k) node)
    (valid_offset lambda k node hValid) hc.1 (exact_mass_positive (base k) (base_positive k) node).le hc.2.2.1 hc.2.2.2

theorem rounded_root_code_sum (lambda k : ℕ) {height : ℕ} (node : Node height) (hValid : Valid lambda k node) :
    retention (prepare lambda k).format.unit^((GeneralPaperPowerPrecision.levelBound lambda k+2)*height+
        GeneralPaperPowerPrecision.levelBound lambda k+1)*(∑ i ∈ Finset.range (2^height), base k^levelAt node i)≤
      value (applyOffset (prepare lambda k) (offset node) (mass (prepare lambda k) node)).number ∧
    value (applyOffset (prepare lambda k) (offset node) (mass (prepare lambda k) node)).number≤
      ∑ i ∈ Finset.range (2^height), base k^levelAt node i := by
  rw [global_mass_sum]
  exact rounded_root_bounds lambda k node hValid

end Blotto.GeneralPaperIntervalMass

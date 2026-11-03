import Blotto.GeneralPaperNormalizedMassError

/-! Fresh global subtree masses include the exact ancestor offset once.
The path-level invariant proves that the actual shared-table power query is
within G. Structural cache error then gives a common exponent for every node
visited by quantile descent.
-/
namespace Blotto.GeneralPaperGlobalNodeQuery
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperCachedMassJoin
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalMass
open GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 2500000

def PathBound (cap ancestor : ℕ) {height : ℕ} (node : Node height) : Prop :=
  ∀ index<2^height, ancestor+levelAt node index≤cap

def trueMass (k ancestor : ℕ) {height : ℕ} (node : Node height) : ℚ :=
  base k^ancestor*globalMass (base k) node

def fresh (prepared : Prepared) (ancestor : ℕ) {height : ℕ} (node : Node height) : GeneralPaperDyadicMultiply.Result :=
  applyOffset prepared (ancestor+offset node) (mass prepared node)

theorem path_offset (cap ancestor : ℕ) {height : ℕ} (node : Node height) (h : PathBound cap ancestor node) :
    ancestor+offset node≤cap := by
  have hp := h 0 (Nat.two_pow_pos _)
  have ho := offset_le_level node 0
  omega

theorem child_paths (cap ancestor : ℕ) {height : ℕ} (node : Node (height+1)) (h : PathBound cap ancestor node) :
    PathBound cap (ancestor+offset node) (leftChild node) ∧ PathBound cap (ancestor+offset node) (rightChild node) := by
  constructor
  · intro index hi
    have hRange : index<2^(height+1) := by rw [pow_succ]; omega
    have hp := h index hRange
    rw [split_level node index,if_pos hi] at hp
    omega
  · intro index hi
    have hRange : 2^height+index<2^(height+1) := by rw [pow_succ]; omega
    have hp := h (2^height+index) hRange
    rw [split_level node (2^height+index),if_neg (by omega),Nat.add_sub_cancel_left] at hp
    omega

theorem child_validity (lambda k : ℕ) {height : ℕ} (node : Node (height+1)) (h : Valid lambda k node) :
    Valid lambda k (leftChild node) ∧ Valid lambda k (rightChild node) := by
  cases node with
  | uniform h level => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | branch level cached left right => exact ⟨h.2.1,h.2.2.1⟩

theorem true_positive (k ancestor : ℕ) {height : ℕ} (node : Node height) : 0<trueMass k ancestor node :=
  mul_pos (pow_pos (base_positive k) _) (global_mass_positive (base k) (base_positive k) node)

theorem true_split (k ancestor : ℕ) {height : ℕ} (node : Node (height+1)) :
    trueMass k ancestor node=trueMass k (ancestor+offset node) (leftChild node)+
      trueMass k (ancestor+offset node) (rightChild node) := by
  cases node with
  | uniform h level =>
    simp only [trueMass,globalMass,offset,exactMass,leftChild,rightChild,pow_zero,one_mul,pow_succ,pow_add]
    ring
  | branch level cached left right =>
    simp only [trueMass,globalMass,offset,exactMass,leftChild,rightChild,pow_add]
    ring

theorem true_uniform (k ancestor height level : ℕ) :
    trueMass k ancestor (.uniform height level)=base k^(ancestor+level)*(2:ℚ)^height := by
  simp only [trueMass,globalMass,offset,exactMass,pow_add]
  ring

theorem fresh_bound (lambda k ancestor : ℕ) {height : ℕ} (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node) :
    Bound (prepare lambda k).format.unit (queryExponent lambda k) (trueMass k ancestor node)
      (fresh (prepare lambda k) ancestor node).number := by
  have hc := valid_cache lambda k node hValid
  have ho := path_offset _ ancestor node hPath
  have ha := apply_bounds lambda k (ancestor+offset node) ((GeneralPaperPowerPrecision.levelBound lambda k+2)*height)
    (mass (prepare lambda k) node) (exactMass (base k) node) ho hc.1
    (exact_mass_positive (base k) (base_positive k) node).le hc.2.2.1 hc.2.2.2
  have hMass : base k^(ancestor+offset node)*exactMass (base k) node=trueMass k ancestor node := by
    unfold trueMass globalMass
    rw [pow_add]
    ring
  rw [hMass] at ha
  have hInitial : Bound (prepare lambda k).format.unit
      ((GeneralPaperPowerPrecision.levelBound lambda k+2)*height+GeneralPaperPowerPrecision.levelBound lambda k+1)
      (trueMass k ancestor node) (fresh (prepare lambda k) ancestor node).number :=
    ⟨apply_normal lambda k _ _ ho hc.1,(true_positive k ancestor node).le,ha.1,ha.2⟩
  apply weaken _ _ _ _ _ (GeneralPaperPowerPrecision.unit_positive lambda k) _ hInitial
  unfold queryExponent
  nlinarith

theorem fresh_positive (lambda k ancestor : ℕ) {height : ℕ} (node : Node height)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node) :
    0<(fresh (prepare lambda k) ancestor node).number.mantissa := by
  have hc := valid_cache lambda k node hValid
  exact apply_positive lambda k _ _ (path_offset _ ancestor node hPath) hc.1 hc.2.1

theorem fresh_work (lambda k ancestor : ℕ) {height : ℕ} (node : Node height) :
    (fresh (prepare lambda k) ancestor node).work≤
      (prepare lambda k).format.columns*(12*((prepare lambda k).format.fractionalBits+1)+82)+
        12*((prepare lambda k).format.fractionalBits+1)+92 := by
  have hq := query_work lambda k (ancestor+offset node)
  have ha := apply_work (prepare lambda k) (ancestor+offset node) (mass (prepare lambda k) node)
  change (applyOffset _ _ _).work≤_
  omega

end Blotto.GeneralPaperGlobalNodeQuery

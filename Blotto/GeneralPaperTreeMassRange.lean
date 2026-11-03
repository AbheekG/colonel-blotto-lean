import Blotto.GeneralPaperMassExponentRange

/-! Derive mass ranges from the actual code-level path invariant. Every
nonempty prefix contains a geometric weight at least 2^(-G); dense sums
are proof semantics only. Cached and fresh masses inherit the paper range.
-/
namespace Blotto.GeneralPaperTreeMassRange
open scoped BigOperators
open GeneralPaperDyadicFloat GeneralPaperCachedMassJoin GeneralPaperIntervalCache
open GeneralPaperIntervalLevels GeneralPaperIntervalMass GeneralPaperGlobalNodeQuery GeneralPaperTreePrefix
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem base_range (k : ℕ) : (1/2:ℚ)≤base k ∧ base k<1 := by
  have hp := GeneralPaperSourceParameters.positive k
  exact GeneralPaperGeometricLevels.base_bounds _ _ hp.2.1 hp.2.2.2 (GeneralPaperSourceParameters.eta_theta k)

theorem weight_range (k G level : ℕ) (hLevel : level≤G) :
    (2:ℚ)^(-(G:ℤ))≤base k^level ∧ base k^level≤1 := by
  have hb := base_range k
  have hHalf := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤1/2) (by norm_num : (1/2:ℚ)≤1) hLevel
  have hBase : (1/2:ℚ)^level≤base k^level := by gcongr; exact hb.1
  have hIdentity : (1/2:ℚ)^G=(2:ℚ)^(-(G:ℤ)) := by simp only [zpow_neg,zpow_natCast,one_div,inv_pow]
  rw [hIdentity] at hHalf
  exact ⟨hHalf.trans hBase,pow_le_one₀ (by linarith) hb.2.le⟩

theorem weighted_sum (k ancestor : ℕ) {height : ℕ} (node : Node height) (count : ℕ) :
    weightedPrefix k ancestor node count=∑ i∈Finset.range count,base k^(ancestor+levelAt node i) := by
  unfold weightedPrefix prefixWeights
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

theorem weighted_lower (k G ancestor : ℕ) {height : ℕ} (node : Node height) (count : ℕ)
    (hPath : PathBound G ancestor node) (hCount : 0<count) :
    (2:ℚ)^(-(G:ℤ))≤weightedPrefix k ancestor node count := by
  have hWeight := (weight_range k G (ancestor+levelAt node 0) (hPath 0 (Nat.two_pow_pos height))).1
  rw [weighted_sum]
  have hs := Finset.single_le_sum
    (fun i (_ : i∈Finset.range count) => pow_nonneg (base_positive k).le (ancestor+levelAt node i))
    (Finset.mem_range.mpr hCount)
  exact hWeight.trans hs

theorem weighted_upper (k ancestor : ℕ) {height : ℕ} (node : Node height) (count : ℕ) (hCount : count≤2^height) :
    weightedPrefix k ancestor node count≤(2:ℚ)^height := by
  have hb := base_range k
  rw [weighted_sum]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.range count) =>
    pow_le_one₀ (base_positive k).le hb.2.le (n:=ancestor+levelAt node i))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hs
  have hc : (count:ℚ)≤(2:ℚ)^height := by exact_mod_cast hCount
  exact hs.trans hc

theorem true_range (k G ancestor : ℕ) {height : ℕ} (node : Node height) (hPath : PathBound G ancestor node) :
    (2:ℚ)^(-(G:ℤ))≤trueMass k ancestor node ∧ trueMass k ancestor node≤(2:ℚ)^height := by
  have hl := weighted_lower k G ancestor node (2^height) hPath (Nat.two_pow_pos height)
  have hu := weighted_upper k ancestor node (2^height) (Nat.le_refl _)
  rw [weighted_total] at hl hu
  exact ⟨hl,hu⟩

theorem exact_upper (k : ℕ) {height : ℕ} (node : Node height) : exactMass (base k) node≤(2:ℚ)^height := by
  have hb := base_range k
  induction node with
  | uniform height level => exact le_refl _
  | @branch height level cached left right ihl ihr =>
    have hl := mul_le_mul
      (pow_le_one₀ (base_positive k).le hb.2.le (n:=offset left)) ihl
      (exact_mass_positive (base k) (base_positive k) left).le (by norm_num : (0:ℚ)≤1)
    have hr := mul_le_mul
      (pow_le_one₀ (base_positive k).le hb.2.le (n:=offset right)) ihr
      (exact_mass_positive (base k) (base_positive k) right).le (by norm_num : (0:ℚ)≤1)
    change base k^offset left*exactMass (base k) left+base k^offset right*exactMass (base k) right≤_
    rw [pow_succ]
    nlinarith only [hl,hr]

theorem exact_lower (k G : ℕ) {height : ℕ} (node : Node height) (hPath : PathBound G 0 node) :
    (2:ℚ)^(-(G:ℤ))≤exactMass (base k) node := by
  have hl := (true_range k G 0 node hPath).1
  have hb := base_range k
  have hFactor := pow_le_one₀ (base_positive k).le hb.2.le (n:=offset node)
  have hs := mul_le_of_le_one_left (exact_mass_positive (base k) (base_positive k) node).le hFactor
  simp only [trueMass,pow_zero,one_mul,globalMass] at hl
  exact hl.trans hs

theorem cached (lambda k : ℕ) {height : ℕ} (node : Node height) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (mass (GeneralPaperPreparedPowers.prepare lambda k) node).exponent.natAbs≤
      lambda+GeneralPaperPowerPrecision.levelBound lambda k+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+8 := by
  let G := GeneralPaperPowerPrecision.levelBound lambda k
  have hc := valid_cache lambda k node hValid
  have hBound : GeneralPaperMassApproximation.Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit
      ((G+2)*height) (exactMass (base k) node) (mass (GeneralPaperPreparedPowers.prepare lambda k) node) :=
    ⟨hc.1,(exact_mass_positive (base k) (base_positive k) node).le,hc.2.2.1,hc.2.2.2⟩
  have hBudget : (G+2)*height≤GeneralPaperMassApproximation.budget lambda k := by
    have hh := Nat.mul_le_mul_left (G+2) hHeight
    unfold GeneralPaperMassApproximation.budget GeneralPaperMassApproximation.queryExponent
    change (G+2)*height≤(G+2)*(lambda+1)+G+1+lambda+2
    omega
  exact GeneralPaperMassExponentRange.paper_range lambda k ((G+2)*height) G height _ _ hHeight hBudget hBound
    (Or.inr (exact_lower k G node hPath)) (exact_upper k node)

theorem fresh (lambda k ancestor : ℕ) {height : ℕ} (node : Node height) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node) :
    (GeneralPaperGlobalNodeQuery.fresh (GeneralPaperPreparedPowers.prepare lambda k) ancestor node).number.exponent.natAbs≤
      lambda+GeneralPaperPowerPrecision.levelBound lambda k+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+8 := by
  have hb := fresh_bound lambda k ancestor node hHeight hValid hPath
  have hm := true_range k (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node hPath
  exact GeneralPaperMassExponentRange.paper_range lambda k _ _ height _ _ hHeight
    (by unfold GeneralPaperMassApproximation.budget; omega) hb (Or.inr hm.1) hm.2

theorem prefix_range (lambda k ancestor exponent : ℕ) {height : ℕ} (node : Node height) (count : ℕ) (x : Number)
    (hHeight : height≤lambda+1) (hCount : count≤2^height)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hExponent : exponent≤GeneralPaperMassApproximation.budget lambda k)
    (hBound : GeneralPaperMassApproximation.Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit
      exponent (weightedPrefix k ancestor node count) x) :
    x.exponent.natAbs≤lambda+GeneralPaperPowerPrecision.levelBound lambda k+
      (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+8 := by
  apply GeneralPaperMassExponentRange.paper_range lambda k exponent _ height _ x hHeight hExponent hBound
  · by_cases hc : count=0
    · exact Or.inl (by rw [hc,weighted_zero])
    · exact Or.inr (weighted_lower k _ ancestor node count hPath (by omega))
  · exact weighted_upper k ancestor node count hCount

end Blotto.GeneralPaperTreeMassRange

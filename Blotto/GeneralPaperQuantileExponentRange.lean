import Blotto.GeneralPaperTreeMassRange

/-! An erased invariant follows the actual branch selected at every
quantile descent. It bounds every stored total/mass/prefix and both child
masses/through-prefix by the paper signed-exponent range. No trace is stored.
-/
namespace Blotto.GeneralPaperQuantileExponentRange
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperTreePrefix GeneralPaperMassApproximation
open GeneralPaperQuantileDescent
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def cap (lambda k : ℕ) : ℕ := lambda+GeneralPaperPowerPrecision.levelBound lambda k+
  (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+8

def StateBound (R : ℕ) (total storedMass storedPrefix : Number) : Prop :=
  total.exponent.natAbs≤R ∧ storedMass.exponent.natAbs≤R ∧ storedPrefix.exponent.natAbs≤R

def Safe (lambda k width j s : ℕ) (storedTotal : Number) :
    (height : ℕ) → Node height → ℕ → Number → Number → Prop
  | 0,_,_,storedMass,storedPrefix => StateBound (cap lambda k) storedTotal storedMass storedPrefix
  | height+1,node,ancestor,storedMass,storedPrefix =>
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    let left := leftMass prepared ancestor node storedMass
    let right := rightMass prepared ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add prepared.format.unit prepared.format.fractionalBits storedPrefix left.number
    StateBound (cap lambda k) storedTotal storedMass storedPrefix ∧
      left.number.exponent.natAbs≤cap lambda k ∧ right.number.exponent.natAbs≤cap lambda k ∧
      through.number.exponent.natAbs≤cap lambda k ∧
      if (GeneralPaperDyadicCompare.scaledLE width j storedTotal s through.number).answer then
        Safe lambda k width j s storedTotal height (leftChild node) (ancestor+offset node) left.number storedPrefix
      else
        Safe lambda k width j s storedTotal height (rightChild node) (ancestor+offset node) right.number through.number

theorem state_bound (lambda k height ancestor depth : ℕ) (node : Node height) (P T : ℚ)
    (storedTotal storedMass storedPrefix : Number) (hDepth : height+depth≤lambda+1)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hTotal : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k) T storedTotal)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k) (trueMass k ancestor node) storedMass)
    (hPrefix : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k+depth) P storedPrefix)
    (hPrefixMin : P=0 ∨ (2:ℚ)^(-(GeneralPaperPowerPrecision.levelBound lambda k:ℤ))≤P)
    (hTotalMin : (2:ℚ)^(-(GeneralPaperPowerPrecision.levelBound lambda k:ℤ))≤T)
    (hTotalMax : T≤(2:ℚ)^(lambda+1)) (hDomain : P+trueMass k ancestor node≤T) :
    StateBound (cap lambda k) storedTotal storedMass storedPrefix := by
  have hQuery : queryExponent lambda k≤budget lambda k := by unfold budget; omega
  have hPrefixExp : queryExponent lambda k+depth≤budget lambda k := by unfold budget; omega
  have hT := GeneralPaperMassExponentRange.paper_range lambda k _ _ (lambda+1) T storedTotal
    (Nat.le_refl _) hQuery hTotal (Or.inr hTotalMin) hTotalMax
  have hBounds := GeneralPaperTreeMassRange.true_range k (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node hPath
  have hM := GeneralPaperMassExponentRange.paper_range lambda k _ _ height _ storedMass
    (by omega) hQuery hMass (Or.inr hBounds.1) hBounds.2
  have hPMax : P≤(2:ℚ)^(lambda+1) := by
    have hPos := true_positive k ancestor node
    linarith
  have hP := GeneralPaperMassExponentRange.paper_range lambda k _ _ (lambda+1) P storedPrefix
    (Nat.le_refl _) hPrefixExp hPrefix hPrefixMin hPMax
  exact ⟨hT,hM,hP⟩

theorem safe (lambda k width j s : ℕ) (storedTotal : Number) (T : ℚ)
    (hTotal : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k) T storedTotal)
    (hTotalMin : (2:ℚ)^(-(GeneralPaperPowerPrecision.levelBound lambda k:ℤ))≤T)
    (hTotalMax : T≤(2:ℚ)^(lambda+1))
    (height : ℕ) (node : Node height) (ancestor depth : ℕ) (P : ℚ) (storedMass storedPrefix : Number)
    (hDepth : height+depth≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k) (trueMass k ancestor node) storedMass)
    (hPrefix : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k+depth) P storedPrefix)
    (hPrefixMin : P=0 ∨ (2:ℚ)^(-(GeneralPaperPowerPrecision.levelBound lambda k:ℤ))≤P)
    (hDomain : P+trueMass k ancestor node≤T) :
    Safe lambda k width j s storedTotal height node ancestor storedMass storedPrefix := by
  induction height generalizing ancestor depth P storedMass storedPrefix with
  | zero =>
    exact state_bound lambda k 0 ancestor depth node P T storedTotal storedMass storedPrefix
      hDepth hPath hTotal hMass hPrefix hPrefixMin hTotalMin hTotalMax hDomain
  | succ height ih =>
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    let G := GeneralPaperPowerPrecision.levelBound lambda k
    let left := leftMass prepared ancestor node storedMass
    let right := rightMass prepared ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add prepared.format.unit prepared.format.fractionalBits storedPrefix left.number
    let L := trueMass k (ancestor+offset node) (leftChild node)
    let R := trueMass k (ancestor+offset node) (rightChild node)
    have hState := state_bound lambda k (height+1) ancestor depth node P T storedTotal storedMass storedPrefix
      hDepth hPath hTotal hMass hPrefix hPrefixMin hTotalMin hTotalMax hDomain
    have hSplit : trueMass k ancestor node=L+R := true_split k ancestor node
    have hChildren := child_validity lambda k node hValid
    have hPaths := child_paths _ ancestor node hPath
    have hL := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass (by omega) hValid hPath hMass
    have hR := GeneralPaperQuantileChildMass.right_bound lambda k ancestor node storedMass (by omega) hValid hPath hMass
    have hLRange := GeneralPaperTreeMassRange.true_range k G (ancestor+offset node) (leftChild node) hPaths.1
    have hRRange := GeneralPaperTreeMassRange.true_range k G (ancestor+offset node) (rightChild node) hPaths.2
    have hQ : queryExponent lambda k≤budget lambda k := by unfold budget; omega
    have hLMag := GeneralPaperMassExponentRange.paper_range lambda k _ G height L left.number
      (by omega) hQ hL (Or.inr hLRange.1) hLRange.2
    have hRMag := GeneralPaperMassExponentRange.paper_range lambda k _ G height R right.number
      (by omega) hQ hR (Or.inr hRRange.1) hRRange.2
    have hLeftWeak := weaken _ _ (queryExponent lambda k+depth) _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
      (Nat.le_add_right _ _) hL
    have hThrough : Bound prepared.format.unit (queryExponent lambda k+(depth+1)) (P+L) through.number := by
      dsimp only [through,prepared,GeneralPaperPreparedPowers.prepare]
      simpa only [Nat.add_assoc] using add_bound _ _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
        (GeneralPaperPowerPrecision.unit_power lambda k) P L storedPrefix left.number hPrefix hLeftWeak
    have hPNonneg := hPrefix.2.1
    have hThroughMin : (2:ℚ)^(-(G:ℤ))≤P+L := by have hl:=hLRange.1; change _≤L at hl; linarith
    have hThroughMax : P+L≤(2:ℚ)^(lambda+1) := by
      have hr := true_positive k (ancestor+offset node) (rightChild node)
      change 0<R at hr
      rw [hSplit] at hDomain
      linarith
    have hThroughMag := GeneralPaperMassExponentRange.paper_range lambda k _ G (lambda+1) (P+L) through.number
      (Nat.le_refl _) (by unfold budget; omega) hThrough (Or.inr hThroughMin) hThroughMax
    change StateBound _ _ _ _ ∧ left.number.exponent.natAbs≤_ ∧ right.number.exponent.natAbs≤_ ∧
      through.number.exponent.natAbs≤_ ∧ _
    refine ⟨hState,hLMag,hRMag,hThroughMag,?_⟩
    split
    · have hp := weaken _ _ (queryExponent lambda k+(depth+1)) _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
        (by omega) hPrefix
      apply ih (leftChild node) (ancestor+offset node) (depth+1) P left.number storedPrefix (by omega)
        hChildren.1 hPaths.1 hL hp hPrefixMin
      have hr := true_positive k (ancestor+offset node) (rightChild node)
      change 0<R at hr
      rw [hSplit] at hDomain
      linarith
    · apply ih (rightChild node) (ancestor+offset node) (depth+1) (P+L) right.number through.number (by omega)
        hChildren.2 hPaths.2 hR hThrough (Or.inr hThroughMin)
      rw [hSplit] at hDomain
      linarith

theorem initial (lambda k width j s height : ℕ) (node : Node height) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    let total := (fresh prepared 0 node).number
    Safe lambda k width j s total height node 0 total zero := by
  let prepared := GeneralPaperPreparedPowers.prepare lambda k
  have hTotal := fresh_bound lambda k 0 node hHeight hValid hPath
  have hRange := GeneralPaperTreeMassRange.true_range k (GeneralPaperPowerPrecision.levelBound lambda k) 0 node hPath
  have hUpper : trueMass k 0 node≤(2:ℚ)^(lambda+1) :=
    hRange.2.trans (pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) hHeight)
  apply safe lambda k width j s _ _ hTotal hRange.1 hUpper height node 0 0 0 _ zero
    (by omega) hValid hPath hTotal
  · exact zero_bound _ _
  · exact Or.inl rfl
  · simp only [zero_add,le_refl]

end Blotto.GeneralPaperQuantileExponentRange

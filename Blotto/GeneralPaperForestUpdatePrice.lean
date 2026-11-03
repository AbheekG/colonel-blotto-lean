import Blotto.GeneralPaperForestUpdateExecution

/-! All four retained forest families have complete arithmetic/bit prices.
Signed height additions, field reads, array writes/control and final records
are included. The same post-epoch level cap supplies all per-node premises.
-/
namespace Blotto.GeneralPaperForestUpdatePrice
open GeneralPaperIntervalCache GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperForestUpdateExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def familyProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  m*(GeneralPaperEpochNodeUpdate.profile price W m lambda k Qv+
    2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+256*W)+44*(m+1)*arrayWord W m

def arithmeticFamilyProfile (m lambda k Qv : ℕ) : ℕ :=
  m*(GeneralPaperEpochNodeUpdate.arithmeticProfile m lambda k Qv+2+256)+44*(m+1)

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ := 4*familyProfile price W m lambda k Qv+128*W

def arithmeticProfile (m lambda k Qv : ℕ) : ℕ := 4*arithmeticFamilyProfile m lambda k Qv+128

theorem height_work (price : ℕ → ℕ) (hMono : Monotone price) (m lambda k Qv : ℕ) (learner : Learner) :
    heightCost price learner lambda≤2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  have hm : binaryWordWidth (lambda+1)≤GeneralPaperSourcePreparationSizes.measure m lambda k Qv := by
    unfold GeneralPaperSourcePreparationSizes.measure
    omega
  have hp := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  have hw : 1+binaryWordWidth (lambda+1)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    unfold GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  have h := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) lambda 1 (lambda+1)
    (by omega) (by omega) (Nat.le_refl _)).trans (Nat.mul_le_mul_left 2 (hMono hw))
  cases learner with
  | p => exact Nat.zero_le _
  | q => exact Nat.zero_le _
  | lambda => exact h
  | mu => exact h

theorem height_arithmetic (lambda : ℕ) (learner : Learner) : heightCost (fun _ => 1) learner lambda≤2 := by
  cases learner with
  | p => exact Nat.zero_le _
  | q => exact Nat.zero_le _
  | lambda => exact Nat.le_refl _
  | mu => exact Nat.le_refl _

theorem element_bit_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (hMono : Monotone price) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (learner : Learner) (j : Fin m)
    (hSpan : ∀ learner,span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ learner j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (element true (fun w => w) price W c shared trees state learner j).2≤
      GeneralPaperEpochNodeUpdate.profile price W m cache.alphabet.lambda k Qv+
        2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m cache.alphabet.lambda k Qv)+256*W := by
  have hn := GeneralPaperEpochNodeUpdate.bit_work price hMono W Qv c hc learner state j _ _ _
    (hSpan learner) (tree_height_bound learner cache.alphabet.lambda) (hValid learner j) (hFinal learner j)
  have hh := height_work price hMono m cache.alphabet.lambda k Qv learner
  exact Nat.add_le_add_right (Nat.add_le_add hn hh) (256*W)

theorem family_bit_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (hMono : Monotone price) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (learner : Learner)
    (hSpan : ∀ learner,span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ learner j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (family true (fun w => w) price W c shared trees state learner).2≤familyProfile price W m cache.alphabet.lambda k Qv := by
  exact GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) _
    (element true (fun w => w) price W c shared trees state learner)
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (fun j => element_bit_work price hMono W Qv c hc shared trees state learner j hSpan hValid hFinal)

theorem element_arithmetic_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (learner : Learner) (j : Fin m)
    (hSpan : ∀ learner,span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ learner j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (element false (fun _ => 1) price 1 c shared trees state learner j).2≤
      GeneralPaperEpochNodeUpdate.arithmeticProfile m cache.alphabet.lambda k Qv+2+256 := by
  have hn := GeneralPaperEpochNodeUpdate.arithmetic_work price Qv c hc learner state j _ _ _
    (hSpan learner) (tree_height_bound learner cache.alphabet.lambda) (hValid learner j) (hFinal learner j)
  have hh := height_arithmetic cache.alphabet.lambda learner
  exact Nat.add_le_add_right (Nat.add_le_add hn hh) 256

theorem family_arithmetic_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (learner : Learner)
    (hSpan : ∀ learner,span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ learner j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (family false (fun _ => 1) price 1 c shared trees state learner).2≤arithmeticFamilyProfile m cache.alphabet.lambda k Qv := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1
    (GeneralPaperEpochNodeUpdate.arithmeticProfile m cache.alphabet.lambda k Qv+2+256)
    (element false (fun _ => 1) price 1 c shared trees state learner)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun j => element_arithmetic_work price Qv c hc shared trees state learner j hSpan hValid hFinal)
  simpa only [family,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticFamilyProfile] using h

theorem sum_four (p q l u C W : ℕ) (hp : p≤C) (hq : q≤C) (hl : l≤C) (hu : u≤C) :
    p+q+l+u+128*W≤4*C+128*W := by omega

theorem bit_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (hMono : Monotone price) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (hSpan : ∀ learner,span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ learner j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (run true (fun w => w) price W c shared trees state).2≤profile price W m cache.alphabet.lambda k Qv := by
  exact sum_four _ _ _ _ _ W
    (family_bit_work price hMono W Qv c hc shared trees state .p hSpan hValid hFinal)
    (family_bit_work price hMono W Qv c hc shared trees state .q hSpan hValid hFinal)
    (family_bit_work price hMono W Qv c hc shared trees state .lambda hSpan hValid hFinal)
    (family_bit_work price hMono W Qv c hc shared trees state .mu hSpan hValid hFinal)

theorem arithmetic_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (shared : Shared m) (trees : Trees m cache.alphabet.lambda) (state : State cache)
    (hSpan : ∀ learner,span learner shared=(2:ℚ)^(treeHeight learner cache.alphabet.lambda))
    (hValid : Valid cache.alphabet k trees)
    (hFinal : ∀ learner j i,i<2^(treeHeight learner cache.alphabet.lambda) → GeneralPaperIntervalLevels.levelAt (node learner trees j) i+
      GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
        GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (run false (fun _ => 1) price 1 c shared trees state).2≤arithmeticProfile m cache.alphabet.lambda k Qv := by
  exact sum_four _ _ _ _ _ 1
    (family_arithmetic_work price Qv c hc shared trees state .p hSpan hValid hFinal)
    (family_arithmetic_work price Qv c hc shared trees state .q hSpan hValid hFinal)
    (family_arithmetic_work price Qv c hc shared trees state .lambda hSpan hValid hFinal)
    (family_arithmetic_work price Qv c hc shared trees state .mu hSpan hValid hFinal)

end Blotto.GeneralPaperForestUpdatePrice

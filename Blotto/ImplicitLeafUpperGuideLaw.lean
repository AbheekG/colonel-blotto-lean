import Blotto.ImplicitLeafUpperGuide
import Blotto.ImplicitLeafIntervalMass

/-! All-real-threshold upper envelopes for the actual plateau-safe R162 leaf
bin constructor. The guide is upper-oriented; it is not inserted into an
existing lower-certified recursive tree without a separate orientation proof. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

noncomputable def intervalResourceMass (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (lo hi : ℕ) (threshold : ℝ) : ℚ := ∑ code : Fin (C + 1),
  if lo ≤ code.val ∧ code.val ≤ hi ∧ (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0

theorem intervalResourceMass_nonnegative (C : ℕ) (blocks : List Block) (hn : Nonnegative blocks)
    (decode : ℕ → ℚ) (lo hi : ℕ) (threshold : ℝ) : 0 ≤ intervalResourceMass C blocks decode lo hi threshold := by
  apply Finset.sum_nonneg
  intro code _
  split_ifs
  · exact labelMass_nonnegative blocks code.val hn
  · exact le_rfl

theorem intervalResourceMass_le (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hn : Nonnegative blocks)
    (decode : ℕ → ℚ) (lo hi : ℕ) (hOrder : lo ≤ hi) (threshold : ℝ) :
    intervalResourceMass C blocks decode lo hi threshold ≤ intervalMass blocks lo hi := by
  rw [intervalMass_labels C blocks hp lo hi hOrder]
  apply Finset.sum_le_sum
  intro code _
  split_ifs <;> first | exact le_rfl | exact labelMass_nonnegative blocks code.val hn | omega

theorem intervalResourceMass_append (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (lo middle hi : ℕ) (hm : lo ≤ middle ∧ middle ≤ hi) (threshold : ℝ) :
    intervalResourceMass C blocks decode lo middle threshold +
      intervalResourceMass C blocks decode (middle + 1) hi threshold = intervalResourceMass C blocks decode lo hi threshold := by
  unfold intervalResourceMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro code _
  by_cases ht : (decode code.val : ℝ) ≤ threshold
  · simp only [ht, and_true]
    split_ifs <;> first | omega | simp
  · simp only [ht, and_false, ite_false, add_zero]

theorem intervalResourceMass_zero_after (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (lo hi : ℕ) (threshold : ℝ) (hAfter : ∀ code : Fin (C + 1), lo ≤ code.val ∧ code.val ≤ hi → threshold < (decode code.val : ℝ)) :
    intervalResourceMass C blocks decode lo hi threshold = 0 := by
  apply Finset.sum_eq_zero
  intro code _
  split_ifs with h
  · exact False.elim (not_le_of_gt (hAfter code ⟨h.1, h.2.1⟩) h.2.2)
  · rfl

theorem intervalResourceMass_full_before (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (decode : ℕ → ℚ) (lo hi : ℕ) (hOrder : lo ≤ hi) (threshold : ℝ)
    (hBefore : ∀ code : Fin (C + 1), lo ≤ code.val ∧ code.val ≤ hi → (decode code.val : ℝ) ≤ threshold) :
    intervalResourceMass C blocks decode lo hi threshold = intervalMass blocks lo hi := by
  rw [intervalMass_labels C blocks hp lo hi hOrder]
  apply Finset.sum_congr rfl
  intro code _
  by_cases h : lo ≤ code.val ∧ code.val ≤ hi
  · simp only [h.1, h.2, hBefore code h, and_self, ite_true]
  · have he : ¬(lo ≤ code.val ∧ code.val ≤ hi ∧ (decode code.val : ℝ) ≤ threshold) := by omega
    simp only [he, h, ite_false]

def LocalUpperBins (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) : ℕ → List UpperBin → Prop
  | next, [] => next = C + 1
  | next, bin :: rest => bin.lo = next ∧ bin.lo ≤ bin.hi ∧ bin.hi ≤ C ∧
      bin.resource = decode bin.lo ∧ bin.mass = intervalMass blocks bin.lo bin.hi ∧
      plateauEnd C decode bin.lo ≤ bin.hi ∧
      prefixMass blocks (bin.hi : ℤ) ≤ gamma * prefixMass blocks (plateauEnd C decode bin.lo : ℤ) ∧
      LocalUpperBins C blocks decode gamma (bin.hi + 1) rest

theorem upperBins_local (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (start : ℕ) (hs : start ≤ C + 1) :
    LocalUpperBins C blocks decode gamma start (upperBins C blocks decode gamma start) := by
  rw [upperBins]
  by_cases hActive : start ≤ C
  · rw [ite_eq_left hActive]
    have he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
    have hStep : start ≤ (upperBinStep C blocks decode gamma start).hi := he.1
    rw [ite_eq_left hStep]
    change start = start ∧ start ≤ upperBinEnd C blocks decode gamma start ∧ upperBinEnd C blocks decode gamma start ≤ C ∧
      decode start = decode start ∧ _ = _ ∧ plateauEnd C decode start ≤ upperBinEnd C blocks decode gamma start ∧
      prefixMass blocks (upperBinEnd C blocks decode gamma start : ℤ) ≤ _ ∧ _
    refine ⟨rfl, he.1, he.2.1, rfl, rfl,
      upperBinEnd_plateau_covered C blocks hp hw decode hm gamma hg start hActive, he.2.2, ?_⟩
    exact upperBins_local C blocks hp hw decode hm gamma hg
      (upperBinEnd C blocks decode gamma start + 1) (by omega)
  · rw [ite_eq_right hActive]
    change start = C + 1
    omega
termination_by C + 1 - start
decreasing_by
  have _he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hActive
  omega

theorem intervalResourceMass_empty (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (lo hi : ℕ) (h : hi < lo) (threshold : ℝ) : intervalResourceMass C blocks decode lo hi threshold = 0 := by
  apply Finset.sum_eq_zero
  intro code _
  rw [ite_eq_right (by omega)]

theorem intervalResourceMass_prefix_lower (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hn : Nonnegative blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (code : ℕ) (hc : code ≤ C)
    (threshold : ℝ) (ht : (decode code : ℝ) ≤ threshold) :
    prefixMass blocks (code : ℤ) ≤ intervalResourceMass C blocks decode 0 C threshold := by
  rw [← intervalMass_prefix blocks code, intervalMass_labels C blocks hp 0 code (Nat.zero_le _)]
  apply Finset.sum_le_sum
  intro label _
  by_cases hl : label.val ≤ code
  · have hResource : (decode label.val : ℝ) ≤ threshold := by
      have hle : (decode label.val : ℝ) ≤ (decode code : ℝ) := by exact_mod_cast hm label.val code hl hc
      exact hle.trans ht
    simp only [Nat.zero_le, hl, and_self, hResource, ite_true, show label.val ≤ C by omega]
    exact le_rfl
  · have hFalse : ¬(0 ≤ label.val ∧ label.val ≤ code) := by omega
    rw [ite_eq_right hFalse]
    split_ifs
    · exact labelMass_nonnegative blocks label.val hn
    · exact le_rfl

theorem localUpperBins_after (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ)
    (bins : List UpperBin) (next : ℕ) (h : LocalUpperBins C blocks decode gamma next bins) :
    ∀ bin ∈ bins, next ≤ bin.lo ∧ bin.lo ≤ bin.hi ∧ bin.hi ≤ C ∧ bin.resource = decode bin.lo := by
  induction bins generalizing next with
  | nil => simp
  | cons bin rest ih =>
    change bin.lo = next ∧ bin.lo ≤ bin.hi ∧ bin.hi ≤ C ∧ bin.resource = decode bin.lo ∧
      bin.mass = intervalMass blocks bin.lo bin.hi ∧ plateauEnd C decode bin.lo ≤ bin.hi ∧
      prefixMass blocks (bin.hi : ℤ) ≤ gamma * prefixMass blocks (plateauEnd C decode bin.lo : ℤ) ∧
      LocalUpperBins C blocks decode gamma (bin.hi + 1) rest at h
    intro out ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨by omega, h.2.1, h.2.2.1, h.2.2.2.1⟩
    · have he := ih (bin.hi + 1) h.2.2.2.2.2.2.2 out ho
      exact ⟨by omega, he.2⟩

theorem localUpperBins_zero_before (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ)
    (bins : List UpperBin) (next : ℕ) (h : LocalUpperBins C blocks decode gamma next bins)
    (threshold : ℝ) (ht : threshold < (decode next : ℝ)) :
    CumulativeGuidePruning.prefixMass (bins.map (fun bin => (bin.resource, bin.mass))) threshold = 0 := by
  apply CumulativeGuidePruning.prefixMass_zero_of_after
  intro atom ha
  rcases List.mem_map.mp ha with ⟨bin, hb, rfl⟩
  have he := localUpperBins_after C blocks decode gamma bins next h bin hb
  have hmR : (decode next : ℝ) ≤ (decode bin.lo : ℝ) := by exact_mod_cast hm next bin.lo he.1 (he.2.1.trans he.2.2.1)
  rw [he.2.2.2]
  exact ht.trans_le hmR

theorem localUpperBins_envelope (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode) (gamma : ℚ) (hg : 1 ≤ gamma)
    (bins : List UpperBin) (next : ℕ) (h : LocalUpperBins C blocks decode gamma next bins)
    (threshold : ℝ) :
    prefixMass blocks ((next : ℤ) - 1) + intervalResourceMass C blocks decode next C threshold ≤
      prefixMass blocks ((next : ℤ) - 1) + CumulativeGuidePruning.prefixMass (bins.map (fun bin => (bin.resource, bin.mass))) threshold ∧
    prefixMass blocks ((next : ℤ) - 1) + CumulativeGuidePruning.prefixMass (bins.map (fun bin => (bin.resource, bin.mass))) threshold ≤
      gamma * (prefixMass blocks ((next : ℤ) - 1) + intervalResourceMass C blocks decode next C threshold) := by
  have hn : Nonnegative blocks := fun block hb => (hw block hb).le
  induction bins generalizing next with
  | nil =>
    change next = C + 1 at h
    have hz := intervalResourceMass_empty C blocks decode next C (by omega) threshold
    simp only [List.map_nil, CumulativeGuidePruning.prefixMass, hz, add_zero]
    have hp0 := prefixMass_nonnegative blocks ((next : ℤ) - 1) hn
    constructor
    · exact le_rfl
    · nlinarith
  | cons bin rest ih =>
    change bin.lo = next ∧ bin.lo ≤ bin.hi ∧ bin.hi ≤ C ∧ bin.resource = decode bin.lo ∧
      bin.mass = intervalMass blocks bin.lo bin.hi ∧ plateauEnd C decode bin.lo ≤ bin.hi ∧
      prefixMass blocks (bin.hi : ℤ) ≤ gamma * prefixMass blocks (plateauEnd C decode bin.lo : ℤ) ∧
      LocalUpperBins C blocks decode gamma (bin.hi + 1) rest at h
    have hTail := h.2.2.2.2.2.2.2
    have hStepMass := h.2.2.2.2.1
    have hPlateau := h.2.2.2.2.2.1
    have hBound := h.2.2.2.2.2.2.1
    have hBinNonneg : 0 ≤ bin.mass := by rw [hStepMass]; exact (intervalMass_positive C blocks hp hw _ _ h.2.1 h.2.2.1).le
    have hPrefixNonneg := prefixMass_nonnegative blocks ((next : ℤ) - 1) hn
    by_cases hStart : (decode next : ℝ) ≤ threshold
    · have hResource : (bin.resource : ℝ) ≤ threshold := by rw [h.2.2.2.1, h.1]; exact hStart
      simp only [List.map_cons, CumulativeGuidePruning.prefixMass, hResource, ite_true]
      by_cases hNext : bin.hi < C ∧ (decode (bin.hi + 1) : ℝ) ≤ threshold
      · have hWhole : intervalResourceMass C blocks decode next bin.hi threshold = bin.mass := by
          rw [hStepMass, h.1]
          apply intervalResourceMass_full_before C blocks hp decode next bin.hi (by omega) threshold
          intro code hc
          have he : (decode code.val : ℝ) ≤ (decode (bin.hi + 1) : ℝ) := by
            exact_mod_cast hm code.val (bin.hi + 1) (by omega) (by omega)
          exact he.trans hNext.2
        have hSplit := intervalResourceMass_append C blocks decode next bin.hi C ⟨by omega, h.2.2.1⟩ threshold
        rw [hWhole] at hSplit
        have hBase : prefixMass blocks ((next : ℤ) - 1) + bin.mass = prefixMass blocks (bin.hi : ℤ) := by
          rw [hStepMass, intervalMass, h.1]
          ring
        have hBaseTail : prefixMass blocks (((bin.hi + 1 : ℕ) : ℤ) - 1) = prefixMass blocks (bin.hi : ℤ) := by congr 1; omega
        have he := ih (bin.hi + 1) hTail
        rw [hBaseTail] at he
        rw [← hSplit]
        simp_rw [← add_assoc, hBase]
        exact he
      · have hFutureZero : intervalResourceMass C blocks decode (bin.hi + 1) C threshold = 0 := by
          apply intervalResourceMass_zero_after
          intro code hc
          have hHi : bin.hi < C := by omega
          have hGreater : threshold < (decode (bin.hi + 1) : ℝ) := by
            exact lt_of_not_ge (fun hle => hNext ⟨hHi, hle⟩)
          have hmR : (decode (bin.hi + 1) : ℝ) ≤ (decode code.val : ℝ) := by exact_mod_cast hm _ _ hc.1 (by omega)
          exact hGreater.trans_le hmR
        have hGuideFutureZero : CumulativeGuidePruning.prefixMass (rest.map (fun bin => (bin.resource, bin.mass))) threshold = 0 := by
          by_cases hHi : bin.hi < C
          · apply localUpperBins_zero_before C blocks decode hm gamma rest (bin.hi + 1) hTail threshold
            exact lt_of_not_ge (fun hle => hNext ⟨hHi, hle⟩)
          · have hEmpty : rest = [] := by
              cases rest with
              | nil => rfl
              | cons out tail =>
                have ht := localUpperBins_after C blocks decode gamma (out :: tail) (bin.hi + 1) hTail out (by simp)
                omega
            simp [hEmpty, CumulativeGuidePruning.prefixMass]
        have hSplit := intervalResourceMass_append C blocks decode next bin.hi C ⟨by omega, h.2.2.1⟩ threshold
        rw [hFutureZero, add_zero] at hSplit
        have hActualUpper := intervalResourceMass_le C blocks hp hn decode next bin.hi (by omega) threshold
        rw [← h.1, ← hStepMass] at hActualUpper
        have hAtPlateau : prefixMass blocks (plateauEnd C decode next : ℤ) ≤
            prefixMass blocks ((next : ℤ) - 1) + intervalResourceMass C blocks decode next C threshold := by
          rw [partition_prefixMass_labels C blocks hp, partition_prefixMass_labels C blocks hp]
          unfold intervalResourceMass
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro code _
          by_cases hIn : code.val ≤ plateauEnd C decode next
          · by_cases hBefore : code.val < next
            · simp only [show (code.val : ℤ) ≤ (plateauEnd C decode next : ℤ) by omega,
                show (code.val : ℤ) ≤ (next : ℤ) - 1 by omega, ite_true]
              split_ifs <;> first | omega | linarith [labelMass_nonnegative blocks code.val hn]
            · have hRes : (decode code.val : ℝ) ≤ threshold := by
                rw [plateauEnd_same C decode hm next (by omega) code.val ⟨by omega, hIn⟩]
                exact hStart
              simp only [show (code.val : ℤ) ≤ (plateauEnd C decode next : ℤ) by omega,
                show ¬(code.val : ℤ) ≤ (next : ℤ) - 1 by omega,
                show next ≤ code.val by omega, show code.val ≤ C by omega, hRes,
                and_self, ite_true, ite_false, zero_add]
              exact le_rfl
          · rw [ite_eq_right (by omega)]
            split_ifs <;> first | omega | linarith [labelMass_nonnegative blocks code.val hn]
        rw [hGuideFutureZero, add_zero]
        have hBase : prefixMass blocks ((next : ℤ) - 1) + bin.mass = prefixMass blocks (bin.hi : ℤ) := by
          rw [hStepMass, intervalMass, h.1]
          ring
        rw [h.1] at hBound
        rw [h.1] at hActualUpper
        constructor
        · linarith
        · have hMul := mul_le_mul_of_nonneg_left hAtPlateau (show 0 ≤ gamma by linarith)
          linarith
    · have hActualZero : intervalResourceMass C blocks decode next C threshold = 0 := by
        apply intervalResourceMass_zero_after
        intro code hc
        have hmR : (decode next : ℝ) ≤ (decode code.val : ℝ) := by exact_mod_cast hm _ _ hc.1 (by omega)
        exact (lt_of_not_ge hStart).trans_le hmR
      have hGuideZero := localUpperBins_zero_before C blocks decode hm gamma (bin :: rest) next h threshold (lt_of_not_ge hStart)
      rw [hActualZero, hGuideZero, add_zero]
      constructor
      · exact le_rfl
      · nlinarith

theorem upperGuide_envelope (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (threshold : ℝ) :
    (∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0) ≤
      CumulativeGuidePruning.prefixMass (upperGuide C blocks decode gamma) threshold ∧
    CumulativeGuidePruning.prefixMass (upperGuide C blocks decode gamma) threshold ≤
      gamma * (∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0) := by
  have he := localUpperBins_envelope C blocks hp hw decode hm gamma hg
    (upperBins C blocks decode gamma 0) 0 (upperBins_local C blocks hp hw decode hm gamma hg 0 (by omega)) threshold
  norm_num only [Nat.cast_zero, zero_sub] at he
  have hz : prefixMass blocks (-1) = 0 := prefixMass_negative blocks (-1) (by norm_num)
  rw [hz] at he
  simp only [zero_add] at he
  have hActual : intervalResourceMass C blocks decode 0 C threshold =
      ∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0 := by
    unfold intervalResourceMass
    apply Finset.sum_congr rfl
    intro code _
    simp only [Nat.zero_le, show code.val ≤ C by omega, true_and]
  rw [hActual] at he
  exact he

theorem upperGuide_zero_iff (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (threshold : ℝ) :
    CumulativeGuidePruning.prefixMass (upperGuide C blocks decode gamma) threshold = 0 ↔
      (∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0) = 0 := by
  have he := upperGuide_envelope C blocks hp hw decode hm gamma hg threshold
  have hn : 0 ≤ (∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0) := by
    apply Finset.sum_nonneg
    intro code _
    split_ifs
    · exact (partition_labelMass_positive C blocks hp hw code).le
    · exact le_rfl
  constructor
  · intro hz
    rw [hz] at he
    exact le_antisymm he.1 hn
  · intro hz
    rw [hz, mul_zero] at he
    exact le_antisymm he.2 he.1

theorem upperGuide_family_real_envelope (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (threshold : ℝ) :
    ((∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0) : ℝ) ≤
      (CumulativeGuidePruning.prefixMass (upperGuide C blocks decode gamma) threshold : ℝ) ∧
    (CumulativeGuidePruning.prefixMass (upperGuide C blocks decode gamma) threshold : ℝ) ≤
      (gamma : ℝ) * ((∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0) : ℝ) := by
  have he := upperGuide_envelope C blocks hp hw decode hm gamma hg threshold
  let actual : ℚ := ∑ code : Fin (C + 1), if (decode code.val : ℝ) ≤ threshold then labelMass blocks code.val else 0
  have hCast : (actual : ℝ) = ∑ code : Fin (C + 1),
      if (decode code.val : ℝ) ≤ threshold then (labelMass blocks code.val : ℝ) else 0 := by
    unfold actual
    push_cast
    apply Finset.sum_congr rfl
    intro code _
    split_ifs <;> simp
  constructor
  · rw [← hCast]
    exact (Rat.cast_le (K := ℝ)).mpr he.1
  · rw [← hCast, ← Rat.cast_mul]
    exact (Rat.cast_le (K := ℝ)).mpr he.2

end ImplicitLeafCounts
end Blotto

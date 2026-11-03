import Blotto.ImplicitLeafUpperGuide

/-! Actual implicit upper-bin query visits. Prefix and inverse scans visit
stored blocks; weak/strict code queries use certified logarithmic comparisons.
The instrumented recursion refines the actual bins. Visits are not full rational
or finite-binary time; decoder, arithmetic and list allocation remain separate. -/

namespace Blotto.ImplicitLeafCounts

def upperBinEndWithVisits (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (gamma : ℚ) (start : ℕ) : ℕ × ℕ :=
  let strictCut := MonotoneResourceCuts.strict C decode (decode start)
  let endpoint := min C (strictCut.1 - 1)
  let cumulative := prefixMassWithVisits blocks (endpoint : ℤ)
  let target := gamma * cumulative.1
  let base := strictCut.2 + cumulative.2 + blocks.length
  if totalMass blocks ≤ target then (C, base) else
    let crossing := inverseWithVisits blocks target
    match crossing.1 with
    | none => (C, base + crossing.2)
    | some code =>
        let first := MonotoneResourceCuts.weak C decode (decode code)
        (first.1 - 1, base + crossing.2 + first.2)

theorem upperBinEndWithVisits_state (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (gamma : ℚ) (start : ℕ) :
    (upperBinEndWithVisits C blocks decode gamma start).1 = upperBinEnd C blocks decode gamma start := by
  unfold upperBinEndWithVisits upperBinEnd plateauEnd
  dsimp only
  rw [prefixMassWithVisits_refines]
  dsimp only
  split
  · rfl
  · change _ = match inverseStrict blocks (gamma * prefixMass blocks _ ) with
      | none => C | some crossing => (MonotoneResourceCuts.weak C decode (decode crossing)).1 - 1
    unfold inverseStrict
    cases h : (inverseWithVisits blocks (gamma * prefixMass blocks _)).1 <;> rfl

theorem upperBinEndWithVisits_bound (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (gamma : ℚ) (start : ℕ) :
    (upperBinEndWithVisits C blocks decode gamma start).2 ≤
      2 * binaryWordWidth (C + 1) + 3 * blocks.length := by
  have hs := MonotoneCodeSearch.first_visits C (MonotoneResourceCuts.strictPredicate decode (decode start))
  change (MonotoneResourceCuts.strict C decode (decode start)).2 ≤ _ at hs
  unfold upperBinEndWithVisits
  dsimp only
  rw [prefixMassWithVisits_refines]
  dsimp only
  split
  · omega
  · have hi := inverseWithVisits_bound blocks
      (gamma * prefixMass blocks ((min C ((MonotoneResourceCuts.strict C decode (decode start)).1 - 1) : ℕ) : ℤ))
    split
    · dsimp only
      omega
    · rename_i crossing hCross
      have hw := MonotoneCodeSearch.first_visits C (MonotoneResourceCuts.weakPredicate decode (decode crossing))
      change (MonotoneResourceCuts.weak C decode (decode crossing)).2 ≤ _ at hw
      dsimp only
      omega

def upperBinStepWithVisits (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (gamma : ℚ) (start : ℕ) : UpperBin × ℕ :=
  let endpoint := upperBinEndWithVisits C blocks decode gamma start
  let through := prefixMassWithVisits blocks (endpoint.1 : ℤ)
  let before := prefixMassWithVisits blocks ((start : ℤ) - 1)
  (⟨decode start, start, endpoint.1, through.1 - before.1⟩,
    endpoint.2 + through.2 + before.2)

theorem upperBinStepWithVisits_state (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (gamma : ℚ) (start : ℕ) :
    (upperBinStepWithVisits C blocks decode gamma start).1 = upperBinStep C blocks decode gamma start := by
  unfold upperBinStepWithVisits upperBinStep
  dsimp only
  rw [prefixMassWithVisits_refines, prefixMassWithVisits_refines, upperBinEndWithVisits_state]

theorem upperBinStepWithVisits_bound (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ)
    (gamma : ℚ) (start : ℕ) :
    (upperBinStepWithVisits C blocks decode gamma start).2 ≤
      2 * binaryWordWidth (C + 1) + 5 * blocks.length := by
  have he := upperBinEndWithVisits_bound C blocks decode gamma start
  unfold upperBinStepWithVisits
  dsimp only
  rw [prefixMassWithVisits_refines, prefixMassWithVisits_refines]
  dsimp only
  omega

def upperBinsWithVisits (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) (start : ℕ) : List UpperBin × ℕ :=
  if start ≤ C then
    let step := upperBinStepWithVisits C blocks decode gamma start
    if start ≤ step.1.hi then
      let later := upperBinsWithVisits C blocks decode gamma (step.1.hi + 1)
      (step.1 :: later.1, step.2 + later.2)
    else ([], step.2)
  else ([], 0)
termination_by C + 1 - start
decreasing_by
  simp_wf
  have _hs : start ≤ C := by assumption
  have hp : start ≤ (upperBinStepWithVisits C blocks decode gamma start).1.hi := by assumption
  omega

theorem upperBinsWithVisits_state (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (gamma : ℚ) (start : ℕ) :
    (upperBinsWithVisits C blocks decode gamma start).1 = upperBins C blocks decode gamma start := by
  rw [upperBinsWithVisits, upperBins]
  by_cases hs : start ≤ C
  · rw [ite_eq_left hs, ite_eq_left hs]
    dsimp only
    rw [upperBinStepWithVisits_state]
    split
    · rw [upperBinsWithVisits_state]
    · rfl
  · rw [ite_eq_right hs, ite_eq_right hs]
termination_by C + 1 - start
decreasing_by
  have _hp : start ≤ (upperBinStep C blocks decode gamma start).hi := by assumption
  omega

theorem upperBinsWithVisits_bound (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (gamma : ℚ) (hg : 1 ≤ gamma) (start : ℕ) :
    (upperBinsWithVisits C blocks decode gamma start).2 ≤
      (upperBins C blocks decode gamma start).length *
        (2 * binaryWordWidth (C + 1) + 5 * blocks.length) := by
  rw [upperBinsWithVisits, upperBins]
  by_cases hs : start ≤ C
  · rw [ite_eq_left hs, ite_eq_left hs]
    dsimp only
    have hStep := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hs
    have hProgress : start ≤ (upperBinStep C blocks decode gamma start).hi := hStep.1
    rw [upperBinStepWithVisits_state, ite_eq_left hProgress, ite_eq_left hProgress]
    dsimp only
    have hCall := upperBinStepWithVisits_bound C blocks decode gamma start
    have hLater := upperBinsWithVisits_bound C blocks hp hw decode hm gamma hg
      ((upperBinStep C blocks decode gamma start).hi + 1)
    simp only [List.length_cons]
    nlinarith
  · rw [ite_eq_right hs, ite_eq_right hs]
    simp
termination_by C + 1 - start
decreasing_by
  have _he := upperBinEnd_contract C blocks hp hw decode hm gamma hg start hs
  dsimp only [upperBinStep]
  omega

end Blotto.ImplicitLeafCounts

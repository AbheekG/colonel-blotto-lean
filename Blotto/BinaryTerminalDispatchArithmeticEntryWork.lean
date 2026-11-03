import Blotto.BinaryReflectedPrimitiveExtraWork
import Blotto.BinaryWordTerminalCompleteMeasured
import Blotto.BinarySmallUniformArithmeticEntryWork
import Blotto.BinaryGluingArithmeticEntryWork

/-! Reached optional four-variable root/guard/order and mixed-three emission
join uniform/mixed-two branches in complete cached terminal entry accounting.
The root's Boolean coin/canonicalization is outside the raw/comparison entry class. -/
namespace Blotto.BinaryTerminalDispatchArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 5000000

def afterRoot (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value) : ℕ :=
  match root.1.1.1 with
  | none => 0
  | some true => BinarySmallUniformArithmeticEntryWork.run store input hC hAd K scalar root.1.1.2 hNext
  | some false => BinaryReflectedWholeArithmeticEntryWork.draw store input hC hAd K outer scalar root.1.1.2 hNext

theorem afterRoot_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    afterRoot store input hC hAd K outer scalar root hNext ≤
      2*listCells (BinaryFourSmallMeasured.afterRoot store input hC hAd K outer scalar root hNext).1.2 := by
  have hu := BinarySmallUniformArithmeticEntryWork.run_bound store input hC hAd K scalar root.1.1.2 hNext
  have hr := BinaryReflectedWholeArithmeticEntryWork.draw_bound store input hC hAd K outer scalar root.1.1.2 hNext
  cases h : root.1.1.1 with
  | none => simp only [afterRoot,BinaryFourSmallMeasured.afterRoot_record,h]; omega
  | some branch => cases branch <;> simp only [afterRoot,BinaryFourSmallMeasured.afterRoot_record,h,
      wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def small (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  afterRoot store input hC hAd K outer scalar (BinaryFourSmallCoinMeasured.sample store input pc hp)
    (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2

theorem small_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    small store input hC hAd K outer scalar pc hp ≤ 2*listCells (BinaryFourSmallMeasured.run store input hC hAd K outer scalar pc hp).1.2 :=
  afterRoot_bound store input hC hAd K outer scalar _ _

def ordered (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  BinaryFourPreparationArithmeticEntryWork.guard input+
    if hg : (BinaryFourGuardMeasured.guard input).1.1 = true then
      have hOld : BinaryFourParentCompiler.gluingCase input = true := by
        rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
      BinaryGluingArithmeticEntryWork.run store input hC
        (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
    else
      have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
        rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
      small store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp

theorem ordered_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ordered store input hC hAd K outer scalar pc hp ≤ 2*listCells (BinaryFourOrderedMeasured.run store input hC hAd K outer scalar pc hp).1.2 := by
  have hg := BinaryFourPreparationArithmeticEntryWork.guard_bound input
  simp only [ordered,BinaryFourOrderedMeasured.run_record]
  split
  · rename_i hGuard
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hGuard
    have h := BinaryGluingArithmeticEntryWork.run_bound store input hC
      (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
    simp only [hGuard,dif_pos,BinaryFourOrderedMeasured.join,wrap,combine,listCells_append,listCells_under,listCells]; omega
  · rename_i hNot
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hNot
    have h := small_bound store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp
    simp only [hNot,dif_neg,BinaryFourOrderedMeasured.join,wrap,combine,listCells_append,listCells_under,listCells]; omega


def afterOrder (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (held : BinaryFourRestoredMeasured.Ordered)
    (hHeld : held.1.1=(BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  have hOC : held.1.1.1.Canonical := by rw [hHeld]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOA : BinaryFourAdmissibility.Admissible held.1.1.1 := by rw [hHeld]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  ordered store held.1.1.1 hOC hOA K outer scalar pc hp

def restored (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let held := BinaryFourOrderMeasured.ordered input
  BinaryFourPreparationArithmeticEntryWork.sort input.length.read+
    afterOrder store input hC hAd held ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans
      (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) K outer scalar pc hp

theorem restored_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    restored store input hC hAd K outer scalar pc hp ≤ 2*listCells (BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).1.2 := by
  let held := BinaryFourOrderMeasured.ordered input
  have hHeld : held.1.1=(BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input) :=
    (congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans (BinaryFourOrderLifetime.orderedWithTrace_erasure input)
  have hOC : held.1.1.1.Canonical := by rw [hHeld]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOA : BinaryFourAdmissibility.Admissible held.1.1.1 := by rw [hHeld]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  have ho := BinaryFourPreparationArithmeticEntryWork.ordered_bound input
  have hd := ordered_bound store held.1.1.1 hOC hOA K outer scalar pc hp
  dsimp only [held] at hd
  simp only [restored,afterOrder,BinaryFourRestoredMeasured.run_record,BinaryFourRestoredMeasured.afterOrder_record,BinaryFourRestoredMeasured.restore]
  split <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def mixedThree {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let drawn := BinaryFourRestoredMeasured.run store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  restored store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp+
    BinaryGroupArithmeticEntryWork.emitMixedOption routes pivot drawn.1.1.1

theorem mixedThree_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedThree store input hC hAd routes pivot K outer scalar pc hp ≤
      2*listCells (BinaryWordGroupCompleteMeasured.mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.2 := by
  have hd := restored_bound store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp
  have he := BinaryGroupArithmeticEntryWork.emitMixedOption_bound routes pivot
    (BinaryFourRestoredMeasured.run store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp).1.1.1
  simp only [mixedThree,BinaryWordGroupCompleteMeasured.mixedThreeRun_record,BinaryWordGroupCompleteMeasured.afterMixed_record,
    BinaryWordGroupCompleteMeasured.collect,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def drawTwo {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ := by
  subst m
  exact BinaryGroupArithmeticEntryWork.mixedTwoRun store input hC hAd routes pivot K scalar pc hp

theorem drawTwo_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawTwo store input hC hAd hCount routes pivot K scalar pc hp ≤
      2*listCells (BinaryWordTerminalCompleteMeasured.drawTwo store input hC hAd hCount routes pivot K scalar pc hp).1.2 := by
  subst m
  exact BinaryGroupArithmeticEntryWork.mixedTwoRun_bound store input hC hAd routes pivot K scalar pc hp

def drawThree {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ := by
  subst m
  exact mixedThree store input hC hAd routes pivot K outer scalar pc hp

theorem drawThree_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawThree store input hC hAd hCount routes pivot K outer scalar pc hp ≤
      2*listCells (BinaryWordTerminalCompleteMeasured.drawThree store input hC hAd hCount routes pivot K outer scalar pc hp).1.2 := by
  subst m
  exact mixedThree_bound store input hC hAd routes pivot K outer scalar pc hp

def terminal {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  match hPivot : prepared.pivot with
  | none => BinaryGroupArithmeticEntryWork.uniformRun store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
  | some selected =>
    if hTwo : prepared.count=2 then
      drawTwo store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot) hTwo prepared.routes selected K scalar pc hp
    else drawThree store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
      ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp

theorem terminal_bound {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    terminal store prepared hC hAd K outer scalar pc hp ≤
      2*listCells (BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2 := by
  rcases prepared with ⟨count,packing,totals,routes,pivot,ell,probability,work,hCount,hPack,hTotals,hRoutes,hPivot,hEll,hProb⟩
  cases pivot with
  | none =>
    let held : Prepared input := ⟨count,packing,totals,routes,none,ell,probability,work,hCount,hPack,hTotals,hRoutes,hPivot,hEll,hProb⟩
    have h := BinaryGroupArithmeticEntryWork.uniformRun_bound store held.uniform (held.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible held hC hAd rfl)
      (held.count_bound hC hAd) held.routes K scalar pc hp
    simpa only [held,terminal,BinaryWordTerminalCompleteMeasured.run_record,BinaryWordTerminalCompleteMeasured.branch,
      wrap,combine,listCells_append,listCells_under,listCells,Nat.add_zero,Nat.zero_add] using h
  | some selected =>
    let held : Prepared input := ⟨count,packing,totals,routes,some selected,ell,probability,work,hCount,hPack,hTotals,hRoutes,hPivot,hEll,hProb⟩
    by_cases hTwo : count=2
    · have h := drawTwo_bound store held.mixed (held.mixed_canonical hC selected rfl)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible held hC hAd selected rfl)
        hTwo held.routes selected K scalar pc hp
      simpa only [held,terminal,BinaryWordTerminalCompleteMeasured.run_record,dif_pos hTwo,BinaryWordTerminalCompleteMeasured.branch,
        wrap,combine,listCells_append,listCells_under,listCells,Nat.add_zero,Nat.zero_add] using h
    · have h := drawThree_bound store held.mixed (held.mixed_canonical hC selected rfl)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible held hC hAd selected rfl)
        ((held.count_bound hC hAd).resolve_left hTwo) held.routes selected K outer scalar pc hp
      simpa only [held,terminal,BinaryWordTerminalCompleteMeasured.run_record,dif_neg hTwo,BinaryWordTerminalCompleteMeasured.branch,
        wrap,combine,listCells_append,listCells_under,listCells,Nat.add_zero,Nat.zero_add] using h


end Blotto.BinaryTerminalDispatchArithmeticEntryWork

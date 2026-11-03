import Blotto.BinaryReflectedInitialExtraWork
import Blotto.BinaryWordTerminalCompleteMeasured
import Blotto.BinarySmallUniformArithmeticEntryWork
import Blotto.BinaryGluingArithmeticEntryWork

/-! The reached reflected branch carries its actual primitive extra work,
initial counter/build emission work and initial allocated-bit sum through the
optional ordered/restored/mixed-three and complete cached terminal interfaces.
Other branches add zero to this defined reflected-extra class. -/
namespace Blotto.BinaryTerminalReflectedExtraWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 5000000

def reflected (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let prepared := (BinaryReflectedPreparationMeasured.prepare input hC).1.1
  BinaryReflectedPrimitiveExtraWork.sourceExtra store prepared.capacity prepared.system.initial
    prepared.capacity_canonical prepared.canonical.2.2.2 pc hp+
    BinaryReflectedInitialExtraWork.drawInitialExtra input hC+BinaryReflectedInitialExtraWork.drawAllocated input hC

theorem reflected_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    reflected store input hC hAd K outer scalar pc hp ≤
      49*(BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar pc hp).2+
        35*(BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar pc hp).1.2.length+475 := by
  have hw := BinaryReflectedInitialExtraWork.drawTotal_bound store input hC hAd K outer scalar pc hp
  have hr := BinaryReflectedInitialExtraWork.drawTotal_record store input hC hAd K outer scalar pc hp
  have ha := (BinaryReflectedInitialExtraWork.draw_initial_bounds store input hC hAd K outer scalar pc hp).2
  dsimp only [BinaryReflectedInitialExtraWork.drawInitialExtra] at hr
  dsimp only [reflected,BinaryReflectedInitialExtraWork.drawInitialExtra]
  omega

def afterRoot (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value) : ℕ :=
  match root.1.1.1 with
  | none => 0
  | some true => 0
  | some false => reflected store input hC hAd K outer scalar root.1.1.2 hNext

theorem afterRoot_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    afterRoot store input hC hAd K outer scalar root hNext ≤
      49*(BinaryFourSmallMeasured.afterRoot store input hC hAd K outer scalar root hNext).2+35*(BinaryFourSmallMeasured.afterRoot store input hC hAd K outer scalar root hNext).1.2.length+475 := by
  have hr := reflected_bound store input hC hAd K outer scalar root.1.1.2 hNext
  cases h : root.1.1.1 with
  | none => simp only [afterRoot,BinaryFourSmallMeasured.afterRoot_record,h]; omega
  | some branch => cases branch <;> simp only [afterRoot,BinaryFourSmallMeasured.afterRoot_record,h,
      BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] <;> omega

def small (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  afterRoot store input hC hAd K outer scalar (BinaryFourSmallCoinMeasured.sample store input pc hp)
    (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2

theorem small_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    small store input hC hAd K outer scalar pc hp ≤ 49*(BinaryFourSmallMeasured.run store input hC hAd K outer scalar pc hp).2+35*(BinaryFourSmallMeasured.run store input hC hAd K outer scalar pc hp).1.2.length+475 :=
  afterRoot_bound store input hC hAd K outer scalar _ _

def ordered (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  if hg : (BinaryFourGuardMeasured.guard input).1.1 = true then
      have hOld : BinaryFourParentCompiler.gluingCase input = true := by
        rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
      0
    else
      have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
        rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hg
      small store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp

theorem ordered_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ordered store input hC hAd K outer scalar pc hp ≤ 49*(BinaryFourOrderedMeasured.run store input hC hAd K outer scalar pc hp).2+35*(BinaryFourOrderedMeasured.run store input hC hAd K outer scalar pc hp).1.2.length+475 := by
  simp only [ordered,BinaryFourOrderedMeasured.run_record]
  split
  · rename_i hGuard
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hGuard
    simp only [hGuard,dif_pos,BinaryFourOrderedMeasured.join,BinaryResourceTraceLength.wrap_length,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  · rename_i hNot
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hNot
    have h := small_bound store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp
    simp only [hNot,dif_neg,BinaryFourOrderedMeasured.join,BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; omega


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
  afterOrder store input hC hAd held ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans
      (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) K outer scalar pc hp

theorem restored_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    restored store input hC hAd K outer scalar pc hp ≤ 49*(BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).2+35*(BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).1.2.length+475 := by
  let held := BinaryFourOrderMeasured.ordered input
  have hHeld : held.1.1=(BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input) :=
    (congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans (BinaryFourOrderLifetime.orderedWithTrace_erasure input)
  have hOC : held.1.1.1.Canonical := by rw [hHeld]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOA : BinaryFourAdmissibility.Admissible held.1.1.1 := by rw [hHeld]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  have hd := ordered_bound store held.1.1.1 hOC hOA K outer scalar pc hp
  dsimp only [held] at hd
  simp only [restored,afterOrder,BinaryFourRestoredMeasured.run_record,BinaryFourRestoredMeasured.afterOrder_record,BinaryFourRestoredMeasured.restore]
  split <;> simp only [BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] <;> omega

def mixedThree {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  restored store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp

theorem mixedThree_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedThree store input hC hAd routes pivot K outer scalar pc hp ≤
      49*(BinaryWordGroupCompleteMeasured.mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).2+35*(BinaryWordGroupCompleteMeasured.mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.2.length+475 := by
  have hd := restored_bound store (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp
  simp only [mixedThree,BinaryWordGroupCompleteMeasured.mixedThreeRun_record,BinaryWordGroupCompleteMeasured.afterMixed_record,
    BinaryWordGroupCompleteMeasured.collect,BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

def drawTwo {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ := by
  subst m
  exact 0

theorem drawTwo_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawTwo store input hC hAd hCount routes pivot K scalar pc hp ≤
      49*(BinaryWordTerminalCompleteMeasured.drawTwo store input hC hAd hCount routes pivot K scalar pc hp).2+35*(BinaryWordTerminalCompleteMeasured.drawTwo store input hC hAd hCount routes pivot K scalar pc hp).1.2.length+475 := by
  subst m
  simp only [drawTwo]; omega

def drawThree {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ := by
  subst m
  exact mixedThree store input hC hAd routes pivot K outer scalar pc hp

theorem drawThree_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hCount : m=3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawThree store input hC hAd hCount routes pivot K outer scalar pc hp ≤
      49*(BinaryWordTerminalCompleteMeasured.drawThree store input hC hAd hCount routes pivot K outer scalar pc hp).2+35*(BinaryWordTerminalCompleteMeasured.drawThree store input hC hAd hCount routes pivot K outer scalar pc hp).1.2.length+475 := by
  subst m
  exact mixedThree_bound store input hC hAd routes pivot K outer scalar pc hp

def terminal {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  match hPivot : prepared.pivot with
  | none => 0
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
      49*(BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).2+35*(BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2.length+475 := by
  rcases prepared with ⟨count,packing,totals,routes,pivot,ell,probability,work,hCount,hPack,hTotals,hRoutes,hPivot,hEll,hProb⟩
  cases pivot with
  | none =>
    let held : Prepared input := ⟨count,packing,totals,routes,none,ell,probability,work,hCount,hPack,hTotals,hRoutes,hPivot,hEll,hProb⟩
    simp only [terminal,BinaryWordTerminalCompleteMeasured.run_record,BinaryWordTerminalCompleteMeasured.branch]
    omega
  | some selected =>
    let held : Prepared input := ⟨count,packing,totals,routes,some selected,ell,probability,work,hCount,hPack,hTotals,hRoutes,hPivot,hEll,hProb⟩
    by_cases hTwo : count=2
    · have h := drawTwo_bound store held.mixed (held.mixed_canonical hC selected rfl)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible held hC hAd selected rfl)
        hTwo held.routes selected K scalar pc hp
      simp only [held,terminal,BinaryWordTerminalCompleteMeasured.run_record,dif_pos hTwo,BinaryWordTerminalCompleteMeasured.branch,
        BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.zero_add] at h ⊢
      omega
    · have h := drawThree_bound store held.mixed (held.mixed_canonical hC selected rfl)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible held hC hAd selected rfl)
        ((held.count_bound hC hAd).resolve_left hTwo) held.routes selected K outer scalar pc hp
      simp only [held,terminal,BinaryWordTerminalCompleteMeasured.run_record,dif_neg hTwo,BinaryWordTerminalCompleteMeasured.branch,
        BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.zero_add] at h ⊢
      omega


end Blotto.BinaryTerminalReflectedExtraWork

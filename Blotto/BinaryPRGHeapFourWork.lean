import Blotto.BinaryPRGHeapReflectedWork

/-! Ordered and restored four-coordinate callers reach the physical reflected
draw on their small branch. Exact outputs/cursors and an additive physical
setup-price comparison cover root exhaustion, both regimes and restoration. -/

namespace Blotto.BinaryPRGHeapFourWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerFourWork (root root_erasure uniformRun uniformRun_erasure gluingRun gluingRun_erasure)

def smallRun (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.Result store × ℕ :=
  let chosen := root store input pc hp
  have hPosition : chosen.1.2.value ≤ store.cap.value := by
    rw [root_erasure]
    exact (BinaryPRGWordControllerDataCoin.sample_position store
      (BinaryPRGWordControllerFour.probability input) pc hp).2
  match chosen.1.1 with
  | none => ((none,chosen.1.2),chosen.2 + 2)
  | some true =>
      let drawn := uniformRun store input hC hAd K scalar chosen.1.2 hPosition
      (drawn.1,chosen.2 + drawn.2 + 2)
  | some false =>
      let drawn := BinaryPRGHeapReflectedWork.run store input hC hAd K outer scalar chosen.1.2 hPosition
      (drawn.1,chosen.2 + drawn.2 + 2)

theorem smallRun_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (smallRun store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp := by
  unfold smallRun BinaryPRGWordControllerFour.smallRun
  dsimp only
  simp only [root_erasure]
  split
  · rename_i hNone; simp only [hNone]
  · rename_i hTrue; simp only [hTrue]; exact uniformRun_erasure _ _ _ _ _ _ _ _
  · rename_i hFalse; simp only [hFalse]; exact BinaryPRGHeapReflectedWork.run_erasure _ _ _ _ _ _ _ _ _

theorem smallRun_cost_le (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinarySmallRootSample.Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (smallRun store input hC hAd K outer scalar pc hp).2 ≤
      (BinaryPRGWordControllerFourWork.smallRun store input hC hAd K outer scalar pc hp).2 +
        BinaryPRGHeapReflectedSetup.bound s store.width store.cap.value := by
  have hPosition : (root store input pc hp).1.2.value ≤ store.cap.value := by
    rw [root_erasure]
    exact (BinaryPRGWordControllerDataCoin.sample_position store
      (BinaryPRGWordControllerFour.probability input) pc hp).2
  have hCompare := (BinaryPRGHeapReflectedWork.run_compare store input hC hAd K outer scalar
    (root store input pc hp).1.2 hPosition).2
  have hSetup := BinaryPRGHeapReflectedSetup.run_bound store input source hC hR hCase s hs hH
    (root store input pc hp).1.2 hPosition
  unfold smallRun BinaryPRGWordControllerFourWork.smallRun
  dsimp only
  cases hRoot : (root store input pc hp).1.1 with
  | none => dsimp only; omega
  | some branch => cases branch <;> dsimp only <;> omega

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.Result store × ℕ :=
  let guard := BinaryFourNativeOrderWork.guardWithWork input
  if hg : guard.1 = true then
    let drawn := gluingRun store input hC (BinaryFourAdmissibility.gluing_guard input hC hAd
      ((BinaryFourNativeOrderWork.guardWithWork_state input).symm.trans hg)) K scalar pc hp
    (drawn.1,guard.2 + drawn.2 + 2)
  else
    let drawn := smallRun store input hC (BinaryFourAdmissibility.small_guard input hC hAd
      (fun h => hg ((BinaryFourNativeOrderWork.guardWithWork_state input).trans h))) K outer scalar pc hp
    (drawn.1,guard.2 + drawn.2 + 2)

set_option maxHeartbeats 800000 in
theorem run_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerFour.run store input hC hAd K outer scalar pc hp := by
  unfold run BinaryPRGWordControllerFour.run
  dsimp only
  simp only [BinaryFourNativeOrderWork.guardWithWork_state]
  split
  · simp only
    exact gluingRun_erasure _ _ _ _ _ _ _ _
  · simp only
    exact smallRun_erasure _ _ _ _ _ _ _ _ _

theorem run_cost_le (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤
      (BinaryPRGWordControllerFourWork.run store input hC hAd K outer scalar pc hp).2 +
        BinaryPRGHeapReflectedSetup.bound s store.width store.cap.value := by
  unfold run BinaryPRGWordControllerFourWork.run
  dsimp only
  split
  · omega
  · rename_i hg
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := fun h => hg
      ((BinaryFourNativeOrderWork.guardWithWork_state input).trans h)
    have hCase : source.w < (1 - source.p) * source.ell := lt_of_not_ge (fun h => hOld
      ((BinaryFourParentCompiler.gluingCase_iff input source hC hR).mpr h))
    have hSmall := smallRun_cost_le store input source hC hR
      (BinaryFourAdmissibility.small_guard input hC hAd hOld) hCase s hs hH K outer scalar pc hp
    omega

def restoredRun (store : Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.Result store × ℕ :=
  let ordered := BinaryFourSpecRetainedWork.prepareOrdered input hC hAd
  let drawn := run store ordered.ordered ordered.canonical ordered.admissible K outer scalar pc hp
  match drawn.1.1 with
  | none => ((none,drawn.1.2),ordered.orderWork + drawn.2 + 2)
  | some row =>
      ((some (FixedArrayTable.ofFn (fun j => row.read (BinaryFourSpecSampler.permutation input j))),drawn.1.2),
        5 * ordered.orderWork + drawn.2 + 20)

theorem restoredRun_erasure (store : Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (restoredRun store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp := by
  unfold restoredRun BinaryPRGWordControllerFour.restoredRun
  dsimp only
  rw [run_erasure]
  have hOrdered := (BinaryFourSpecRetainedWork.prepareOrdered input hC hAd).ordered_correct
  simp only [hOrdered]
  split
  · rename_i hNone; simp only [hNone,Option.map_none]
  · rename_i row hRow; simp only [hRow,Option.map_some]

theorem restoredRun_cost_le (store : Store) (input : BinaryFourSpecSampler.Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (restoredRun store input hC hAd K outer scalar pc hp).2 ≤
      (BinaryPRGWordControllerFourWork.restoredRun store input hC hAd K outer scalar pc hp).2 +
        BinaryPRGHeapReflectedSetup.bound s store.width store.cap.value := by
  let ordered := BinaryFourSpecRetainedWork.prepareOrdered input hC hAd
  have hRef : ordered.ordered.Refines source.input := by
    rw [ordered.ordered_correct]
    exact BinaryFourSpecSampler.orderedInput_refines input source hC hR
  have hCost := run_cost_le store ordered.ordered source.input ordered.canonical hRef ordered.admissible
    s hs hH.input K outer scalar pc hp
  have hData := (run_erasure store ordered.ordered ordered.canonical ordered.admissible K outer scalar pc hp).trans
    (BinaryPRGWordControllerFourWork.run_erasure store ordered.ordered ordered.canonical ordered.admissible
      K outer scalar pc hp).symm
  unfold restoredRun BinaryPRGWordControllerFourWork.restoredRun
  dsimp only
  dsimp only [ordered] at hData hCost
  simp only [hData]
  cases (BinaryPRGWordControllerFourWork.run store
    (BinaryFourSpecRetainedWork.prepareOrdered input hC hAd).ordered
    (BinaryFourSpecRetainedWork.prepareOrdered input hC hAd).canonical
    (BinaryFourSpecRetainedWork.prepareOrdered input hC hAd).admissible K outer scalar pc hp).1.1
  <;> dsimp only <;> omega

end Blotto.BinaryPRGHeapFourWork

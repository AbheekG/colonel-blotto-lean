import Blotto.BinaryPRGHeapReflectedSetup
import Blotto.BinaryPRGWordControllerFourWork

/-! The complete reflected selector and emission consume the physical setup
result. A work comparison keeps the extra physical price explicit while exact
native output and cursor equality preserve the retained continuation proofs. -/

namespace Blotto.BinaryPRGHeapReflectedWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryReflectedFourSetup BinaryReflectedSerialRun
open BinaryPRGWordControllerReflectedWork (profileWithWork profileWithWork_state emissionWithWork)

def select (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : Admissible input) (K : ℕ) (outer : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerReflected.Selection store input × ℕ :=
  let reached := BinaryPRGHeapReflectedSetup.run store input hC pc hp
  match hResult : reached.1.1 with
  | none => ((none,reached.1.2),reached.2 + 2)
  | some result =>
      have hReached : (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 = some result :=
        (congrArg Prod.fst (BinaryPRGHeapReflectedSetup.run_erasure store input hC pc hp)).symm.trans hResult
      let table := profileWithWork input result.state K outer
      have hTable := profileWithWork_state input result.state K outer
      have hTableC : table.1.Canonical := by
        rw [hTable]
        exact BinaryTerminalProfileCompiler.profile_canonical
          _ result.state (prepare_canonical input hC) result.canonical K outer
      have hNonnegative : ∀ slot,0 ≤ value (table.1.weight.read slot) := by
        rw [hTable]
        exact profile_nonnegative input hC hAd (store.cap.value - pc.value)
          (BinaryPRGWordControllerReflected.localReader store pc hp) result
          (BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result hReached) K outer
      have hPosition : reached.1.2.value ≤ store.cap.value := by
        rw [BinaryPRGHeapReflectedSetup.run_erasure]
        exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2
      let selected := BinaryPRGWordControllerCategorical.run store (0 : Fin 18)
        (NativeBinarySegmentSampler.weights table.1 hTableC hNonnegative) reached.1.2 hPosition
      ((selected.1.1.map (fun slot => (result,slot)),selected.1.2),
        reached.2 + table.2 + selected.2 + 56)

theorem select_compare (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : Admissible input) (K : ℕ) (outer : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (select store input hC hAd K outer pc hp).1 =
        (BinaryPRGWordControllerReflectedWork.select store input hC hAd K outer pc hp).1 ∧
      (select store input hC hAd K outer pc hp).2 +
        (BinaryPRGWordControllerReflectedSetupWork.run store input hC pc hp).2 =
      (BinaryPRGWordControllerReflectedWork.select store input hC hAd K outer pc hp).2 +
        (BinaryPRGHeapReflectedSetup.run store input hC pc hp).2 := by
  have hData := (BinaryPRGHeapReflectedSetup.run_erasure store input hC pc hp).trans
    (BinaryPRGWordControllerReflectedSetupWork.run_erasure store input hC pc hp).symm
  have hOption := congrArg Prod.fst hData
  have hPC := congrArg Prod.snd hData
  unfold select BinaryPRGWordControllerReflectedWork.select
  dsimp only
  split
  · rename_i hNone
    have hOld := hOption.symm.trans hNone
    split
    · exact ⟨congrArg (fun p => (none,p)) hPC,by omega⟩
    · rename_i result hOther
      cases hOld.symm.trans hOther
  · rename_i result hSome
    have hOld := hOption.symm.trans hSome
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he : result = other := Option.some.inj (hOld.symm.trans hOther)
      subst other
      simp only [hPC]
      exact ⟨trivial,by omega⟩

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerReflected.Result store × ℕ :=
  let selected := select store input hC hAd K outer pc hp
  match selected.1.1 with
  | none => ((none,selected.1.2),selected.2 + 2)
  | some pair =>
      let emitted := emissionWithWork input pair.1.state K outer scalar pair.2
      ((some emitted.1,selected.1.2),selected.2 + emitted.2 + 2)

theorem run_compare (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1 =
        (BinaryPRGWordControllerReflectedWork.run store input hC hAd K outer scalar pc hp).1 ∧
      (run store input hC hAd K outer scalar pc hp).2 +
        (BinaryPRGWordControllerReflectedSetupWork.run store input hC pc hp).2 =
      (BinaryPRGWordControllerReflectedWork.run store input hC hAd K outer scalar pc hp).2 +
        (BinaryPRGHeapReflectedSetup.run store input hC pc hp).2 := by
  obtain ⟨hData,hWork⟩ := select_compare store input hC hAd K outer pc hp
  unfold run BinaryPRGWordControllerReflectedWork.run
  dsimp only
  simp only [hData]
  cases (BinaryPRGWordControllerReflectedWork.select store input hC hAd K outer pc hp).1.1
  <;> dsimp only
  <;> exact ⟨rfl,by omega⟩

theorem run_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar pc hp :=
  (run_compare store input hC hAd K outer scalar pc hp).1.trans
    (BinaryPRGWordControllerReflectedWork.run_erasure store input hC hAd K outer scalar pc hp)

def bound (s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGWordControllerReflectedWork.bound s K indexWidth seedCap +
    BinaryPRGHeapReflectedSetup.bound s indexWidth seedCap

theorem run_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1 - source.p) * source.ell) (hAd : Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ bound s K store.width store.cap.value := by
  have hOld := (BinaryPRGWordControllerReflectedWork.run_bound
    store input source hC hR hCase hAd s hs hH K outer scalar pc hp).trans
      (BinaryPRGWordControllerFourWork.reflectedBound_span_mono s K store.width (Nat.sub_le _ _))
  have hSetup := BinaryPRGHeapReflectedSetup.run_bound store input source hC hR hCase s hs hH pc hp
  have hCompare := (run_compare store input hC hAd K outer scalar pc hp).2
  unfold bound
  omega

end Blotto.BinaryPRGHeapReflectedWork

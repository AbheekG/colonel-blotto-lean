import Blotto.BinaryPRGWordControllerTerminal
import Blotto.BinaryPRGWordControllerResource
import Blotto.BinaryPRGCachedPrimitiveRun
import Blotto.BinaryOverlapInputPreparation

/-! A prepared original-game request keeps a single concrete Boolean seed
store and absolute Boolean counter through the complete resource and terminal
draw. All old outcomes and positions are preserved. The execution of factories,
routes and array access retains its separately declared backend obligations. -/

namespace Blotto.BinaryPRGWordControllerRequest
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGResourceWork BinaryPRGResourceHandoff BinaryPRGTerminalWork

abbrev Result (store : Store) (n : ℕ) := BinaryPRGWordControllerTerminal.Result store n
abbrev decoded {n : ℕ} (store : Store) := @BinaryPRGWordControllerTerminal.decoded n store

theorem resource_position {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) :
    (BinaryPRGWordControllerResource.requestRun store request rich).2.value ≤ store.cap.value := by
  have h := congrArg Prod.snd (BinaryPRGWordControllerResource.requestRun_state store request rich)
  change (BinaryPRGWordControllerResource.requestRun store request rich).2.value = _ at h
  rw [h]
  exact resourceWork_position _ _ _ _

theorem resource_terminal_admissible {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (hState : (BinaryPRGWordControllerResource.requestRun store request rich).1 = some state) :
    BinaryTerminalPromises.Admissible (terminalInput request rich state) := by
  have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state store request rich)
  change (BinaryPRGWordControllerResource.requestRun store request rich).1 = _ at h
  exact terminal_admissible request rich store.cap.value
    (BinaryWordIndexCoinController.reader store) state (h.symm.trans hState)

def run {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) : Result store n :=
  let observed := BinaryPRGWordControllerResource.requestRun store request rich
  match hs : observed.1 with
  | none => (none, observed.2)
  | some state =>
      let input := terminalInput request rich state
      let prepared := BinaryCachedTerminalPreparation.prepare input
      BinaryPRGWordControllerTerminal.runPrepared store prepared (terminal_canonical request rich state)
        (resource_terminal_admissible store request rich state hs) K outer scalar observed.2
        (resource_position store request rich)

theorem run_state {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    decoded store (run store request rich K outer scalar) =
      (BinaryPRGCachedPrimitiveRun.run request rich K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store)).1 := by
  have hState : (BinaryPRGWordControllerResource.requestRun store request rich).1 =
      (resourceWork request rich store.cap.value (BinaryWordIndexCoinController.reader store)).1.1 :=
    congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state store request rich)
  have hPosition : (BinaryPRGWordControllerResource.requestRun store request rich).2.value =
      (resourceWork request rich store.cap.value (BinaryWordIndexCoinController.reader store)).1.2 :=
    congrArg Prod.snd (BinaryPRGWordControllerResource.requestRun_state store request rich)
  unfold run BinaryPRGCachedPrimitiveRun.run
  dsimp only
  split
  · rename_i hNone
    have hOld := hState.symm.trans hNone
    split
    · exact congrArg (fun p => (none, p)) hPosition
    · rename_i state hOther
      cases hOld.symm.trans hOther
  · rename_i state hSome
    have hOld := hState.symm.trans hSome
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he : state = other := Option.some.inj (hOld.symm.trans hOther)
      subst other
      apply (BinaryPRGWordControllerTerminal.runPrepared_state store
        (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))
        (terminal_canonical request rich state)
        (resource_terminal_admissible store request rich state hSome) K outer scalar
        (BinaryPRGWordControllerResource.requestRun store request rich).2
        (resource_position store request rich)).trans
      simp only [BinaryCachedTerminalPrimitiveRun.runPrepared_state, hPosition]

theorem run_position {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).2.value ≤ store.cap.value := by
  have h := congrArg Prod.snd (run_state store request rich K outer scalar)
  change (run store request rich K outer scalar).2.value = _ at h
  rw [h, BinaryPRGCachedPrimitiveRun.run_state]
  exact BinaryPRGResourceHandoff.run_position _ _ _ _ _ _ _

def fixedSample {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) : FixedArrayTable n SignedWord :=
  (run store request rich K outer scalar).1.getD (BinaryLottoSampler.fallback (resourceInput request rich))

theorem fixedSample_state {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    fixedSample store request rich K outer scalar =
      (BinaryPRGCachedPrimitiveRun.fixedSample request rich K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store)).1 := by
  have h := congrArg Prod.fst (run_state store request rich K outer scalar)
  exact congrArg (fun result => result.getD (BinaryLottoSampler.fallback (resourceInput request rich))) h

theorem fixedSample_canonical {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    ∀ j, CanonicalWord ((fixedSample store request rich K outer scalar).read j) := by
  rw [fixedSample_state, BinaryPRGCachedPrimitiveRun.fixedSample_state]
  exact BinaryPRGResourceHandoff.fixedSample_canonical _ _ _ _ _ _ _

theorem fixedSample_fullBudget {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    FullBudget (value (resourceInput request rich).budget : ℝ)
      (fun j => (value ((fixedSample store request rich K outer scalar).read j) : ℝ)) := by
  rw [fixedSample_state, BinaryPRGCachedPrimitiveRun.fixedSample_state]
  exact BinaryPRGResourceHandoff.fixedSample_fullBudget _ _ _ _ _ _ _

def originalFixedSample {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) (K : ℕ) (outer scalar : Fin K → Bool) : FixedArrayTable n SignedWord :=
  let normalized := fixedSample store request rich K outer scalar
  FixedArrayTable.ofFn (fun j => BinaryQuadraticData.apply .mul request.prepared.original.a (normalized.read j))

theorem originalFixedSample_state {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) (K : ℕ) (outer scalar : Fin K → Bool) :
    originalFixedSample store request rich K outer scalar =
      BinaryPRGOriginalSampler.rescale request.prepared.original.a
        (BinaryPRGResourceHandoff.fixedSample request rich K store.cap.value outer scalar
          (BinaryWordIndexCoinController.reader store)).1 := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [originalFixedSample, BinaryPRGOriginalSampler.rescale, FixedArrayTable.read_ofFn]
  rw [← BinaryQuadraticData.apply_erasure,
    BinaryQuadraticOpcode.applyWithWork_state _ _ _ request.valid.2.1.1.1
      (fixedSample_canonical store request rich K outer scalar j).1]
  rw [fixedSample_state, BinaryPRGCachedPrimitiveRun.fixedSample_state]

theorem reader_ofFn {N : ℕ} (bits : Fin N → Bool)
    (j : Fin (prepare (List.ofFn bits)).cap.value) :
    BinaryWordIndexCoinController.reader (prepare (List.ofFn bits)) j =
      bits ⟨j.val, by simpa only [cap_value, List.length_ofFn] using j.isLt⟩ := by
  rw [BinaryWordIndexCoinController.reader_prepare]
  have hj : j.val < N := by simpa only [cap_value, List.length_ofFn] using j.isLt
  simp [List.getD_eq_getElem?_getD, hj]

theorem reader_transport {N M : ℕ} (h : N = M) (bits : Fin M → Bool) :
    HEq (fun j : Fin N => bits (j.cast h)) bits := by
  subst M
  rfl

theorem fixedSample_count_congr {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N M : ℕ) (outer scalar : Fin K → Bool) (first : Fin N → Bool) (second : Fin M → Bool)
    (hCount : N = M) (hBits : HEq first second) :
    (BinaryPRGResourceHandoff.fixedSample request rich K N outer scalar first).1 =
      (BinaryPRGResourceHandoff.fixedSample request rich K M outer scalar second).1 := by
  subst M
  cases hBits
  rfl

def vectorFixedSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable n SignedWord :=
  fixedSample (prepare (List.ofFn bits)) request rich K outer scalar

theorem vectorFixedSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    vectorFixedSample request rich K N outer scalar bits =
      (BinaryPRGResourceHandoff.fixedSample request rich K N outer scalar bits).1 := by
  have h := fixedSample_state (prepare (List.ofFn bits)) request rich K outer scalar
  rw [BinaryPRGCachedPrimitiveRun.fixedSample_state] at h
  have hCap : (prepare (List.ofFn bits)).cap.value = N := by rw [cap_value, List.length_ofFn]
  have hReader : BinaryWordIndexCoinController.reader (prepare (List.ofFn bits)) =
      fun j => bits (j.cast hCap) := by
    funext j
    exact (reader_ofFn bits j).trans (congrArg bits (Fin.ext rfl))
  exact h.trans (fixedSample_count_congr request rich K _ N outer scalar _ bits hCap
    ((heq_of_eq hReader).trans (reader_transport hCap bits)))

def sample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let outer := secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  vectorFixedSample request rich K (RationalLottoResourceSystem.coinBitBudget n K) outer
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)

theorem sample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    sample request rich K bits = (BinaryPRGResourceHandoff.sample request rich K bits).1 :=
  vectorFixedSample_state _ _ _ _ _ _ _

def originalSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FixedArrayTable n SignedWord :=
  let normalized := sample request rich request.precision bits
  FixedArrayTable.ofFn (fun j => BinaryQuadraticData.apply .mul request.prepared.original.a (normalized.read j))

theorem originalSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    originalSample request rich bits = (BinaryPRGResourceHandoff.originalSample request rich bits).1 := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [originalSample, BinaryPRGResourceHandoff.originalSample, BinaryPRGOriginalSampler.rescale,
    FixedArrayTable.read_ofFn]
  have hC : CanonicalWord ((sample request rich request.precision bits).read j) := by
    rw [sample_state]
    exact BinaryPRGResourceHandoff.fixedSample_canonical _ _ _ _ _ _ _ j
  rw [← BinaryQuadraticData.apply_erasure,
    BinaryQuadraticOpcode.applyWithWork_state _ _ _ request.valid.2.1.1.1 hC.1,
    sample_state]

theorem originalSample_fullBudget {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FullBudget (if rich then (value request.prepared.original.a : ℝ) else (value request.prepared.original.b : ℝ))
      (fun j => (value ((originalSample request rich bits).read j) : ℝ)) := by
  rw [originalSample_state]
  exact BinaryPRGResourceHandoff.originalSample_fullBudget _ _ _

noncomputable def law {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n request.precision)).map
    (fun bits j => (value ((originalSample request rich bits).read j) : ℝ))

theorem law_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    law request rich = BinaryPRGResourceHandoff.law request rich := by
  have h : (fun bits j => (value ((originalSample request rich bits).read j) : ℝ)) =
      fun bits j => (value ((BinaryPRGResourceHandoff.originalSample request rich bits).1.read j) : ℝ) := by
    funext bits j
    rw [originalSample_state]
  unfold law BinaryPRGResourceHandoff.law
  rw [h]

theorem law_regrets {n : ℕ} (request : BinaryPRGRequest.Request n) :
    regret request.source.realValues (request.source.a : ℝ) (law request true) (law request false) <
      request.accuracy.numeric.real ∧
    regret request.source.realValues (request.source.b : ℝ) (law request false) (law request true) <
      request.accuracy.numeric.real := by
  rw [law_state, law_state]
  exact BinaryPRGResourceHandoff.law_regrets request

end Blotto.BinaryPRGWordControllerRequest

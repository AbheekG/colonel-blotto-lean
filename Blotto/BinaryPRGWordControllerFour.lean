import Blotto.BinaryPRGWordControllerSegment
import Blotto.BinaryPRGWordControllerReflected
import Blotto.BinaryFourSpecPartialRun

/-! The complete ordered and restored four controller retains one seed Store,
cap and absolute Boolean counter through root, gluing, uniform and reflected
branches. Numeric offsets/windows occur solely in exact old-byte refinement.
Quadratic interpolation/probability normalization execute data-only; source
factories and metadata retain their separate existing contracts. -/

namespace Blotto.BinaryPRGWordControllerFour
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding

abbrev Result (store : Store) := BinaryPRGWordControllerSegment.Result store 4
abbrev decoded (store : Store) := @BinaryPRGWordControllerSegment.decoded 4 store

def probability (input : BinaryFourParameters.Input) : SignedWord :=
  BinaryQuadraticData.canonicalize input.p

theorem probability_state (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    probability input = BinarySmallRootSample.probability input := by
  rw [probability,← BinaryQuadraticData.canonicalize_erasure,
    BinaryQuadraticNormalization.canonicalizeWithWork_state input.p hC.2.2.2.2.2.1]
  rfl

def uniformPrepared (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) : BinaryStoredSegmentProgram.Prepared 4 9 :=
  ⟨BinarySmallUniformCompiler.fromOriginal input,BinarySmallUniformCompiler.fromOriginal_canonical input hC,
    BinarySmallRootSample.uniform_nonnegative input hC hAd⟩

def smallRun (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  let root := BinaryPRGWordControllerDataCoin.sample store (probability input) pc hp
  match root.1 with
  | none => (none,root.2)
  | some true => BinaryPRGWordControllerSegment.run store (uniformPrepared input hC hAd) 0 K scalar root.2
      (BinaryPRGWordControllerDataCoin.sample_position store (probability input) pc hp).2
  | some false => BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar root.2
      (BinaryPRGWordControllerDataCoin.sample_position store (probability input) pc hp).2

theorem window_heq (N M base : ℕ) (hSize : N = base + M)
    (bits : Fin N → Bool) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index = bits ⟨base + index.val,by rw [hSize]; omega⟩)
    (pos localPos count otherCount : ℕ) (hPos : pos = base + localPos) (hCount : count = otherCount)
    (hp : pos + count ≤ N) (hlp : localPos + otherCount ≤ M) :
    HEq (WordStateMachine.inputWindow bits pos count hp)
      (WordStateMachine.inputWindow localBits localPos otherCount hlp) := by
  subst otherCount
  apply heq_of_eq
  funext index
  unfold WordStateMachine.inputWindow
  rw [hBits ⟨localPos + index.val,by omega⟩]
  congr 1
  apply Fin.ext
  dsimp only
  omega

theorem cachedReader_congr (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K N M : ℕ) (outer scalar : Fin K → Bool)
    (bits : Fin N → Bool) (other : Fin M → Bool) (hSize : N = M) (hBits : HEq bits other) :
    BinaryReflectedCachedRun.run input hC hAd K N outer scalar bits =
      BinaryReflectedCachedRun.run input hC hAd K M outer scalar other := by
  subst M
  cases hBits
  rfl

theorem reflected_offset (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K N M base : ℕ) (hSize : N = base + M)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index = bits ⟨base + index.val,by rw [hSize]; omega⟩)
    (pos localPos : ℕ) (hp : pos ≤ N) (hlp : localPos ≤ M) (hPos : pos = base + localPos) :
    BinaryReflectedIndexedRun.run input hC hAd K N outer scalar bits pos hp =
      WordStateMachine.offsetConsumed base
        (BinaryReflectedIndexedRun.run input hC hAd K M outer scalar localBits localPos hlp) := by
  have hRemaining : N - pos = M - localPos := by omega
  have hWindow := window_heq N M base hSize bits localBits hBits pos localPos
    (N - pos) (M - localPos) hPos hRemaining (by omega) (by omega)
  have hRun := cachedReader_congr input hC hAd K (N - pos) (M - localPos) outer scalar _ _ hRemaining hWindow
  unfold BinaryReflectedIndexedRun.run
  dsimp only
  rw [hRun]
  simp only [WordStateMachine.offsetConsumed]
  apply Prod.ext
  · rfl
  · omega

set_option maxHeartbeats 1000000 in
theorem smallRun_state (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (smallRun store input hC hAd K outer scalar pc hp) =
      WordStateMachine.offsetConsumed pc.value (BinarySmallRootSample.run input hC hAd K
        (store.cap.value - pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value - pc.value) (by omega))) := by
  let M := store.cap.value - pc.value
  let localBits := WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value M (by omega)
  let root := BinaryPRGWordControllerDataCoin.sample store (probability input) pc hp
  let oldRoot := BinaryStoredCoinIndexed.sample (BinarySmallRootSample.probability input) M localBits 0 (Nat.zero_le M)
  have hRoot : (root.1,root.2.value) = WordStateMachine.offsetConsumed pc.value oldRoot := by
    have h := (BinaryPRGWordControllerDataCoin.sample_contract store (probability input) pc hp).1
    have ho := BinaryPRGWordControllerWindow.coinSample_offset store.cap.value M pc.value (by dsimp [M]; omega)
      (BinaryWordIndexCoinController.reader store) localBits (by intro index; rfl) (probability input)
      pc.value 0 hp (Nat.zero_le M) (by omega)
    have joined := h.trans ho
    simpa only [probability_state input hC,root,oldRoot] using joined
  have hOption : root.1 = oldRoot.1 := congrArg Prod.fst hRoot
  have hPosition : root.2.value = pc.value + oldRoot.2 := congrArg Prod.snd hRoot
  have hpNew := (BinaryPRGWordControllerDataCoin.sample_position store (probability input) pc hp).2
  have hpOld := (BinaryStoredCoinIndexed.sample_position (BinarySmallRootSample.probability input)
    (BinarySmallRootSample.probability_valid input hC) (BinarySmallRootSample.probability_unit input hC hAd)
    M localBits 0 (Nat.zero_le M)).2
  unfold smallRun BinarySmallRootSample.run
  dsimp only
  change decoded store (match root.1 with
    | none => (none,root.2)
    | some true => BinaryPRGWordControllerSegment.run store (uniformPrepared input hC hAd) 0 K scalar root.2 hpNew
    | some false => BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar root.2 hpNew) =
      WordStateMachine.offsetConsumed pc.value (match oldRoot.1 with
        | none => (none,oldRoot.2)
        | some branch => if h : oldRoot.2 ≤ M then
            if branch then BinarySmallRootSample.uniformRun input hC hAd K M scalar localBits oldRoot.2 h
            else BinaryReflectedIndexedRun.run input hC hAd K M outer scalar localBits oldRoot.2 h
          else (none,oldRoot.2))
  cases hc : root.1 with
  | none => simp only [← hOption,hc,WordStateMachine.offsetConsumed]; exact congrArg (fun p => (none,p)) hPosition
  | some branch =>
      simp only [← hOption,hc]
      cases branch
      · simp only [Bool.false_eq_true,ite_false]
        split
        · exact (BinaryPRGWordControllerReflected.run_state store input hC hAd K outer scalar root.2 hpNew).trans
            (reflected_offset input hC hAd K store.cap.value M pc.value (by dsimp [M]; omega)
              outer scalar (BinaryWordIndexCoinController.reader store) localBits (by intro index; rfl)
              root.2.value oldRoot.2 hpNew hpOld hPosition)
        · rename_i hFail
          exact False.elim (hFail hpOld)
      · simp only [ite_true]
        split
        · exact BinaryPRGWordControllerSegment.run_offset store (uniformPrepared input hC hAd) 0 K scalar
            pc.value M (by dsimp [M]; omega) localBits (by intro index; rfl)
            root.2 hpNew oldRoot.2 hpOld hPosition
        · rename_i hFail
          exact False.elim (hFail hpOld)

theorem smallRun_position (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (smallRun store input hC hAd K outer scalar pc hp).2.value ∧
      (smallRun store input hC hAd K outer scalar pc hp).2.value ≤ store.cap.value := by
  unfold smallRun
  dsimp only
  have hRoot := BinaryPRGWordControllerDataCoin.sample_position store (probability input) pc hp
  split
  · exact hRoot
  · have h := BinaryPRGWordControllerSegment.run_position store (uniformPrepared input hC hAd) 0 K scalar _ hRoot.2
    exact ⟨hRoot.1.trans h.1,h.2⟩
  · have h := BinaryPRGWordControllerReflected.run_position store input hC hAd K outer scalar _ hRoot.2
    exact ⟨hRoot.1.trans h.1,h.2⟩

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  if hg : BinaryFourParentCompiler.gluingCase input = true then
    let prepared := BinaryGluingSampler.prepare input hC (BinaryFourAdmissibility.gluing_guard input hC hAd hg)
    BinaryPRGWordControllerSegment.run store ⟨prepared.table,prepared.canonical,prepared.nonnegative⟩ 0 K scalar pc hp
  else smallRun store input hC (BinaryFourAdmissibility.small_guard input hC hAd hg) K outer scalar pc hp

theorem run_state (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (run store input hC hAd K outer scalar pc hp) =
      BinaryFourPartialRun.runIndexed input hC hAd K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp := by
  unfold run BinaryFourPartialRun.runIndexed BinaryFourPartialRun.run
  dsimp only
  split
  · exact BinaryPRGWordControllerSegment.run_offset store _ 0 K scalar pc.value (store.cap.value - pc.value)
      (by omega) _ (by intro index; rfl) pc hp 0 (Nat.zero_le _) (by omega)
  · exact smallRun_state store input hC _ K outer scalar pc hp

theorem run_position (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).2.value ∧
      (run store input hC hAd K outer scalar pc hp).2.value ≤ store.cap.value := by
  unfold run
  split
  · exact BinaryPRGWordControllerSegment.run_position store _ 0 K scalar pc hp
  · exact smallRun_position store input hC _ K outer scalar pc hp

def restoredRun (store : Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  let result := run store (BinaryFourSpecSampler.orderedInput input)
    (BinaryFourSpecSampler.orderedInput_canonical input hC) (BinaryFourSpecSampler.orderedInput_admissible input hC hAd)
    K outer scalar pc hp
  (result.1.map (fun row => FixedArrayTable.ofFn (fun j => row.read (BinaryFourSpecSampler.permutation input j))),result.2)

theorem restoredRun_state (store : Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (restoredRun store input hC hAd K outer scalar pc hp) =
      BinaryFourSpecPartialRun.runIndexed input hC hAd K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp := by
  have h := run_state store (BinaryFourSpecSampler.orderedInput input)
    (BinaryFourSpecSampler.orderedInput_canonical input hC) (BinaryFourSpecSampler.orderedInput_admissible input hC hAd)
    K outer scalar pc hp
  exact congrArg (fun result : Option (FixedArrayTable 4 SignedWord) × ℕ =>
    (result.1.map (fun row => FixedArrayTable.ofFn (fun j => row.read (BinaryFourSpecSampler.permutation input j))),result.2)) h

theorem restoredRun_position (store : Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (restoredRun store input hC hAd K outer scalar pc hp).2.value ∧
      (restoredRun store input hC hAd K outer scalar pc hp).2.value ≤ store.cap.value :=
  run_position store _ _ _ K outer scalar pc hp

end Blotto.BinaryPRGWordControllerFour

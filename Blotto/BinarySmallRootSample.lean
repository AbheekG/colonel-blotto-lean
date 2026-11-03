import Blotto.BinarySmallUniformCompiler
import Blotto.BinaryStoredCoinIndexed
import Blotto.BinaryReflectedIndexedRun
import Blotto.BinaryTerminalFallback
import Blotto.WordBinaryRunHandoff
import Blotto.RationalFourSmallProgram

/-! The small four-variable root uses its actual stored Boolean probability,
then passes its returned absolute position to exactly one chosen continuation.
Uniform nine-slot and reflected resource/categorical choices use the same N
and reader. A Prop-only source witness supplies erased validity certificates. -/

namespace Blotto.BinarySmallRootSample
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedSerialRun BinaryStoredOverlapEnvironment
open BinaryReflectedSerialValue

abbrev Admissible (input : BinaryFourParameters.Input) :=BinaryReflectedSerialRun.Admissible input

def probability (input : BinaryFourParameters.Input) : SignedWord:=BinaryRationalOpcode.canonicalize input.p

theorem probability_valid (input : BinaryFourParameters.Input) (hC : input.Canonical) : BinaryRationalOpcode.Valid (probability input):=
  BinaryRationalOpcode.canonicalize_valid input.p hC.2.2.2.2.2.1

theorem probability_numbers (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) :
    BinaryBigEndian.littleValue (probability input).numerator=source.smallWords.numerator ∧
      BinaryBigEndian.littleValue (probability input).denominator=source.smallWords.denominator:=by
  have hv : value (probability input)=source.p:=
    (BinaryRationalOpcode.canonicalize_value input.p hC.2.2.2.2.2.1).trans hr.2.2.2.2.2
  have he:=BinaryRationalOpcode.value_num_den_of_coprime (probability input) (probability_valid input hC)
    (BinaryRationalOpcode.canonicalize_coprime input.p hC.2.2.2.2.2.1)
  rw [hv] at he
  constructor
  · change _=source.p.num.toNat
    rw [←he.1]
    exact ProbabilityWords.nonnegative_abs_eq_toNat _ source.p_pos.le
  · exact he.2.symm

theorem probability_unit (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) :
    BinaryBigEndian.littleValue (probability input).numerator≤BinaryBigEndian.littleValue (probability input).denominator:=by
  obtain ⟨source,hr,_⟩:=hAd
  rw [(probability_numbers input source hC hr).1,(probability_numbers input source hC hr).2]
  exact source.smallWords.normalized

theorem uniform_nonnegative (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) :
    ∀ slot,0≤value ((BinarySmallUniformCompiler.fromOriginal input).weight.read slot):=by
  obtain ⟨source,hr,hCase⟩:=hAd
  intro slot
  rw [(BinarySmallUniformCompiler.fromOriginal_refines input source hC hr hCase).1 slot]
  exact (source.smallUniformLottery hCase).nonnegative slot

def uniformRun (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) : Option (FixedArrayTable 4 SignedWord)×ℕ:=
  let table:=BinarySmallUniformCompiler.fromOriginal input
  let selected:=BinaryCategoricalRun.runIndexed (0 : Fin 9) N bits
    (.remaining (NativeBinarySegmentSampler.weights table (BinarySmallUniformCompiler.fromOriginal_canonical input hC)
      (uniform_nonnegative input hC hAd))) pos hp
  (selected.1.map (fun slot=>BinarySegmentPoint.sample table slot K scalar),selected.2)

theorem uniformRun_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    ((uniformRun input hC hAd K N scalar bits pos hp).1.map sourceRow,(uniformRun input hC hAd K N scalar bits pos hp).2)=
      (source.uniformMachine hCase K scalar).runCursorIndexed N bits (.state (source.smallUniformLottery hCase).start) pos hp:=by
  let table:=BinarySmallUniformCompiler.fromOriginal input
  have hc:=BinarySmallUniformCompiler.fromOriginal_canonical input hC
  have ht:=BinarySmallUniformCompiler.fromOriginal_refines input source hC hr hCase
  unfold uniformRun
  dsimp only
  rw [BinaryReflectedSerialSelection.native_selectIndexed_refines table (source.smallUniformLottery hCase) hc ht]
  unfold RationalFourInput.uniformMachine RationalSegmentLottery.machine
  rw [WordMappedIndexedRefinement.indexed_refines]
  simp only [WordMappedIndexedRefinement.mapResult,Option.map_map,Function.comp_def]
  apply Prod.ext
  · apply congrArg (fun f=>((categoricalMachine (0 : Fin 9)).runCursorIndexed N bits
      (.state (source.smallUniformLottery hCase).start) pos hp).1.map f)
    funext slot j
    exact BinarySegmentPoint.sample_value table _ hc ht slot K scalar j
  · rfl

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) : Option (FixedArrayTable 4 SignedWord)×ℕ:=
  let root:=BinaryStoredCoinIndexed.sample (probability input) N bits 0 (Nat.zero_le N)
  match root.1 with
  | none=>(none,root.2)
  | some branch=>
      if hp : root.2≤N then
        if branch then uniformRun input hC hAd K N scalar bits root.2 hp
        else BinaryReflectedIndexedRun.run input hC hAd K N outer scalar bits root.2 hp
      else (none,root.2)


theorem root_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N→Bool) :
    BinaryStoredCoinIndexed.sample (probability input) N bits 0 (Nat.zero_le N)=
      BinaryStoredCoinIndexed.selected.runCursorIndexed N bits (binarySelectedCoin source.smallWords) 0 (Nat.zero_le N):=by
  rw [BinaryStoredCoinIndexed.sample_refines (probability input) (probability_valid input hC) (probability_unit input hC hAd)]
  apply congrArg (fun c=>BinaryStoredCoinIndexed.selected.runCursorIndexed N bits c 0 (Nat.zero_le N))
  exact BinarySharedResourceRun.coin_eq _ _ _ _ _ _ _ _ _ _
    (probability_numbers input source hC hr).1 (probability_numbers input source hC hr).2

theorem run_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) :
    ((run input hC hAd K N outer scalar bits).1.map sourceRow,(run input hC hAd K N outer scalar bits).2)=
      (source.smallMachine hCase K outer scalar).run N .start bits:=by
  rw [WordStateMachine.run_eq_numeric,WordStateMachine.runNumeric]
  unfold RationalFourInput.smallMachine
  rw [WordStateMachine.binary_root_handoff]
  rw [←root_refines input source hC hr hAd]
  unfold run WordStateMachine.handoff
  dsimp only
  cases hs : (BinaryStoredCoinIndexed.sample (probability input) N bits 0 (Nat.zero_le N)).1 with
  | none=>simp only [Option.map_none]
  | some branch=>
      dsimp only
      have hp:=BinaryStoredCoinIndexed.sample_position (probability input) (probability_valid input hC)
        (probability_unit input hC hAd) N bits 0 (Nat.zero_le N)
      simp only [dite_eq_left hp.2]
      cases branch
      · simp only [Bool.false_eq_true,ite_false]
        have he:=BinaryReflectedIndexedRun.run_refines input source hC hr hCase hAd K N outer scalar bits
          (BinaryStoredCoinIndexed.sample (probability input) N bits 0 (Nat.zero_le N)).2 hp.2
        rw [RationalFourInput.reflectedMachine,WordMappedIndexedRefinement.indexed_refines]
        exact he
      · simp only [ite_true]
        exact uniformRun_refines input source hC hr hCase hAd K N scalar bits _ hp.2


theorem small_fallback (source : RationalFourInput) (hCase : source.w < (1-source.p)*source.ell)
    (K : ℕ) (outer scalar : Fin K→Bool) :
    source.smallFallback hCase K outer scalar=
      (RationalAffineAllocation.reflectAppend source.originalLengths).value
        ((source.reflectedResourceSystem hCase).fallback K outer scalar):=by
  unfold RationalFourInput.smallFallback
  rw [WordStateMachine.chooseLeaf_eq_lowerLeaf,RationalFourInput.smallMachine,binaryMachine_specification]
  change ((source.reflectedMachine hCase K outer scalar).specification
    (source.reflectedResourceSystem hCase).samplingStart).lowerLeaf=_
  rw [←WordStateMachine.chooseLeaf_eq_lowerLeaf,RationalFourInput.reflectedMachine,WordStateMachine.mapped_chooseLeaf]
  rfl

def fixedSample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) : FixedArrayTable 4 SignedWord:=
  match (run input hC hAd K N outer scalar bits).1 with
  | some row=>row
  | none=>BinaryTerminalFallback.sample input hC hAd K outer scalar

theorem fixedSample_value (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) (j : Fin 4) :
    value ((fixedSample input hC hAd K N outer scalar bits).read j)=source.smallFixedSample hCase K N outer scalar bits j:=by
  have he:=congrArg Prod.fst (run_refines input source hC hr hCase hAd K N outer scalar bits)
  unfold fixedSample RationalFourInput.smallFixedSample WordStateMachine.output
  cases hn : (run input hC hAd K N outer scalar bits).1 with
  | none=>
      rw [hn,Option.map_none] at he
      rw [←he]
      rw [small_fallback]
      exact BinaryTerminalFallback.sample_value input source hC hAd hr hCase K outer scalar j
  | some row=>
      rw [hn,Option.map_some] at he
      rw [←he]
      rfl

def sample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K)→Bool) : FixedArrayTable 4 SignedWord:=
  let inner:=firstBitBlock (RationalFourInput.smallInnerBitBudget K) K bits
  let outer:=secondBitBlock (RationalFourInput.smallInnerBitBudget K) K bits
  fixedSample input hC hAd K (RationalFourInput.smallCoinBitBudget K) outer
    (secondBitBlock (RationalFourInput.smallCoinBitBudget K) K inner)
    (firstBitBlock (RationalFourInput.smallCoinBitBudget K) K inner)

theorem sample_value (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K)→Bool) (j : Fin 4) :
    value ((sample input hC hAd K bits).read j)=source.smallSample hCase K bits j:=
  fixedSample_value input source hC hr hCase hAd K _ _ _ _ j

noncomputable def sampleLaw (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4:=
  (fairBitLaw (RationalFourInput.smallSampleBitBudget K)).map (fun bits j=>(value ((sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_eq (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input) (K : ℕ) :
    sampleLaw input hC hAd K=source.smallSampleLaw hCase K:=by
  unfold sampleLaw RationalFourInput.smallSampleLaw
  congr 1
  funext bits j
  rw [sample_value input source hC hr hCase hAd]

theorem sampleLaw_CDF_error (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) (source.real.smallCaseLaw (source.smallCase_real hCase)) (5/(2*(2:ℝ)^K)):=by
  rw [sampleLaw_eq input source hC hr hCase hAd]
  exact source.smallSampleLaw_CDF_error hCase K


theorem fixedSample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) :
    FullBudget (source.B : ℝ) (fun j=>(value ((fixedSample input hC hAd K N outer scalar bits).read j) : ℝ)):=by
  have he : (fun j=>(value ((fixedSample input hC hAd K N outer scalar bits).read j) : ℝ))=
      fun j=>(source.smallFixedSample hCase K N outer scalar bits j : ℝ):=by
    funext j
    rw [fixedSample_value input source hC hr hCase hAd]
  rw [he]
  exact (source.smallFixedSample_contract hCase K N outer scalar bits).1

theorem fixedSample_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j=>(value ((fixedSample input hC hAd K N outer scalar bits).read j) : ℝ)):=by
  have he : (fun j=>(value ((fixedSample input hC hAd K N outer scalar bits).read j) : ℝ))=
      fun j=>(source.smallFixedSample hCase K N outer scalar bits j : ℝ):=by
    funext j
    rw [fixedSample_value input source hC hr hCase hAd]
  rw [he]
  exact (source.smallFixedSample_contract hCase K N outer scalar bits).2

theorem sample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K)→Bool) :
    FullBudget (source.B : ℝ) (fun j=>(value ((sample input hC hAd K bits).read j) : ℝ)):=
  fixedSample_fullBudget input source hC hr hCase hAd K _ _ _ _

theorem sample_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K)→Bool) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j=>(value ((sample input hC hAd K bits).read j) : ℝ)):=
  fixedSample_inBox input source hC hr hCase hAd K _ _ _ _


theorem uniformRun_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (row : FixedArrayTable 4 SignedWord) (hs : (uniformRun input hC hAd K N scalar bits pos hp).1=some row) :
    ∀ j,CanonicalWord (row.read j):=by
  obtain ⟨slot,hSlot,rfl⟩:=Option.map_eq_some_iff.mp hs
  exact BinarySegmentPoint.sample_canonical _ slot K scalar (BinarySmallUniformCompiler.fromOriginal_canonical input hC)

theorem reflectedRun_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (row : FixedArrayTable 4 SignedWord) (hs : (BinaryReflectedIndexedRun.run input hC hAd K N outer scalar bits pos hp).1=some row) :
    ∀ j,CanonicalWord (row.read j):=by
  change (BinaryReflectedCachedRun.run input hC hAd K (N-pos) outer scalar
    (WordStateMachine.inputWindow bits pos (N-pos) (by omega))).1=some row at hs
  rw [BinaryReflectedCachedRun.run_eq] at hs
  exact BinaryReflectedSerialRun.run_canonical input hC hAd K (N-pos) outer scalar _ row hs

theorem run_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool)
    (row : FixedArrayTable 4 SignedWord) (hs : (run input hC hAd K N outer scalar bits).1=some row) :
    ∀ j,CanonicalWord (row.read j):=by
  unfold run at hs
  dsimp only at hs
  split at hs
  · cases hs
  · rename_i branch hBranch
    split at hs
    · rename_i hp
      split at hs
      · exact uniformRun_canonical input hC hAd K N scalar bits _ hp row hs
      · exact reflectedRun_canonical input hC hAd K N outer scalar bits _ hp row hs
    · cases hs

theorem fixedSample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K→Bool) (bits : Fin N→Bool) :
    ∀ j,CanonicalWord ((fixedSample input hC hAd K N outer scalar bits).read j):=by
  unfold fixedSample
  split
  · rename_i row hs
    exact run_canonical input hC hAd K N outer scalar bits row hs
  · exact BinaryTerminalFallback.sample_canonical input hC hAd K outer scalar

theorem sample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K)→Bool) :
    ∀ j,CanonicalWord ((sample input hC hAd K bits).read j):=
  fixedSample_canonical input hC hAd K _ _ _ _

end Blotto.BinarySmallRootSample

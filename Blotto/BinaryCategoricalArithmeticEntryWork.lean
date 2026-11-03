import Blotto.BinaryPhysicalArithmeticEntryWork

/-! The entry class follows actual categorical mass sums and reached guards,
probabilities and recursive suffixes. Coin failure/selection skips later sums.
The returned scalar/cursor and preparation choice are the actual source values. -/
namespace Blotto.BinaryCategoricalArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCategoricalPreparation BinaryCategoricalRun
open BinaryExpressionArithmeticEntryWork (quadratic_bound comparison_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def sum {α : Type*} : List (α × SignedWord) → ℕ
  | [] => 0
  | item::rest => sum rest+BinaryArithmeticEntryWork.raw .add item.2 (BinaryQuadraticCategoricalMeasured.sum rest).1.1

theorem sum_bound {α : Type*} (items : List (α × SignedWord)) :
    sum items ≤ 2*listCells (BinaryQuadraticCategoricalMeasured.sum items).1.2 := by
  induction items with
  | nil => simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sum,BinaryQuadraticCategoricalMeasured.sum_nil,BinaryQuadraticCategoricalMeasured.sum_cons,listCells]; omega
  | cons item rest ih =>
      have h := quadratic_bound .add item.2 (BinaryQuadraticCategoricalMeasured.sum rest).1.1
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,sum,BinaryQuadraticCategoricalMeasured.sum_nil,BinaryQuadraticCategoricalMeasured.sum_cons,listCells_append,listCells_under,listCells]
      omega

def prepare {α : Type*} (weights : WeightList α) : ℕ :=
  match weights.items with
  | [] => 0
  | [_] => 0
  | head::_::_ =>
      let computed := BinaryQuadraticCategoricalMeasured.sum weights.items
      let guard := BinaryQuadraticExpressionMeasured.compare computed.1.1 BinaryRationalOpcode.zero
      sum weights.items+BinaryArithmeticEntryWork.comparison computed.1.1 BinaryRationalOpcode.zero+
        if (!guard.1.1)=true then BinaryArithmeticEntryWork.raw .div head.2 computed.1.1 else 0

theorem prepare_bound {α : Type*} (fallback : α) (weights : WeightList α) :
    prepare weights ≤ 2*listCells (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticCategoricalMeasured.prepare_record]
  split
  · rename_i he
    simp only [prepare,he]
    omega
  · rename_i head he
    simp only [prepare,he]
    omega
  · rename_i head next tail he
    have hs := sum_bound weights.items
    have hc := comparison_bound (BinaryQuadraticCategoricalMeasured.sum weights.items).1.1 BinaryRationalOpcode.zero
    have hd := quadratic_bound .div head.2 (BinaryQuadraticCategoricalMeasured.sum weights.items).1.1
    simp only [prepare,he] at hs hc hd ⊢
    split <;> simp only [listCells_append,listCells_under,listCells] <;> omega

def run {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ℕ :=
  let prepared := BinaryQuadraticCategoricalMeasured.prepare fallback weights
  prepare weights+
    match hs : prepared.1.1 with
    | .done _ => 0
    | .ask choice =>
        let coin := BinaryWordCoinMeasured.sample store choice.probability pc hp
        match coin.1.1.1 with
        | none => 0
        | some true => 0
        | some false => run store fallback choice.rest coin.1.1.2
            (BinaryWordCoinMeasured.sample_position store choice.probability pc hp).2
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem run_bound {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store fallback weights pc hp ≤ 2*listCells (BinaryWordCategoricalMeasured.run store fallback weights pc hp).1.2 := by
  have hpairs := prepare_bound fallback weights
  conv_lhs => unfold run
  conv_rhs => rw [BinaryWordCategoricalMeasured.run_record]
  dsimp only
  cases hs : (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.1 with
  | done selected =>
      simp only [Nat.add_zero,wrap,combine,listCells_append,listCells_under,listCells]
      omega
  | ask choice =>
      dsimp only
      cases hc : (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.1 with
      | none =>
          simp only [hc,Nat.add_zero,wrap,combine,listCells_append,listCells_under,listCells]
          omega
      | some branch =>
          cases branch with
          | false =>
              have hl := run_bound store fallback choice.rest
                (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.2
                (BinaryWordCoinMeasured.sample_position store choice.probability pc hp).2
              simp only [hc,wrap,combine,listCells_append,listCells_under,listCells]
              omega
          | true =>
              simp only [hc,Nat.add_zero,wrap,combine,listCells_append,listCells_under,listCells]
              omega

termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

def select {n k : ℕ} (seed : BinarySeedLookupTree.Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  run seed fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp

theorem select_bound {n k : ℕ} (seed : BinarySeedLookupTree.Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    select seed prepared fallback pc hp ≤ 2*listCells (BinaryWordSegmentMeasured.select seed prepared fallback pc hp).1.2 := by
  have h := run_bound seed fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  simp only [select,BinaryWordSegmentMeasured.select_record,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def segment {n k : ℕ} (seed : BinarySeedLookupTree.Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) : ℕ :=
  select seed prepared fallback pc hp+BinaryPhysicalArithmeticEntryWork.segment seed prepared fallback K scalar pc hp

theorem segment_bound {n k : ℕ} (seed : BinarySeedLookupTree.Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) : segment seed prepared fallback K scalar pc hp ≤
      2*listCells (BinaryWordSegmentMeasured.run seed prepared fallback K scalar pc hp).1.2 := by
  have hs := select_bound seed prepared fallback pc hp
  simp only [BinaryWordSegmentMeasured.run_record]
  split
  · rename_i hNone
    simp only [segment,BinaryPhysicalArithmeticEntryWork.segment,hNone,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i slot hSome
    have hp := BinaryPhysicalArithmeticEntryWork.point_bound prepared.table slot K scalar
    simp only [segment,BinaryPhysicalArithmeticEntryWork.segment,hSome,wrap,combine,listCells_append,listCells_under,listCells]
    omega

end Blotto.BinaryCategoricalArithmeticEntryWork

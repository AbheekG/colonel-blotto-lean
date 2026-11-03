import Blotto.BinaryCanonicalFrameMeasured
import Blotto.BinaryStoredDimensionControlMeasured
import Blotto.BinaryStoredDimensionRowLifetime

/-! One measured row reader uses actual Boolean scans, canonical readers
and borrow loops. Recursion and its bound decrease the remaining input,
including failed parses with an arbitrarily large stored dimension. The
decoded value occurs in types/proofs only, never as a runtime loop ruler. -/
namespace Blotto.BinaryStoredDimensionRowMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def read (counter bits : List Bool) : (Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × Trace) × ℕ :=
  let tested := BooleanFreshSeedMeasured.scan counter
  if hPositive : tested.1.1 = true then
    let first := BinaryCanonicalFrameMeasured.read bits
    match hf : first.1.1 with
    | none => ((none,wrap 24 2 [tested.1.2,first.1.2]),tested.2+first.2+8)
    | some parsed =>
        let smaller := BinaryStoredDimensionControlMeasured.predecessor counter
        let later := read smaller.1.1 parsed.2
        have hCount : BinaryBigEndian.littleValue smaller.1.1+1 = BinaryBigEndian.littleValue counter :=
          BinaryStoredDimensionControlMeasured.predecessor_value counter ((BinaryEuclideanGCD.nonzero_true_iff _).mp
            ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).symm.trans
              ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).symm.trans hPositive)))
        let result := later.1.1.map (fun rest =>
          (⟨parsed.1.val::rest.1.row,(by simp only [List.length_cons,rest.1.length]; exact hCount),
            (by intro word hw; rcases List.mem_cons.mp hw with he | ht
                · subst word; exact parsed.1.property
                · exact rest.1.canonical word ht)⟩,rest.2))
        ((result,wrapList 1 48 2 [tested.1.2,first.1.2,smaller.1.2,later.1.2]),
          tested.2+first.2+smaller.2+later.2+12)
  else
    have hZero : BinaryBigEndian.littleValue counter = 0 := by
      apply BinaryStoredCountdown.nonzeroWithWork_false counter
      apply Bool.eq_false_iff.mpr
      exact fun h => hPositive ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).trans
        ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).trans h))
    ((some (⟨[],hZero.symm,by simp⟩,bits),wrap 16 2 [tested.1.2]),tested.2+4)
termination_by bits.length
decreasing_by exact BinaryCanonicalFrameMeasured.read_suffix_lt bits parsed hf

def eraseResult {n : ℕ} (result : Option (Words n × List Bool) × Trace) :
    Option (List SignedWord × List Bool) × Trace :=
  (result.1.map BinaryStoredDimensionRow.erase,result.2)

theorem read_raw_erases (counter bits : List Bool) :
    eraseResult (read counter bits).1 =
      eraseResult (BinaryStoredDimensionRowLifetime.readWithTrace counter bits) := by
  unfold read BinaryStoredDimensionRowLifetime.readWithTrace
  dsimp only
  by_cases hp : (BooleanFreshSeedMeasured.scan counter).1.1 = true
  · have ho : (BinaryBooleanPrimitiveLifetime.scanWithTrace counter).1 = true :=
      (congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).symm.trans hp
    rw [dite_eq_left hp,dite_eq_left ho]
    cases hf : (BinaryCanonicalFrameMeasured.read bits).1.1 with
    | none =>
        symm
        split
        · simp only [eraseResult,Option.map_none,BooleanFreshSeedMeasured.scan_erases,
            BinaryCanonicalFrameMeasured.read_erases]
        · rename_i parsed hOld
          have hNone := (congrArg Prod.fst (BinaryCanonicalFrameMeasured.read_erases bits)).symm.trans hf
          rw [hOld] at hNone
          cases hNone
    | some parsed =>
        symm
        split
        · rename_i hOld
          have hSome := (congrArg Prod.fst (BinaryCanonicalFrameMeasured.read_erases bits)).symm.trans hf
          rw [hOld] at hSome
          cases hSome
        · rename_i old hOld
          have hSome := (congrArg Prod.fst (BinaryCanonicalFrameMeasured.read_erases bits)).symm.trans hf
          have he : old = parsed := Option.some.inj (hOld.symm.trans hSome)
          subst old
          symm
          let extend : Option (List SignedWord × List Bool) × Trace →
              Option (List SignedWord × List Bool) × Trace := fun d =>
            (d.1.map (fun rest => (parsed.1.val::rest.1,rest.2)),
              wrapList 1 48 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2,
                (BinaryCanonicalFrameLifetime.readWithTrace bits).2,
                (BinaryStoredCountdownLifetime.predecessorWithTrace counter).2,d.2])
          have ih := congrArg extend
            (read_raw_erases (BinaryStoredDimensionControlMeasured.predecessor counter).1.1 parsed.2)
          have hPred := congrArg Prod.fst (BinaryStoredDimensionControlMeasured.predecessor_erases counter)
          have hOldRows := congrArg (fun smaller => extend
            (eraseResult (BinaryStoredDimensionRowLifetime.readWithTrace smaller parsed.2))) hPred
          simpa only [extend,eraseResult,Option.map_map,Function.comp_def,BinaryStoredDimensionRow.erase,
            BooleanFreshSeedMeasured.scan_erases,BinaryCanonicalFrameMeasured.read_erases,
            BinaryStoredDimensionControlMeasured.predecessor_erases] using ih.trans hOldRows
  · have ho : ¬ (BinaryBooleanPrimitiveLifetime.scanWithTrace counter).1 = true :=
      fun h => hp ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).trans h)
    rw [dite_eq_right hp,dite_eq_right ho]
    simp only [eraseResult,Option.map_some,BinaryStoredDimensionRow.erase,BooleanFreshSeedMeasured.scan_erases]
termination_by bits.length
decreasing_by exact BinaryCanonicalFrameMeasured.read_suffix_lt _ _ (by assumption)

theorem read_erases (counter bits : List Bool) :
    (read counter bits).1 = BinaryStoredDimensionRowLifetime.readWithTrace counter bits := by
  have h := read_raw_erases counter bits
  apply Prod.ext
  · have hd := congrArg Prod.fst h
    change (read counter bits).1.1.map BinaryStoredDimensionRow.erase =
      (BinaryStoredDimensionRowLifetime.readWithTrace counter bits).1.map BinaryStoredDimensionRow.erase at hd
    cases hn : (read counter bits).1.1 with
    | none =>
        rw [hn,Option.map_none] at hd
        cases ho : (BinaryStoredDimensionRowLifetime.readWithTrace counter bits).1 with
        | none => rfl
        | some parsed => rw [ho,Option.map_some] at hd; cases hd
    | some parsed =>
        rw [hn,Option.map_some] at hd
        cases ho : (BinaryStoredDimensionRowLifetime.readWithTrace counter bits).1 with
        | none => rw [ho,Option.map_none] at hd; cases hd
        | some old =>
            rw [ho,Option.map_some] at hd
            exact congrArg some (BinaryStoredDimensionRow.erase_injective (Option.some.inj hd))
  · simpa only [eraseResult] using congrArg Prod.snd h

def price (counterWidth length : ℕ) : ℕ :=
  (length+1)*(BinaryCanonicalFrameMeasured.price length+8*(counterWidth+1)+32)

theorem price_mono {a b c d : ℕ} (hW : a ≤ b) (hL : c ≤ d) : price a c ≤ price b d := by
  have h := BinaryCanonicalFrameMeasured.price_mono hL
  unfold price
  gcongr

theorem read_work (counter bits : List Bool) : (read counter bits).2 ≤ price counter.length bits.length := by
  have hScan := BooleanFreshSeedMeasured.scan_bound counter
  have hFirst := BinaryCanonicalFrameMeasured.read_work bits
  unfold read
  dsimp only
  split
  · split
    · unfold price
      nlinarith
    · rename_i parsed hf
      have hLength := BinaryCanonicalFrameMeasured.read_suffix_lt bits parsed hf
      have hDec := BinaryStoredDimensionControlMeasured.predecessor_work counter
      have ih := read_work (BinaryStoredDimensionControlMeasured.predecessor counter).1.1 parsed.2
      rw [BinaryStoredDimensionControlMeasured.predecessor_length] at ih
      have hCanon := BinaryCanonicalFrameMeasured.price_mono hLength.le
      have ht : (read (BinaryStoredDimensionControlMeasured.predecessor counter).1.1 parsed.2).2 ≤
          bits.length*(BinaryCanonicalFrameMeasured.price bits.length+8*(counter.length+1)+32) :=
        ih.trans (Nat.mul_le_mul (show parsed.2.length+1 ≤ bits.length by omega)
          (Nat.add_le_add_right (Nat.add_le_add_right hCanon (8*(counter.length+1))) 32))
      unfold price
      rw [Nat.add_mul,one_mul]
      omega
  · unfold price
    nlinarith
termination_by bits.length
decreasing_by exact BinaryCanonicalFrameMeasured.read_suffix_lt _ _ (by assumption)

theorem read_count_bound (counter bits : List Bool) (parsed : Words (BinaryBigEndian.littleValue counter) × List Bool)
    (h : (read counter bits).1.1 = some parsed) : BinaryBigEndian.littleValue counter ≤ bits.length :=
  BinaryStoredDimensionRowLifetime.read_count_bound counter bits parsed
    ((congrArg Prod.fst (read_erases counter bits)).symm.trans h)

theorem read_consumed (counter bits : List Bool) (parsed : Words (BinaryBigEndian.littleValue counter) × List Bool)
    (h : (read counter bits).1.1 = some parsed) :
    (parsed.1.row.map width).sum+parsed.2.length ≤ bits.length :=
  BinaryStoredDimensionRowLifetime.read_consumed counter bits parsed
    ((congrArg Prod.fst (read_erases counter bits)).symm.trans h)

theorem read_usage (counter bits : List Bool) :
    usage (read counter bits).1.2 ≤ BinaryStoredDimensionRowLifetime.envelope counter.length bits.length := by
  rw [read_erases]
  exact BinaryStoredDimensionRowLifetime.readWithTrace_usage counter bits

theorem all_prefix (counter bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+counter.length+bits.length) (read counter bits).1.2 steps ≤
      borrowed+counter.length+bits.length+BinaryStoredDimensionRowLifetime.envelope counter.length bits.length ∧
    framePeak ((read counter bits).1.2.take steps) ≤ BinaryStoredDimensionRowLifetime.envelope counter.length bits.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage counter bits) _ steps

end Blotto.BinaryStoredDimensionRowMeasured

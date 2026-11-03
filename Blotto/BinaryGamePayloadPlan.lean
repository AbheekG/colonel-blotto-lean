import Blotto.BinaryCanonicalPayloadPlan
import Blotto.BinaryPRGGameFrameMeasured

/-! Reached canonical payload plans feed actual row recursion and game parsing.
The full preceding game record and source work remain exact. Only reached
payload emissions are added; dimension-header/control/packing scopes remain. -/
namespace Blotto.BinaryGamePayloadPlan
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame BinaryPRGHeaderFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def row (counter bits : List Bool) : ((Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × Trace) × ℕ) × ℕ :=
  let tested := BooleanFreshSeedMeasured.scan counter
  if hPositive : tested.1.1 = true then
    let firstProduced := BinaryCanonicalPayloadPlan.read bits
    let first := firstProduced.1
    match hf : first.1.1 with
    | none => (((none,wrap 24 2 [tested.1.2,first.1.2]),tested.2+first.2+8),firstProduced.2)
    | some parsed =>
        let smaller := BinaryStoredDimensionControlMeasured.predecessor counter
        let returned := row smaller.1.1 parsed.2
        let later := returned.1
        have hCount : BinaryBigEndian.littleValue smaller.1.1+1 = BinaryBigEndian.littleValue counter :=
          BinaryStoredDimensionControlMeasured.predecessor_value counter ((BinaryEuclideanGCD.nonzero_true_iff _).mp
            ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).symm.trans
              ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).symm.trans hPositive)))
        let result := later.1.1.map (fun rest =>
          (⟨parsed.1.val::rest.1.row,(by simp only [List.length_cons,rest.1.length]; exact hCount),
            (by intro word hw; rcases List.mem_cons.mp hw with he | ht
                · subst word; exact parsed.1.property
                · exact rest.1.canonical word ht)⟩,rest.2))
        (((result,wrapList 1 48 2 [tested.1.2,first.1.2,smaller.1.2,later.1.2]),
          tested.2+first.2+smaller.2+later.2+12),firstProduced.2+returned.2)
  else
    have hZero : BinaryBigEndian.littleValue counter = 0 := by
      apply BinaryStoredCountdown.nonzeroWithWork_false counter
      apply Bool.eq_false_iff.mpr
      exact fun h => hPositive ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).trans
        ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).trans h))
    (((some (⟨[],hZero.symm,by simp⟩,bits),wrap 16 2 [tested.1.2]),tested.2+4),0)
termination_by bits.length
decreasing_by exact BinaryCanonicalPayloadPlan.read_suffix_lt bits parsed hf

theorem row_compat (counter bits : List Bool) :
    (row counter bits).1 = BinaryStoredDimensionRowMeasured.read counter bits := by
  conv_lhs => unfold row
  conv_rhs => unfold BinaryStoredDimensionRowMeasured.read
  dsimp only
  simp only [← BinaryCanonicalPayloadPlan.read_compat]
  split
  · cases hf : (BinaryCanonicalPayloadPlan.read bits).1.1.1 with
    | none =>
        have ho := (congrArg (fun out => out.1.1) (BinaryCanonicalPayloadPlan.read_compat bits)).symm.trans hf
        simp only [hf]
        symm
        split
        · rfl
        · rename_i parsed hSome
          cases ho.symm.trans hSome
    | some parsed =>
        have ho := (congrArg (fun out => out.1.1) (BinaryCanonicalPayloadPlan.read_compat bits)).symm.trans hf
        simp only [hf]
        symm
        split
        · rename_i hNone
          cases ho.symm.trans hNone
        · rename_i old hOld
          have he := Option.some.inj (ho.symm.trans hOld)
          subst old
          symm
          rw [row_compat (BinaryStoredDimensionControlMeasured.predecessor counter).1.1 parsed.2]
  · rfl
termination_by bits.length
decreasing_by exact BinaryCanonicalPayloadPlan.read_suffix_lt _ _ (by assumption)

theorem row_price (counter bits : List Bool) : (row counter bits).2 ≤ 30*(row counter bits).1.2 := by
  have hf := BinaryCanonicalPayloadPlan.read_price bits
  unfold row
  dsimp only
  split
  · split
    · dsimp only; omega
    · rename_i parsed hFirst
      have ih := row_price (BinaryStoredDimensionControlMeasured.predecessor counter).1.1 parsed.2
      dsimp only
      omega
  · exact Nat.zero_le _
termination_by bits.length
decreasing_by exact BinaryCanonicalPayloadPlan.read_suffix_lt _ _ (by assumption)

def read (bits : List Bool) : ((Option ((Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool) × Trace) × ℕ) × ℕ :=
  let dimension := BinaryStoredDimensionHeaderMeasured.read bits
  match dimension.1.1 with
  | none => (((none,wrap 16 2 [dimension.1.2]),dimension.2+4),0)
  | some raw =>
      let firstProduced := BinaryCanonicalPayloadPlan.read raw.2
      let first := firstProduced.1
      match first.1.1 with
      | none => (((none,wrap 24 2 [dimension.1.2,first.1.2]),dimension.2+first.2+8),firstProduced.2)
      | some firstWord =>
          let secondProduced := BinaryCanonicalPayloadPlan.read firstWord.2
          let second := secondProduced.1
          match second.1.1 with
          | none => (((none,wrap 32 2 [dimension.1.2,first.1.2,second.1.2]),dimension.2+first.2+second.2+12),firstProduced.2+secondProduced.2)
          | some secondWord =>
              let wordsProduced := row raw.1.payload secondWord.2
              let words := wordsProduced.1
              match words.1.1 with
              | none => (((none,wrap 40 2 [dimension.1.2,first.1.2,second.1.2,words.1.2]),
                  dimension.2+first.2+second.2+words.2+16),firstProduced.2+secondProduced.2+wordsProduced.2)
              | some rest =>
                  let packed := BinaryPRGGameFrameMeasured.pack raw.1.typed firstWord.1 secondWord.1 rest
                  (((some packed.1.1,wrap 80 (raw.1.payload.length+8)
                    [dimension.1.2,first.1.2,second.1.2,words.1.2,packed.1.2]),
                    dimension.2+first.2+second.2+words.2+packed.2+20),firstProduced.2+secondProduced.2+wordsProduced.2)

theorem read_compat (bits : List Bool) : (read bits).1 = BinaryPRGGameFrameMeasured.read bits := by
  simp only [read,BinaryPRGGameFrameMeasured.read,← BinaryCanonicalPayloadPlan.read_compat,← row_compat]
  cases hd : (BinaryStoredDimensionHeaderMeasured.read bits).1.1 with
  | none => simp only [hd]
  | some raw =>
      simp only [hd]
      cases hf : (BinaryCanonicalPayloadPlan.read raw.2).1.1.1 with
      | none => simp only [hf]
      | some first =>
          simp only [hf]
          cases hs : (BinaryCanonicalPayloadPlan.read first.2).1.1.1 with
          | none => simp only [hs]
          | some second =>
              simp only [hs]
              cases hr : (row raw.1.payload second.2).1.1.1 <;> simp only [hr]

theorem read_price (bits : List Bool) : (read bits).2 ≤ 30*(read bits).1.2 := by
  unfold read
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i raw hd
    have hf := BinaryCanonicalPayloadPlan.read_price raw.2
    split
    · dsimp only; omega
    · rename_i first hFirst
      have hs := BinaryCanonicalPayloadPlan.read_price first.2
      split
      · dsimp only; omega
      · rename_i second hSecond
        have hr := row_price raw.1.payload second.2
        split <;> dsimp only <;> omega

end Blotto.BinaryGamePayloadPlan

import Blotto.BinaryStoredRowPlan

/-! A reusable actual canonical-reader continuation preserves the whole
preceding row plan and both old charges, while forwarding an extra reader
counter. Reader compatibility is erased; concrete callers discharge it. -/
namespace Blotto.BinaryCanonicalRowContinuation
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (finish view data_refines)
open BinaryStoredRowPlan (predecessorAt predecessor_refines scan_data)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

structure Backend (E : Type*) where
  run : List Bool → (((Option ({word : SignedWord // CanonicalWord word} × List Bool) × Trace) × ℕ) × ℕ) × E
  compat : ∀ frame,(run frame).1 = BinaryCanonicalPayloadPlan.read frame

theorem read_suffix_lt {E : Type*} (backend : Backend E) (frame : List Bool)
    (parsed : {word : SignedWord // CanonicalWord word} × List Bool)
    (h : (backend.run frame).1.1.1.1 = some parsed) : parsed.2.length < frame.length :=
  BinaryCanonicalPayloadPlan.read_suffix_lt frame parsed
    ((congrArg (fun out => out.1.1.1) (backend.compat frame)).symm.trans h)

variable {E : Type*} [Zero E] [Add E]

def rowAt (backend : Backend E) (counter bits : List Bool) (depth : ℕ) :
    ((Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × Plan) × (ℕ × ℕ)) × E :=
  let tested := BooleanFreshSeedMeasured.scanAt counter (depth+2)
  if hPositive : tested.1.1 = true then
    let extended := backend.run bits
    let firstProduced := extended.1
    let first := firstProduced.1
    match hf : first.1.1 with
    | none =>
        (((none,.join (.block [.frames (depth+2),.arrayAllocation 24])
          (.join (.block tested.1.2) (.shifted (depth+2) first.1.2))),
          (tested.2+first.2+8,firstProduced.2)),extended.2)
    | some parsed =>
        let smaller := predecessorAt counter (depth+2)
        let continued := rowAt backend smaller.1.1 parsed.2 (depth+2)
        let later := continued.1
        have hCount : BinaryBigEndian.littleValue smaller.1.1+1 = BinaryBigEndian.littleValue counter := by
          rw [data_refines (predecessor_refines counter (depth+2))]
          exact BinaryStoredDimensionControlMeasured.predecessor_value counter ((BinaryEuclideanGCD.nonzero_true_iff _).mp
            ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).symm.trans
              ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).symm.trans
                ((scan_data counter (depth+2)).symm.trans hPositive))))
        let result := later.1.1.map (fun rest =>
          (⟨parsed.1.val::rest.1.row,(by simp only [List.length_cons,rest.1.length]; exact hCount),
            (by intro word hw; rcases List.mem_cons.mp hw with he | ht
                · subst word; exact parsed.1.property
                · exact rest.1.canonical word ht)⟩,rest.2))
        (((result,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 48])
          (.join (.block tested.1.2) (.join (.shifted (depth+2) first.1.2) (.join smaller.1.2 later.1.2)))),
          (tested.2+first.2+smaller.2+later.2.1+12,firstProduced.2+later.2.2)),extended.2+continued.2)
  else
    have hZero : BinaryBigEndian.littleValue counter = 0 := by
      apply BinaryStoredCountdown.nonzeroWithWork_false counter
      apply Bool.eq_false_iff.mpr
      exact fun h => hPositive ((scan_data counter (depth+2)).trans
        ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).trans
          ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).trans h)))
    (((some (⟨[],hZero.symm,by simp⟩,bits),
      .join (.block [.frames (depth+2),.arrayAllocation 16]) (.block tested.1.2)),(tested.2+4,0)),0)
termination_by bits.length
 decreasing_by exact read_suffix_lt backend bits parsed hf

theorem rowAt_compat (backend : Backend E) (counter bits : List Bool) (depth : ℕ) :
    (rowAt backend counter bits depth).1 = BinaryStoredRowPlan.rowAt counter bits depth := by
  have hData := congrArg (fun out => out.1.1.1) (backend.compat bits)
  conv_lhs => unfold rowAt
  conv_rhs => unfold BinaryStoredRowPlan.rowAt
  dsimp only
  simp only [backend.compat]
  split
  · cases hf : (backend.run bits).1.1.1.1 with
    | none =>
        have ho := hData.symm.trans hf
        simp only [hf]
        symm
        split
        · rfl
        · rename_i other hSome
          cases ho.symm.trans hSome
    | some parsed =>
        have ho := hData.symm.trans hf
        simp only [hf]
        symm
        split
        · rename_i hNone
          cases ho.symm.trans hNone
        · rename_i other hSome
          have he := Option.some.inj (ho.symm.trans hSome)
          subst other
          symm
          rw [rowAt_compat backend (predecessorAt counter (depth+2)).1.1 parsed.2 (depth+2)]
  · rfl
termination_by bits.length
 decreasing_by exact read_suffix_lt backend _ _ (by assumption)

def row (backend : Backend E) (counter bits : List Bool) :
    ((((Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × Trace) × ℕ) × ℕ) × ℕ) × E :=
  let continued := rowAt backend counter bits 0
  let produced := finish continued.1
  ((((produced.1.1,produced.1.2.1),produced.1.2.2),produced.2),continued.2)

theorem row_compat (backend : Backend E) (counter bits : List Bool) :
    (row backend counter bits).1 = BinaryStoredRowPlan.row counter bits := by
  simp only [row,BinaryStoredRowPlan.row,rowAt_compat]

theorem rowAt_price (backend : Backend ℕ)
    (hPrice : ∀ bits,(backend.run bits).2 ≤ 4*(backend.run bits).1.1.2+25*(backend.run bits).1.1.1.2.length+5)
    (counter bits : List Bool) (depth : ℕ) :
    (rowAt backend counter bits depth).2 ≤
      4*(rowAt backend counter bits depth).1.2.1+25*payload (rowAt backend counter bits depth).1.1.2+5 := by
  have hf := hPrice bits
  unfold rowAt
  dsimp only
  split
  · split
    · dsimp only
      simp only [payload,List.length_cons,List.length_nil]
      omega
    · rename_i parsed hFirst
      have ih := rowAt_price backend hPrice (predecessorAt counter (depth+2)).1.1 parsed.2 (depth+2)
      dsimp only
      simp only [payload,List.length_cons,List.length_nil]
      omega
  · dsimp only
    omega
termination_by bits.length
 decreasing_by exact read_suffix_lt backend _ _ (by assumption)

theorem row_price (backend : Backend ℕ)
    (hPrice : ∀ bits,(backend.run bits).2 ≤ 4*(backend.run bits).1.1.2+25*(backend.run bits).1.1.1.2.length+5)
    (counter bits : List Bool) :
    (row backend counter bits).2 ≤ 4*(row backend counter bits).1.1.1.2+
      25*(row backend counter bits).1.1.1.1.2.length+5 := by
  have h := rowAt_price backend hPrice counter bits 0
  simpa only [row,BinaryNumericalReadbackPlan.finish_record,view,denote_length] using h

end Blotto.BinaryCanonicalRowContinuation

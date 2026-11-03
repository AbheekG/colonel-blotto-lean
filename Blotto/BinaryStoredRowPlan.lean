import Blotto.BinaryGamePayloadPlan
import Blotto.BinarySeedTraceBounds
import Blotto.BinaryNumericalReadbackPlan

/-! The actual stored-dimension row parser retains its Boolean counter and
canonical payload emission. Borrow and recursive row traces collect final-depth
plans; one row emission shifts each reached canonical leaf once. The decoded
counter occurs only in types/proofs; termination decreases remaining input. -/
namespace Blotto.BinaryStoredRowPlan
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

def predecessorAt : List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),4)
  | true::rest,depth => ((false::rest,.block [.listAllocation 1,.frames (depth+1),.arrayAllocation 8]),4)
  | false::rest,depth =>
      let later := predecessorAt rest (depth+2)
      ((true::later.1.1,.join (.block [.listAllocation 1,.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+4)

theorem predecessor_refines (counter : List Bool) (depth : ℕ) :
    view (predecessorAt counter depth) = offset depth (BinaryStoredDimensionControlMeasured.predecessor counter) := by
  induction counter generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      have h := ih (depth+2)
      cases bit <;> simp only [predecessorAt,BinaryStoredDimensionControlMeasured.predecessor,view,offset,denote,
        data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,under_append,under_compose,List.append_nil] <;> rfl

theorem predecessor_budget (counter : List Bool) (depth : ℕ) :
    Bounded (predecessorAt counter depth).1.2 ∧
      payload (predecessorAt counter depth).1.2 ≤ (predecessorAt counter depth).2 := by
  induction counter generalizing depth with
  | nil => simp [predecessorAt,Bounded,nodes,payload]
  | cons bit rest ih =>
      have h := ih (depth+2)
      cases bit <;> simp only [predecessorAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢ <;> omega

theorem scan_data (counter : List Bool) (depth : ℕ) :
    (BooleanFreshSeedMeasured.scanAt counter depth).1.1 = (BooleanFreshSeedMeasured.scan counter).1.1 := by
  rw [BooleanFreshSeedMeasured.scanAt_erases,BooleanFreshSeedMeasured.scan_erases]

theorem scan_trace (counter : List Bool) (depth : ℕ) :
    (BooleanFreshSeedMeasured.scanAt counter depth).1.2 = under depth (BooleanFreshSeedMeasured.scan counter).1.2 := by
  rw [BooleanFreshSeedMeasured.scanAt_erases,BooleanFreshSeedMeasured.scan_erases]

theorem scan_work (counter : List Bool) (depth : ℕ) :
    (BooleanFreshSeedMeasured.scanAt counter depth).2 = (BooleanFreshSeedMeasured.scan counter).2 := by
  rw [BooleanFreshSeedMeasured.scanAt_work,BooleanFreshSeedMeasured.scan_work]

def rowAt (counter bits : List Bool) (depth : ℕ) :
    (Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × Plan) × (ℕ × ℕ) :=
  let tested := BooleanFreshSeedMeasured.scanAt counter (depth+2)
  if hPositive : tested.1.1 = true then
    let firstProduced := BinaryCanonicalPayloadPlan.read bits
    let first := firstProduced.1
    match hf : first.1.1 with
    | none =>
        ((none,.join (.block [.frames (depth+2),.arrayAllocation 24])
          (.join (.block tested.1.2) (.shifted (depth+2) first.1.2))),
          (tested.2+first.2+8,firstProduced.2))
    | some parsed =>
        let smaller := predecessorAt counter (depth+2)
        let later := rowAt smaller.1.1 parsed.2 (depth+2)
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
        ((result,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 48])
          (.join (.block tested.1.2) (.join (.shifted (depth+2) first.1.2) (.join smaller.1.2 later.1.2)))),
          (tested.2+first.2+smaller.2+later.2.1+12,firstProduced.2+later.2.2))
  else
    have hZero : BinaryBigEndian.littleValue counter = 0 := by
      apply BinaryStoredCountdown.nonzeroWithWork_false counter
      apply Bool.eq_false_iff.mpr
      exact fun h => hPositive ((scan_data counter (depth+2)).trans
        ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases counter)).trans
          ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).trans h)))
    ((some (⟨[],hZero.symm,by simp⟩,bits),
      .join (.block [.frames (depth+2),.arrayAllocation 16]) (.block tested.1.2)),(tested.2+4,0))
termination_by bits.length
 decreasing_by exact BinaryCanonicalPayloadPlan.read_suffix_lt bits parsed hf

def eraseRecord {n : ℕ} {β : Type*} (record : (Option (Words n × List Bool) × Trace) × β) :
    (Option (List SignedWord × List Bool) × Trace) × β :=
  ((record.1.1.map BinaryStoredDimensionRow.erase,record.1.2),record.2)

theorem row_raw_refines (counter bits : List Bool) (depth : ℕ) :
    eraseRecord (view (rowAt counter bits depth)) = eraseRecord (offset depth
      ((BinaryGamePayloadPlan.row counter bits).1.1,
        ((BinaryGamePayloadPlan.row counter bits).1.2,(BinaryGamePayloadPlan.row counter bits).2))) := by
  conv_lhs => unfold rowAt
  conv_rhs => unfold BinaryGamePayloadPlan.row
  dsimp only
  simp only [scan_data]
  split
  · cases hf : (BinaryCanonicalPayloadPlan.read bits).1.1.1 with
    | none => simp only [hf,eraseRecord,view,offset,denote,Option.map_none,scan_trace,scan_work,
        wrap,combine,under_append,under_compose,List.append_nil]; rfl
    | some parsed =>
        simp only [hf]
        have hp := predecessor_refines counter (depth+2)
        let extend : ((Option (List SignedWord × List Bool) × Trace) × (ℕ × ℕ)) →
            ((Option (List SignedWord × List Bool) × Trace) × (ℕ × ℕ)) := fun later =>
          ((later.1.1.map (fun rest => (parsed.1.val::rest.1,rest.2)),
            [.listAllocation 1,.frames (depth+2),.arrayAllocation 48] ++
              (under (depth+2) (BooleanFreshSeedMeasured.scan counter).1.2 ++
              (under (depth+2) (BinaryCanonicalPayloadPlan.read bits).1.1.2 ++
              (under (depth+2) (BinaryStoredDimensionControlMeasured.predecessor counter).1.2 ++ later.1.2)))),
            ((BooleanFreshSeedMeasured.scan counter).2+(BinaryCanonicalPayloadPlan.read bits).1.2+
              (BinaryStoredDimensionControlMeasured.predecessor counter).2+later.2.1+12,
              (BinaryCanonicalPayloadPlan.read bits).2+later.2.2))
        have ih := congrArg extend
          (row_raw_refines (predecessorAt counter (depth+2)).1.1 parsed.2 (depth+2))
        have hc := congrArg (fun smaller => extend (eraseRecord (offset (depth+2)
          ((BinaryGamePayloadPlan.row smaller parsed.2).1.1,
            ((BinaryGamePayloadPlan.row smaller parsed.2).1.2,(BinaryGamePayloadPlan.row smaller parsed.2).2)))))
          (data_refines hp)
        have hg := ih.trans hc
        simp only [extend,eraseRecord,view,offset,denote,Option.map_map,Function.comp_def,
          BinaryStoredDimensionRow.erase,trace_refines hp,charge_refines hp,scan_trace,scan_work,
          wrapList,wrap,combine,under_append,under_compose,List.append_nil] at hg ⊢
        simp only [under,shiftEvent,List.map_cons,List.map_nil,List.cons_append,List.nil_append] at hg ⊢
        exact hg
  · simp only [eraseRecord,view,offset,denote,Option.map_some,BinaryStoredDimensionRow.erase,
      scan_trace,scan_work,wrap,combine,under_append,under_compose,List.append_nil]; rfl
termination_by bits.length
 decreasing_by exact BinaryCanonicalPayloadPlan.read_suffix_lt _ _ (by assumption)

theorem row_refines (counter bits : List Bool) (depth : ℕ) :
    view (rowAt counter bits depth) = offset depth
      ((BinaryGamePayloadPlan.row counter bits).1.1,
        ((BinaryGamePayloadPlan.row counter bits).1.2,(BinaryGamePayloadPlan.row counter bits).2)) := by
  have h := row_raw_refines counter bits depth
  apply Prod.ext
  · apply Prod.ext
    · have hd := congrArg (fun out => out.1.1) h
      change (rowAt counter bits depth).1.1.map BinaryStoredDimensionRow.erase =
        (BinaryGamePayloadPlan.row counter bits).1.1.1.map BinaryStoredDimensionRow.erase at hd
      have hi : Function.Injective (Option.map (@BinaryStoredDimensionRow.erase (BinaryBigEndian.littleValue counter))) := by
        intro first second he
        cases first with
        | none => cases second with
          | none => rfl
          | some b => cases he
        | some a => cases second with
          | none => cases he
          | some b => exact congrArg some (BinaryStoredDimensionRow.erase_injective (Option.some.inj he))
      exact hi hd
    · exact congrArg (fun out => out.1.2) h
  · have hw := congrArg Prod.snd h
    exact hw

theorem row_budget (counter bits : List Bool) (depth : ℕ) : Bounded (rowAt counter bits depth).1.2 := by
  unfold rowAt
  dsimp only
  split
  · split
    · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]; omega
    · rename_i parsed hf
      have hp := (predecessor_budget counter (depth+2)).1
      have hl := row_budget (predecessorAt counter (depth+2)).1.1 parsed.2 (depth+2)
      simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hp hl ⊢
      omega
  · simp only [Bounded,nodes,payload,List.length_cons,List.length_nil]; omega
termination_by bits.length
 decreasing_by exact BinaryCanonicalPayloadPlan.read_suffix_lt _ _ (by assumption)

def row (counter bits : List Bool) :
    (((Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  let produced := finish (rowAt counter bits 0)
  (((produced.1.1,produced.1.2.1),produced.1.2.2),produced.2)

theorem row_compat (counter bits : List Bool) : (row counter bits).1 = BinaryGamePayloadPlan.row counter bits := by
  have h := BinaryNumericalReadbackPlan.finish_compat (row_refines counter bits 0)
  simp only [row,h]

theorem row_price (counter bits : List Bool) :
    (row counter bits).2 ≤ 25*(row counter bits).1.1.1.2.length+5 := by
  exact BinaryNumericalReadbackPlan.finish_bound (rowAt counter bits 0) (row_budget counter bits 0)

end Blotto.BinaryStoredRowPlan

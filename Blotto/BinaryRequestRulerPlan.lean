import Blotto.BinaryRulerPrecisionPlan
import Blotto.BinaryPRGRequestRulersMeasured
import Blotto.BinaryHeaderAccuracyPayloadPlan

/-! Actual accuracy preparation and retained-row request assembly collect
ruler plans and emit once at each boundary. Complete preceding records and
source prices are exact; the added emission price counts reached plans only. -/
namespace Blotto.BinaryRequestRulerPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded)
open RationalLottoResourceSystem
set_option autoImplicit false
set_option maxHeartbeats 4000000

def accuracyAt (words : BinaryAccuracyWords) (depth : ℕ) :
    (BinaryAccuracyRulerReadWork.Prepared × Plan) × ℕ :=
  let ruler := List.replicate 5 false
  let aligned := BinaryRulerPrecisionPlan.shiftedAt words.denominator ruler (depth+2)
  let selected := BinaryRulerPrecisionPlan.precisionAt aligned.1.1 words.numerator (depth+2)
  have hAligned : aligned.1.1 = words.denominator.shifted 5 := by
    rw [data_refines (BinaryRulerPrecisionPlan.shifted_refines words.denominator ruler (depth+2)),
      BinaryRulerPrecisionMeasured.shifted_erases,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,
      BinaryRulerPrecision.shifted_state]
    simp only [ruler,List.length_replicate]
  have hCorrect : selected.1.1 = words.precision := by
    rw [data_refines (BinaryRulerPrecisionPlan.precision_refines aligned.1.1 words.numerator (depth+2)),
      BinaryRulerPrecisionMeasured.precision_erases,
      BinaryRulerPrecisionLifetime.precisionWithTrace_state,hAligned]
    rfl
  ((⟨words,selected.1.1,hCorrect⟩,.join (.block [.listAllocation 5,.frames (depth+2),.arrayAllocation 32])
    (.join aligned.1.2 selected.1.2)),aligned.2+selected.2+32)

theorem accuracy_refines (words : BinaryAccuracyWords) (depth : ℕ) :
    view (accuracyAt words depth) = offset depth (BinaryAccuracyMeasured.prepare words) := by
  have hs := BinaryRulerPrecisionPlan.shifted_refines words.denominator (List.replicate 5 false) (depth+2)
  have hp := BinaryRulerPrecisionPlan.precision_refines
    (BinaryRulerPrecisionMeasured.shifted words.denominator (List.replicate 5 false)).1.1 words.numerator (depth+2)
  simp only [accuracyAt,BinaryAccuracyMeasured.prepare,view,offset,denote,
    data_refines hs,data_refines hp,trace_refines hs,trace_refines hp,charge_refines hs,charge_refines hp,
    wrapList,wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem accuracy_budget (words : BinaryAccuracyWords) (depth : ℕ) :
    Bounded (accuracyAt words depth).1.2 ∧ payload (accuracyAt words depth).1.2 ≤ (accuracyAt words depth).2 := by
  have hs := BinaryRulerPrecisionPlan.shifted_budget words.denominator (List.replicate 5 false) (depth+2)
  have hp := BinaryRulerPrecisionPlan.precision_budget
    (BinaryRulerPrecisionPlan.shiftedAt words.denominator (List.replicate 5 false) (depth+2)).1.1 words.numerator (depth+2)
  simp only [accuracyAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at hs hp ⊢
  omega

def accuracyPrepare (words : BinaryAccuracyWords) := finish (accuracyAt words 0)

theorem accuracyPrepare_compat (words : BinaryAccuracyWords) :
    (accuracyPrepare words).1 = BinaryAccuracyMeasured.prepare words :=
  BinaryNumericalReadbackPlan.finish_compat (accuracy_refines words 0)

theorem accuracyPrepare_price (words : BinaryAccuracyWords) :
    (accuracyPrepare words).2 ≤ 30*(accuracyPrepare words).1.2 := by
  have hb := accuracy_budget words 0
  have he := BinaryNumericalReadbackPlan.finish_bound (accuracyAt words 0) hb.1
  have hw : 4 ≤ (accuracyAt words 0).2 := by unfold accuracyAt; dsimp only; omega
  simp only [accuracyPrepare,BinaryNumericalReadbackPlan.finish_record,view,denote_length] at he ⊢
  omega

def tripleAt {α : Type*} : List α → List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],tail,depth => ((tail,.block [.frames (depth+1)]),2)
  | _::rest,tail,depth =>
      let later := tripleAt rest tail (depth+1)
      ((false::false::false::later.1.1,.join (.block [.frames (depth+1),.listAllocation 3]) later.1.2),later.2+8)

theorem triple_refines {α : Type*} (items : List α) (tail : List Bool) (depth : ℕ) :
    view (tripleAt items tail depth) = offset depth (BinaryPRGRequestRulersMeasured.triple items tail) := by
  induction items generalizing depth with
  | nil => rfl
  | cons item rest ih =>
      have h := ih (depth+1)
      simp only [tripleAt,BinaryPRGRequestRulersMeasured.triple,view,offset,denote,
        data_refines h,trace_refines h,charge_refines h,under_append,under_compose]
      rfl

theorem triple_budget {α : Type*} (items : List α) (tail : List Bool) (depth : ℕ) :
    Bounded (tripleAt items tail depth).1.2 ∧ payload (tripleAt items tail depth).1.2 ≤ (tripleAt items tail depth).2 := by
  induction items generalizing depth with
  | nil => simp [tripleAt,Bounded,nodes,payload]
  | cons item rest ih =>
      have h := ih (depth+1)
      simp only [tripleAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

def choiceAt {α : Type*} (rows : List α) (ruler : List Bool) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let precision := tripleAt ruler BinaryPRGRequestRulers.overhead (depth+2)
  let fields := tripleAt rows precision.1.1 (depth+2)
  ((fields.1.1,.join (.block [.listAllocation 3000,.frames (depth+2),.arrayAllocation 32])
    (.join precision.1.2 fields.1.2)),precision.2+fields.2+12004)

theorem choice_refines {α : Type*} (rows : List α) (ruler : List Bool) (depth : ℕ) :
    view (choiceAt rows ruler depth) = offset depth (BinaryPRGRequestRulersMeasured.choice rows ruler) := by
  have hp := triple_refines ruler BinaryPRGRequestRulers.overhead (depth+2)
  have hf := triple_refines rows (BinaryPRGRequestRulersMeasured.triple ruler BinaryPRGRequestRulers.overhead).1.1 (depth+2)
  simp only [choiceAt,BinaryPRGRequestRulersMeasured.choice,view,offset,denote,
    data_refines hp,data_refines hf,trace_refines hp,trace_refines hf,charge_refines hp,charge_refines hf,
    wrapList,wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem choice_budget {α : Type*} (rows : List α) (ruler : List Bool) (depth : ℕ) :
    Bounded (choiceAt rows ruler depth).1.2 ∧ payload (choiceAt rows ruler depth).1.2 ≤ (choiceAt rows ruler depth).2 := by
  have hp := triple_budget ruler BinaryPRGRequestRulers.overhead (depth+2)
  have hf := triple_budget rows (tripleAt ruler BinaryPRGRequestRulers.overhead (depth+2)).1.1 (depth+2)
  simp only [choiceAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at hp hf ⊢
  omega

def rulerPrecisionAt (accuracy : BinaryAccuracyRulerReadWork.Prepared) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let shifted := BinaryRulerPrecisionPlan.shiftedAt accuracy.words.denominator (List.replicate 5 false) (depth+2)
  let selected := BinaryRulerPrecisionPlan.prepareAt shifted.1.1 accuracy.words.numerator (depth+2)
  let zeros := BinaryRulerControlPlan.falseMapAt selected.1.1 (depth+2)
  ((zeros.1.1,.join (.block [.listAllocation 5,.frames (depth+2),.arrayAllocation 64])
    (.join shifted.1.2 (.join selected.1.2 zeros.1.2))),shifted.2+selected.2+zeros.2+32)

theorem rulerPrecision_refines (accuracy : BinaryAccuracyRulerReadWork.Prepared) (depth : ℕ) :
    view (rulerPrecisionAt accuracy depth) = offset depth (BinaryPRGRequestRulersMeasured.precision accuracy) := by
  have hs := BinaryRulerPrecisionPlan.shifted_refines accuracy.words.denominator (List.replicate 5 false) (depth+2)
  have hp := BinaryRulerPrecisionPlan.prepare_refines
    (BinaryRulerPrecisionMeasured.shifted accuracy.words.denominator (List.replicate 5 false)).1.1 accuracy.words.numerator (depth+2)
  have hz := BinaryRulerControlPlan.falseMap_refines
    (BinaryRulerPrecisionMeasured.prepare
      (BinaryRulerPrecisionMeasured.shifted accuracy.words.denominator (List.replicate 5 false)).1.1 accuracy.words.numerator).1.1 (depth+2)
  simp only [rulerPrecisionAt,BinaryPRGRequestRulersMeasured.precision,view,offset,denote,
    data_refines hs,data_refines hp,data_refines hz,trace_refines hs,trace_refines hp,trace_refines hz,
    charge_refines hs,charge_refines hp,charge_refines hz,wrapList,wrap,combine,
    under_append,under_compose,List.append_nil]
  rfl

theorem rulerPrecision_budget (accuracy : BinaryAccuracyRulerReadWork.Prepared) (depth : ℕ) :
    Bounded (rulerPrecisionAt accuracy depth).1.2 ∧
      payload (rulerPrecisionAt accuracy depth).1.2 ≤ (rulerPrecisionAt accuracy depth).2 := by
  have hs := BinaryRulerPrecisionPlan.shifted_budget accuracy.words.denominator (List.replicate 5 false) (depth+2)
  have hp := BinaryRulerPrecisionPlan.prepare_budget
    (BinaryRulerPrecisionPlan.shiftedAt accuracy.words.denominator (List.replicate 5 false) (depth+2)).1.1 accuracy.words.numerator (depth+2)
  have hz := BinaryRulerControlPlan.falseMap_budget
    (BinaryRulerPrecisionPlan.prepareAt
      (BinaryRulerPrecisionPlan.shiftedAt accuracy.words.denominator (List.replicate 5 false) (depth+2)).1.1 accuracy.words.numerator (depth+2)).1.1 (depth+2)
  simp only [rulerPrecisionAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at hs hp hz ⊢
  omega

def assembleAt {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) (depth : ℕ) :
    (BinaryPRGAccuracyRulerRequest.Request n × Plan) × ℕ :=
  let precision := rulerPrecisionAt accuracy (depth+2)
  let choice := choiceAt rows precision.1.1 (depth+2)
  have hP : precision.1.1 = List.replicate accuracy.precision false :=
    (data_refines (rulerPrecision_refines accuracy (depth+2))).trans (BinaryPRGRequestRulersMeasured.precision_state accuracy)
  have hC : choice.1.1 = List.replicate (coinBitBudget n accuracy.precision) false := by
    rw [data_refines (choice_refines rows precision.1.1 (depth+2)),
      BinaryPRGRequestRulersMeasured.choice_erases,BinaryPRGRequestRulers.choice_state,hP,hRows,List.length_replicate]
  ((⟨⟨checked.val,checked.property,accuracy.words,accuracy.precision,accuracy.correct⟩,header,
      precision.1.1,choice.1.1,hP,hC⟩,.join (.block [.listAllocation n,.frames (depth+n+4),.arrayAllocation 64])
      (.join precision.1.2 choice.1.2)),precision.2+choice.2+8)

theorem assemble_refines {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) (depth : ℕ) :
    view (assembleAt checked accuracy header rows hRows depth) =
      offset depth (BinaryPRGRequestRulersMeasured.assembleWithRows checked accuracy header rows hRows) := by
  have hp := rulerPrecision_refines accuracy (depth+2)
  have hc := choice_refines rows (BinaryPRGRequestRulersMeasured.precision accuracy).1.1 (depth+2)
  simp only [assembleAt,BinaryPRGRequestRulersMeasured.assembleWithRows,view,offset,denote,
    data_refines hp,data_refines hc,trace_refines hp,trace_refines hc,charge_refines hp,charge_refines hc,
    wrapList,wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem assemble_budget {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) (depth : ℕ) :
    Bounded (assembleAt checked accuracy header rows hRows depth).1.2 ∧
      payload (assembleAt checked accuracy header rows hRows depth).1.2 ≤ (assembleAt checked accuracy header rows hRows depth).2 := by
  have hp := rulerPrecision_budget accuracy (depth+2)
  have hc := choice_budget rows (rulerPrecisionAt accuracy (depth+2)).1.1 (depth+2)
  simp only [assembleAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at hp hc ⊢
  omega

def assembleWithEmission {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :=
  finish (assembleAt checked accuracy header rows hRows 0)

theorem assembleWithEmission_compat {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    (assembleWithEmission checked accuracy header rows hRows).1 =
      BinaryPRGRequestRulersMeasured.assembleWithRows checked accuracy header rows hRows :=
  BinaryNumericalReadbackPlan.finish_compat (assemble_refines checked accuracy header rows hRows 0)

theorem assembleWithEmission_price {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List BinaryRationalNormalization.SignedWord) (hRows : rows.length = n) :
    (assembleWithEmission checked accuracy header rows hRows).2 ≤
      30*(assembleWithEmission checked accuracy header rows hRows).1.2 := by
  have hb := assemble_budget checked accuracy header rows hRows 0
  have he := BinaryNumericalReadbackPlan.finish_bound (assembleAt checked accuracy header rows hRows 0) hb.1
  have hw : 4 ≤ (assembleAt checked accuracy header rows hRows 0).2 := by
    unfold assembleAt
    dsimp only
    omega
  simp only [assembleWithEmission,BinaryNumericalReadbackPlan.finish_record,view,denote_length] at he ⊢
  omega

def accuracyRead (frame : List Bool) :
    ((Option (BinaryAccuracyRulerReadWork.Prepared × List Bool) × Trace) × ℕ) × (ℕ × ℕ) :=
  let firstProduced := BinaryHeaderAccuracyPayloadPlan.positive frame
  let first := firstProduced.1
  match first.1.1 with
  | none => (((none,wrap 16 2 [first.1.2]),first.2+4),(firstProduced.2,0))
  | some numerator =>
      let secondProduced := BinaryHeaderAccuracyPayloadPlan.positive numerator.2
      let second := secondProduced.1
      match second.1.1 with
      | none => (((none,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8),(firstProduced.2+secondProduced.2,0))
      | some denominator =>
          let produced := accuracyPrepare ⟨numerator.1,denominator.1⟩
          let prepared := produced.1
          (((some (prepared.1.1,denominator.2),wrap 48 2 [first.1.2,second.1.2,prepared.1.2]),
            first.2+second.2+prepared.2+12),(firstProduced.2+secondProduced.2,produced.2))

theorem accuracyRead_compat (frame : List Bool) :
    ((accuracyRead frame).1,(accuracyRead frame).2.1) = BinaryHeaderAccuracyPayloadPlan.accuracy frame := by
  simp only [accuracyRead,BinaryHeaderAccuracyPayloadPlan.accuracy,accuracyPrepare_compat]
  cases hf : (BinaryHeaderAccuracyPayloadPlan.positive frame).1.1.1 with
  | none => simp only [hf]
  | some numerator =>
      simp only [hf]
      cases hs : (BinaryHeaderAccuracyPayloadPlan.positive numerator.2).1.1.1 <;> simp only [hs]

theorem accuracyRead_price (frame : List Bool) :
    (accuracyRead frame).2.2 ≤ 30*(accuracyRead frame).1.2 := by
  unfold accuracyRead
  dsimp only
  split
  · dsimp only; omega
  · rename_i numerator hf
    split
    · dsimp only; omega
    · rename_i denominator hd
      have hp := accuracyPrepare_price (⟨numerator.1,denominator.1⟩ : BinaryAccuracyWords)
      dsimp only
      omega

end Blotto.BinaryRequestRulerPlan

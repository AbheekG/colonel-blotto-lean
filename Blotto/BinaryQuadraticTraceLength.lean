import Blotto.BinaryQuadraticLifetime

/-! Event-count control for the reached quadratic Boolean arithmetic trace.
The recorded allocation events pay for the structural trace entries. This is
an observer bound, not a native runtime or trace-materialization price. -/
namespace Blotto.BinaryQuadraticTraceLength
open BinarySeedPreparationSpace BinaryBooleanPrimitiveLifetime BinaryRationalNormalization
set_option autoImplicit false
set_option maxHeartbeats 1000000

private def bounded (trace : Trace) : Prop :=
  trace.length ≤ 2 * (listCells trace + arraySlots trace)

private theorem bounded_append {a b : Trace} (ha : bounded a) (hb : bounded b) :
    bounded (a ++ b) := by
  simp only [bounded,List.length_append,listCells_append,arraySlots_append] at *
  omega

private theorem bounded_under {trace : Trace} (depth : ℕ) (h : bounded trace) :
    bounded (under depth trace) := by
  have hl : (under depth trace).length = trace.length := by simp [under]
  simpa only [bounded,hl,listCells_under,arraySlots_under] using h

private theorem scan_bounded (bits : List Bool) : bounded (scanWithTrace bits).2 := by
  induction bits with
  | nil => simp [bounded,scanWithTrace,listCells,arraySlots]
  | cons bit rest ih =>
      cases bit
      · change bounded ([.frames 1,.arrayAllocation 4] ++ under 1 (scanWithTrace rest).2)
        apply bounded_append
        · simp [bounded,listCells,arraySlots]
        · exact bounded_under 1 ih
      · simp [bounded,scanWithTrace,listCells,arraySlots]

private theorem difference_bounded (first second : List Bool) :
    bounded (differenceWithTrace first second).2 := by
  simp [bounded,differenceWithTrace,listCells,arraySlots]
  omega

private theorem divide_bounded (first second : List Bool) :
    bounded (divideWithTrace first second).2 := by
  simp [bounded,divideWithTrace,listCells,arraySlots]
  omega

private theorem trim_bounded (bits : List Bool) :
    bounded (trimWithTrace bits).2 := by
  simp [bounded,trimWithTrace,listCells,arraySlots]
  omega

private theorem first_bounded (first : List Bool) :
    bounded (BinarySteinGCDLifetime.firstTrace first) := by
  unfold BinarySteinGCDLifetime.firstTrace
  apply bounded_append
  · simp [bounded,listCells,arraySlots]
  · exact bounded_under 2 (scan_bounded first)

private theorem both_bounded (first second : List Bool) :
    bounded (BinarySteinGCDLifetime.bothTrace first second) := by
  unfold BinarySteinGCDLifetime.bothTrace
  exact bounded_append (first_bounded first) (bounded_under 2 (scan_bounded second))

private theorem singleton_bounded (cells : ℕ) (h : 0 < cells) :
    bounded [.listAllocation cells] := by
  simp [bounded,listCells,arraySlots]
  omega

private theorem loop_bounded (ruler first second : List Bool) :
    bounded (BinarySteinGCDLifetime.loopWithTrace ruler first second).2 := by
  induction ruler generalizing first second with
  | nil => exact first_bounded first
  | cons unused ruler ih =>
      unfold BinarySteinGCDLifetime.loopWithTrace
      dsimp only
      split
      · split
        · cases first with
          | nil => simp_all [scanWithTrace]
          | cons a first =>
              cases second with
              | nil => simp_all [scanWithTrace]
              | cons b second =>
                  cases a <;> cases b <;> dsimp only
                  · exact bounded_append
                      (bounded_append (both_bounded (false::first) (false::second))
                        (singleton_bounded 1 (by omega)))
                      (bounded_under 1 (ih first second))
                  · exact bounded_append
                      (bounded_append (both_bounded (false::first) (true::second))
                        (singleton_bounded 1 (by omega)))
                      (bounded_under 1 (ih first (true::second)))
                  · exact bounded_append
                      (bounded_append (both_bounded (true::first) (false::second))
                        (singleton_bounded 1 (by omega)))
                      (bounded_under 1 (ih (true::first) second))
                  · split
                    · exact bounded_append
                        (bounded_append
                          (bounded_append (both_bounded (true::first) (true::second))
                            (singleton_bounded 2 (by omega)))
                          (bounded_under 2 (difference_bounded (true::first) (true::second))))
                        (bounded_under 1 (ih (true::first)
                          (differenceWithTrace (true::first) (true::second)).1.bits.tail))
                    · exact bounded_append
                        (bounded_append
                          (bounded_append (both_bounded (true::first) (true::second))
                            (singleton_bounded 2 (by omega)))
                          (bounded_under 2 (difference_bounded (true::first) (true::second))))
                        (bounded_under 1 (ih
                          (differenceWithTrace (true::first) (true::second)).1.bits.tail
                          (true::second)))
        · exact both_bounded first second
      · exact first_bounded first

private theorem append_length (first second : List Bool) :
    (BinaryPRGOutputLifetime.appendWithTrace first second).2.length = 2*first.length+1 := by
  induction first with
  | nil => rfl
  | cons bit rest ih =>
      simp only [BinaryPRGOutputLifetime.appendWithTrace,List.length_append,
        List.length_cons,List.length_nil,under,List.length_map,ih]
      omega

private theorem append_near_bounded (first second : List Bool) :
    (BinaryPRGOutputLifetime.appendWithTrace first second).2.length ≤
      2 * (listCells (BinaryPRGOutputLifetime.appendWithTrace first second).2 +
        arraySlots (BinaryPRGOutputLifetime.appendWithTrace first second).2) + 1 := by
  rw [append_length,BinaryPRGOutputLifetime.appendWithTrace_cells,
    BinaryPRGOutputLifetime.appendWithTrace_arrays]
  omega

private theorem gcd_bounded (first second : List Bool) :
    bounded (BinarySteinGCDLifetime.gcdWithTrace first second).2 := by
  let ruler := BinaryPRGOutputLifetime.appendWithTrace first second
  let result := BinarySteinGCDLifetime.loopWithTrace ruler.1 first second
  let trimmed := trimWithTrace result.1
  change bounded ([.frames 2,.arrayAllocation 16] ++
    under 2 ruler.2 ++ under 2 result.2 ++ under 2 trimmed.2)
  have hRuler : ruler.2.length ≤ 2*(listCells ruler.2+arraySlots ruler.2)+1 :=
    append_near_bounded first second
  have hHead : bounded ([.frames 2,.arrayAllocation 16] ++ under 2 ruler.2) := by
    have hl : (under 2 ruler.2).length = ruler.2.length := by simp [under]
    simp only [bounded,List.length_append,listCells_append,arraySlots_append,
      listCells_under,arraySlots_under] at ⊢
    simp only [List.length_cons,List.length_nil,listCells,arraySlots]
    omega
  exact bounded_append
    (bounded_append hHead (bounded_under 2 (loop_bounded ruler.1 first second)))
    (bounded_under 2 (trim_bounded result.1))

private theorem normalize_bounded (word : SignedWord) :
    bounded (BinaryQuadraticLifetime.normalizeWithTrace word).2 := by
  let common := BinarySteinGCDLifetime.gcdWithTrace word.numerator word.denominator
  let numerator := divideWithTrace word.numerator common.1
  let denominator := divideWithTrace word.denominator common.1
  let sign := scanWithTrace numerator.1.1
  change bounded ([.frames 2,.arrayAllocation 16] ++ under 2 common.2 ++
    under 2 numerator.2 ++ under 2 denominator.2 ++ under 2 sign.2)
  exact bounded_append
    (bounded_append
      (bounded_append
        (bounded_append (by simp [bounded,listCells,arraySlots])
          (bounded_under 2 (gcd_bounded word.numerator word.denominator)))
        (bounded_under 2 (divide_bounded word.numerator common.1)))
      (bounded_under 2 (divide_bounded word.denominator common.1)))
    (bounded_under 2 (scan_bounded numerator.1.1))

private theorem canonicalize_bounded (word : SignedWord) :
    bounded (BinaryQuadraticLifetime.canonicalizeWithTrace word).2 := by
  let normalized := BinaryQuadraticLifetime.normalizeWithTrace word
  let numerator := trimWithTrace normalized.1.numerator
  let denominator := trimWithTrace normalized.1.denominator
  change bounded ([.frames 2,.arrayAllocation 16] ++ under 2 normalized.2 ++
    under 2 numerator.2 ++ under 2 denominator.2)
  exact bounded_append
    (bounded_append
      (bounded_append (by simp [bounded,listCells,arraySlots])
        (bounded_under 2 (normalize_bounded word)))
      (bounded_under 2 (trim_bounded normalized.1.numerator)))
    (bounded_under 2 (trim_bounded normalized.1.denominator))

private theorem raw_bounded (op : RealArithmeticOp) (first second : SignedWord) :
    bounded (BinaryQuadraticLifetime.rawWithTrace op first second).2 := by
  simp [bounded,BinaryQuadraticLifetime.rawWithTrace,listCells,arraySlots]
  omega

theorem apply_event_length (op : RealArithmeticOp) (first second : SignedWord) :
    (BinaryQuadraticLifetime.applyWithTrace op first second).2.length ≤
      2 * (listCells (BinaryQuadraticLifetime.applyWithTrace op first second).2 +
        arraySlots (BinaryQuadraticLifetime.applyWithTrace op first second).2) := by
  let raw := BinaryQuadraticLifetime.rawWithTrace op first second
  let canonical := BinaryQuadraticLifetime.canonicalizeWithTrace raw.1
  change bounded ([.frames 2,.arrayAllocation 16] ++ under 2 raw.2 ++ under 2 canonical.2)
  exact bounded_append
    (bounded_append (by simp [bounded,listCells,arraySlots])
      (bounded_under 2 (raw_bounded op first second)))
    (bounded_under 2 (canonicalize_bounded raw.1))

theorem apply_event_bound (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hFirst : width first ≤ W)
    (hSecond : width second ≤ W) :
    (BinaryQuadraticLifetime.applyWithTrace op first second).2.length ≤
      2 * BinaryQuadraticLifetime.opcodeBound W := by
  have hLength := apply_event_length op first second
  have hAllocation :=
    (BinaryQuadraticLifetime.applyWithTrace_bounds op first second W hFirst hSecond).1
  omega

end Blotto.BinaryQuadraticTraceLength

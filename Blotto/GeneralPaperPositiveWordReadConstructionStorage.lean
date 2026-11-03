import Blotto.GeneralPaperAccuracyReadMetadataStorage

/-! Complete native positive-word reader storage. The primary Boolean
parse and repeated delimiter search, all natural metadata traversals,
returned word/suffix owners and caller arithmetic scratch are explicit.
Rejected/truncated/zero frames use the same literal native branches. -/
namespace Blotto.GeneralPaperPositiveWordReadConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBooleanRulerWorkStorage
open GeneralPaperAccuracyReadMetadataStorage BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def dataTrace (frame : List Bool) : Trace :=
  match UnaryPayload.readReversed frame with
  | none => wrap 16 2 [(BinaryUnaryPayloadLifetime.readReversedWithTrace frame).2]
  | some pair => wrap 24 2 [(BinaryUnaryPayloadLifetime.readReversedWithTrace frame).2,
      (BinaryPositiveWordLifetime.parseWithTrace pair.1).2]

theorem data_trace_eq (frame : List Bool) : dataTrace frame=(BinaryPositiveWordLifetime.readWithTrace frame).2 := by
  unfold dataTrace BinaryPositiveWordLifetime.readWithTrace
  dsimp only
  rw [BinaryUnaryPayloadLifetime.readReversedWithTrace_state]
  cases UnaryPayload.readReversed frame <;> rfl

def returnedFoot (W : ℕ) (frame : List Bool) : ℕ :=
  match (BinaryPositiveWordReadWork.read frame).1 with
  | none => 0
  | some pair => wordFoot W pair.1+listFootprint W (fun _ : Bool => 1) pair.2+32*W

def controls (frame : List Bool) : List ℕ :=
  [UnaryPayload.readSteps frame,(BinaryPositiveWordReadWork.read frame).2]++match UnaryPayload.readReversed frame with
  | none => []
  | some pair => [pair.1.length,2*pair.1.length,2*pair.1.length+1,
      UnaryPayload.readSteps frame+2*pair.1.length,UnaryPayload.readSteps frame+2*pair.1.length+1]

def scratch (frame : List Bool) : ℕ :=
  match UnaryPayload.readReversed frame with
  | none => 0
  | some pair =>
    GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a*b) 2 pair.1.length+
      GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) (UnaryPayload.readSteps frame) (2*pair.1.length)+
      GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) (UnaryPayload.readSteps frame+2*pair.1.length) 1

def lengthWindow (W : ℕ) (frame : List Bool) : ℕ :=
  match UnaryPayload.readReversed frame with | none => 0 | some pair => lengthMeta W pair.1

def window (W : ℕ) (frame : List Bool) : ℕ :=
  listFootprint W (fun _ : Bool => 1) frame+returnedFoot W frame+
    (1+4*W)*(usage (dataTrace frame)+usage (BinaryUnaryPayloadLifetime.findWithTrace frame).2)+
    stepsMeta W frame+lengthWindow W frame+node W (controls frame)+scratch frame

def inputProfile (W E : ℕ) : ℕ := E*(1+2*W)+32*W
def returnProfile (W E : ℕ) : ℕ := E*(1+2*W)+160*W

def profile (W E : ℕ) : ℕ :=
  inputProfile W E+returnProfile W E+272*(E+1)*(1+4*W)+stepsProfile W E+lengthProfile W E+
    2*budget W (4*(E+1))+6*(1+binaryWordWidth (4*(E+1)))

theorem returned_bound (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) : returnedFoot W frame≤returnProfile W E := by
  unfold returnedFoot
  cases hr:(BinaryPositiveWordReadWork.read frame).1 with
  | none => dsimp only;unfold returnProfile;omega
  | some pair =>
    have h := BinaryPositiveWordReadWork.read_consumed frame pair hr
    have hw := word_bound W pair.1
    have hs := list_bound W 1 (fun _ : Bool => 1) pair.2 (fun _ _ => le_rfl)
    have hm := Nat.mul_le_mul_right (1+2*W) (show pair.1.width+pair.2.length≤E by omega)
    dsimp only
    unfold returnProfile
    nlinarith only [hw,hs,hm]

theorem payload_length (frame : List Bool) (pair : List Bool×List Bool)
    (h : UnaryPayload.readReversed frame=some pair) : pair.1.length≤frame.length := by
  have hp := UnaryPayload.readReversed_length frame pair.1 pair.2 h
  omega

theorem length_bound (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) : lengthWindow W frame≤lengthProfile W E := by
  unfold lengthWindow
  cases hp:UnaryPayload.readReversed frame with
  | none => dsimp only;omega
  | some pair =>
    have hl : pair.1.length≤E := (payload_length frame pair hp).trans hc
    have h := GeneralPaperAccuracyReadMetadataStorage.length_bound W E pair.1 hl
    dsimp only
    exact h.trans (Nat.mul_le_mul_right (budget W E) (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hl 1)))

theorem header_bound (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) : node W (controls frame)≤2*budget W (4*(E+1)) := by
  have hr := BinaryPositiveWordReadWork.read_bound frame
  have hs := UnaryPayload.readSteps_bound frame
  apply node_bound
  · unfold controls
    split <;> norm_num
  · intro z hz
    unfold controls at hz
    split at hz
    · simp only [List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl <;> omega
    · rename_i pair hp
      have hl := payload_length frame pair hp
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with (rfl|rfl)|(rfl|rfl|rfl|rfl|rfl) <;> omega

theorem scratch_bound (E : ℕ) (frame : List Bool) (hc : frame.length≤E) : scratch frame≤6*(1+binaryWordWidth (4*(E+1))) := by
  have hs := UnaryPayload.readSteps_bound frame
  unfold scratch
  cases hp:UnaryPayload.readReversed frame with
  | none => dsimp only;omega
  | some pair =>
    have hl := payload_length frame pair hp
    have a := GeneralPaperNaturalPrimitivePrice.binary_le (fun w => w) (fun _ _ h => h) (fun a b => a*b)
      2 pair.1.length (4*(E+1)) (by omega) (by omega) (by omega)
    have b := GeneralPaperNaturalPrimitivePrice.binary_le (fun w => w) (fun _ _ h => h) (fun a b => a+b)
      (UnaryPayload.readSteps frame) (2*pair.1.length) (4*(E+1)) (by omega) (by omega) (by omega)
    have c := GeneralPaperNaturalPrimitivePrice.binary_le (fun w => w) (fun _ _ h => h) (fun a b => a+b)
      (UnaryPayload.readSteps frame+2*pair.1.length) 1 (4*(E+1)) (by omega) (by omega) (by omega)
    dsimp only
    omega

theorem bounded (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) : window W frame≤profile W E := by
  have hi := list_bound W 1 (fun _ : Bool => 1) frame (fun _ _ => le_rfl)
  have hi' := hi.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (1+2*W) hc) _)
  have hr := returned_bound W E frame hc
  have hd := BinaryPositiveWordLifetime.readWithTrace_usage frame
  rw [←data_trace_eq] at hd
  have hf := BinaryUnaryPayloadLifetime.findWithTrace_usage frame
  have hData : usage (dataTrace frame)+usage (BinaryUnaryPayloadLifetime.findWithTrace frame).2≤272*(E+1) := by omega
  have hData' := Nat.mul_le_mul_left (1+4*W) hData
  have hs := steps_bound W E frame hc
  have hs' := hs.trans (Nat.mul_le_mul_right (budget W (E+1)) (by omega : 4*(frame.length+1)+2≤4*(E+1)+2))
  have hl := length_bound W E frame hc
  have hh := header_bound W E frame hc
  have hScratch := scratch_bound E frame hc
  unfold window profile inputProfile returnProfile stepsProfile at *
  nlinarith only [hi',hr,hData',hs',hl,hh,hScratch]

theorem returned_covered (W : ℕ) (frame : List Bool) : returnedFoot W frame≤window W frame := by unfold window;omega

@[fun_prop]
theorem scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile W E) := by
  unfold profile inputProfile returnProfile budget
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem profile_rate (W E : Input → ℕ) (hW : Tight W) (hE : Small E) : Linear (fun x => profile (W x) (E x)) E := by
  have hw := of_tight hW
  have hp := poly_tight W hW
  have hs := steps_rate W E hW hE
  have hl := length_rate W E hW hE
  unfold profile inputProfile returnProfile budget natBits
  fun_prop

end Blotto.GeneralPaperPositiveWordReadConstructionStorage

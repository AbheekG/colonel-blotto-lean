import Blotto.BinaryPackedReadPlan
import Blotto.BinaryWrapperEmission
import Blotto.BinaryHeapPairSourceMeasured
import Blotto.BinaryHeapPairRegistersMeasured
import Blotto.BinaryRegisterStoragePlan
import Blotto.BinaryPRGHeapPairLifetime

/-! Four actual packed-read plans feed the pair source and register program.
Their old records are exact. Actual register-tree visits and one output
emission join reached leaf/wrapper work in the existing packed counter; all old bounds keep
their constants. Native primitive/metadata interpretation remains outside this scope. -/
namespace Blotto.BinaryPackedPairPlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage BinaryTracePlanMeasured
open BinaryNumericalReadbackPlan (finish)
set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def four (a b c d : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.frames 2,.arrayAllocation 32])
    (.join (.shifted 2 a) (.join (.shifted 2 b) (.join (.shifted 2 c) (.shifted 2 d))))) []
  (emitted.1.1,emitted.1.2+emitted.2)

theorem four_trace (a b c d : Trace) : (four a b c d).1 = wrap 32 2 [a,b,c,d] := by
  simp only [four,emitFull_erases,emit_data,denote,List.append_nil,wrap,combine]

theorem four_length (a b c d : Trace) : (four a b c d).1.length = a.length+b.length+c.length+d.length+2 := by
  simp only [four,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

theorem four_price (a b c d : Trace) : (four a b c d).2 ≤ 25*(four a b c d).1.length+5 := by
  simp only [four,emitFull_erases,emit_length,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

def six (allocated : ℕ) (a b c d e f : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.listAllocation allocated,.frames 2,.arrayAllocation 32])
    (.join (.shifted 2 a) (.join (.shifted 2 b) (.join (.shifted 2 c)
      (.join (.shifted 2 d) (.join (.shifted 2 e) (.shifted 2 f))))))) []
  (emitted.1.1,emitted.1.2+emitted.2)

theorem six_trace (allocated : ℕ) (a b c d e f : Trace) :
    (six allocated a b c d e f).1 = wrapList allocated 32 2 [a,b,c,d,e,f] := by
  simp only [six,emitFull_erases,emit_data,denote,List.append_nil,wrapList,wrap,combine]
  rfl

theorem six_length (allocated : ℕ) (a b c d e f : Trace) :
    (six allocated a b c d e f).1.length = a.length+b.length+c.length+d.length+e.length+f.length+3 := by
  simp only [six,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

theorem six_price (allocated : ℕ) (a b c d e f : Trace) :
    (six allocated a b c d e f).2 ≤ 25*(six allocated a b c d e f).1.length+5 := by
  simp only [six,emitFull_erases,emit_length,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

theorem packed_data {width : ℕ} (data : BinaryPRGHeapPackedStore.Packed width) (address : FixedBinaryWord width) :
    (BinaryPackedReadPlan.readWithEmission data address).1.1.1 = (data.readWithWork address).1 := by
  rw [BinaryPackedReadPlan.read_compat,BinaryHeapPackedReadMeasured.read_data]

def source (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : ((BinaryRationalPairProgram.Source × Trace) × ℕ) × ℕ :=
  let ap := BinaryPackedReadPlan.readWithEmission (pack limits) first.word
  let a := ap.1
  let bp := BinaryPackedReadPlan.readWithEmission (pack limits) second.word
  let b := bp.1
  let cp := BinaryPackedReadPlan.readWithEmission state.packed first.word
  let c := cp.1
  let dp := BinaryPackedReadPlan.readWithEmission state.packed second.word
  let d := dp.1
  have hA := (packed_data (pack limits) first.word).trans
    (BinaryPRGHeapStoredTree.readWithWork_value limits first.word)
  have hB := (packed_data (pack limits) second.word).trans
    (BinaryPRGHeapStoredTree.readWithWork_value limits second.word)
  have hCRead := (packed_data state.packed first.word).trans
    (BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes first.word)
  have hD := (packed_data state.packed second.word).trans
    (BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes second.word)
  have hActive : state.reference.state.active = first :: second :: tail :=
    state.certified.choose_spec.2.symm.trans he
  let emitted := four a.1.2 b.1.2 c.1.2 d.1.2
  (((⟨a.1.1,b.1.1,c.1.1,d.1.1,
    (by rw [hA]; exact hC first),(by rw [hB]; exact hC second),
    (by rw [hCRead]; exact state.reference.canonical first),(by rw [hD]; exact state.reference.canonical second),
    (by rw [hCRead,hA]; exact state.reference.interior first (by
      rw [hActive]; simp)),
    (by rw [hD,hB]; exact state.reference.interior second (by
      rw [hActive]; simp))⟩,
    emitted.1),a.2+b.2+c.2+d.2+8),ap.2+bp.2+cp.2+dp.2+emitted.2)


theorem source_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (source (hC := hC) limits state first second tail he).1 = BinaryHeapPairSourceMeasured.source (hC := hC) limits state first second tail he := by
  simp only [source,BinaryHeapPairSourceMeasured.source,BinaryPackedReadPlan.read_compat,four_trace]

theorem source_price (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (source (hC := hC) limits state first second tail he).2 ≤
      60*(source (hC := hC) limits state first second tail he).1.1.2.length := by
  have ha := BinaryPackedReadPlan.read_emission_bound (pack limits) first.word
  have hb := BinaryPackedReadPlan.read_emission_bound (pack limits) second.word
  have hc := BinaryPackedReadPlan.read_emission_bound state.packed first.word
  have hd := BinaryPackedReadPlan.read_emission_bound state.packed second.word
  have hw := four_price
    (BinaryPackedReadPlan.readWithEmission (pack limits) first.word).1.1.2
    (BinaryPackedReadPlan.readWithEmission (pack limits) second.word).1.1.2
    (BinaryPackedReadPlan.readWithEmission state.packed first.word).1.1.2
    (BinaryPackedReadPlan.readWithEmission state.packed second.word).1.1.2
  simp only [four_length] at hw
  simp only [source,four_length]
  omega

@[irreducible] def pairMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : (((BinaryPRGWordControllerPairOutputs.Outputs × Trace) × ℕ) × ℕ) × ℕ :=
  let produced := source (hC := hC) limits state first second tail he
  let input := produced.1
  let registers := BinaryRegisterStoragePlan.outputsWithEmission input.1.1
  let outputs := registers.1
  let emitted := BinaryWrapperEmission.two 16 2 input.1.2 outputs.1.1.2
  ((((outputs.1.1.1,emitted.1),input.2+BinaryRegisterMetadataPlan.sourceCharge input.1.1+outputs.1.2+4),outputs.2),produced.2+emitted.2+registers.2)

theorem pair_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (pairMeasured (hC := hC) limits state first second tail he).1 = BinaryHeapPairSourceMeasured.pairMeasured (hC := hC) limits state first second tail he := by
  simp only [pairMeasured,BinaryHeapPairSourceMeasured.pairMeasured,source_compat,BinaryWrapperEmission.two_trace,BinaryRegisterStoragePlan.outputs_compat,BinaryRegisterMetadataPlan.source_exact]

theorem pair_price (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (pairMeasured (hC := hC) limits state first second tail he).2 ≤
      100*(pairMeasured (hC := hC) limits state first second tail he).1.1.1.2.length := by
  have h := source_price (hC := hC) limits state first second tail he
  have hr := BinaryRegisterStoragePlan.outputs_price (source (hC := hC) limits state first second tail he).1.1.1
  simp only [pairMeasured,BinaryWrapperEmission.two_work,BinaryWrapperEmission.two_length]
  omega

end Blotto.BinaryPackedPairPlan

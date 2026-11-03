import Blotto.BinaryExecutionCharges
import Blotto.BinaryTracePlanMeasured
import Blotto.BinaryPRGHeapTraceUsage

/-! Constant-arity outer wrappers emit one plan and return its actual
list/control/shift charge. Proof observers of trace length are not selected
runtime operations; scalar/header/reference/allocator pricing is separate. -/
namespace Blotto.BinaryWrapperEmission
open BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryPRGHeapTraceUsage
set_option autoImplicit false

def one (slots frames : ℕ) (trace : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.frames frames,.arrayAllocation slots]) (.shifted 2 trace)) []
  (emitted.1.1,emitted.1.2+emitted.2)

def two (slots frames : ℕ) (first second : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.frames frames,.arrayAllocation slots])
    (.join (.shifted 2 first) (.shifted 2 second))) []
  (emitted.1.1,emitted.1.2+emitted.2)

def listTwo (allocated slots frames : ℕ) (first second : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots])
    (.join (.shifted 2 first) (.shifted 2 second))) []
  (emitted.1.1,emitted.1.2+emitted.2)

theorem one_trace (slots frames : ℕ) (trace : Trace) : (one slots frames trace).1 = wrap slots frames [trace] := by
  simp only [one,emitFull_erases,emit_data,denote,List.append_nil,wrap,combine]

theorem two_trace (slots frames : ℕ) (first second : Trace) :
    (two slots frames first second).1 = wrap slots frames [first,second] := by
  simp only [two,emitFull_erases,emit_data,denote,List.append_nil,wrap,combine]

theorem listTwo_trace (allocated slots frames : ℕ) (first second : Trace) :
    (listTwo allocated slots frames first second).1 = wrapList allocated slots frames [first,second] := by
  simp only [listTwo,emitFull_erases,emit_data,denote,List.append_nil,wrapList,wrap,combine]
  rfl

theorem one_work (slots frames : ℕ) (trace : Trace) : (one slots frames trace).2 = 5*trace.length+14 := by
  simp only [one,emitFull_erases,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

theorem two_work (slots frames : ℕ) (first second : Trace) :
    (two slots frames first second).2 = 5*first.length+5*second.length+18 := by
  simp only [two,emitFull_erases,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

theorem listTwo_work (allocated slots frames : ℕ) (first second : Trace) :
    (listTwo allocated slots frames first second).2 = 5*first.length+5*second.length+22 := by
  simp only [listTwo,emitFull_erases,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

theorem one_length (slots frames : ℕ) (trace : Trace) : (one slots frames trace).1.length = trace.length+2 := by
  simp only [one,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

theorem two_length (slots frames : ℕ) (first second : Trace) :
    (two slots frames first second).1.length = first.length+second.length+2 := by
  simp only [two,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

theorem listTwo_length (allocated slots frames : ℕ) (first second : Trace) :
    (listTwo allocated slots frames first second).1.length = first.length+second.length+3 := by
  simp only [listTwo,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

end Blotto.BinaryWrapperEmission

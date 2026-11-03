import Blotto.BinaryWrapperEmission

/-! Flattened constant-arity seed/generated wrappers emit once at final depths.
The complete old trace and actual emission counter are returned together. -/
namespace Blotto.BinarySeedWrapperEmission
open BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryPRGHeapTraceUsage
set_option autoImplicit false

def nested (preparation store drawn : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.frames 2,.arrayAllocation 32])
    (.join (.shifted 2 preparation) (.join (.block [.frames 4,.arrayAllocation 16])
      (.join (.shifted 4 store) (.shifted 4 drawn))))) []
  (emitted.1.1,emitted.1.2+emitted.2)

def three (slots frames : ℕ) (first second third : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.frames frames,.arrayAllocation slots])
    (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) []
  (emitted.1.1,emitted.1.2+emitted.2)

theorem nested_trace (preparation store drawn : Trace) :
    (nested preparation store drawn).1 = wrap 32 2 [preparation,wrap 16 2 [store,drawn]] := by
  simp only [nested,emitFull_erases,emit_data,denote,List.append_nil,wrap,combine,
    BinaryTraceDepth.under_append,BinaryTraceDepth.under_compose,List.append_assoc]
  rfl

theorem nested_work (preparation store drawn : Trace) :
    (nested preparation store drawn).2 = 5*preparation.length+5*store.length+5*drawn.length+34 := by
  simp only [nested,emitFull_erases,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

theorem nested_length (preparation store drawn : Trace) :
    (nested preparation store drawn).1.length = preparation.length+store.length+drawn.length+4 := by
  simp only [nested,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

theorem three_trace (slots frames : ℕ) (first second third : Trace) :
    (three slots frames first second third).1 = wrap slots frames [first,second,third] := by
  simp only [three,emitFull_erases,emit_data,denote,List.append_nil,wrap,combine]

theorem three_work (slots frames : ℕ) (first second third : Trace) :
    (three slots frames first second third).2 = 5*first.length+5*second.length+5*third.length+22 := by
  simp only [three,emitFull_erases,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

theorem three_length (slots frames : ℕ) (first second third : Trace) :
    (three slots frames first second third).1.length = first.length+second.length+third.length+2 := by
  simp only [three,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

end Blotto.BinarySeedWrapperEmission

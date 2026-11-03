import Blotto.BinaryTraceScalarWork
import Blotto.BinarySeedWrapperEmission
import Blotto.BinaryInitialWrapperEmission

/-! All six reached constant-arity wrapper plans instantiate the emitter's
Boolean scalar-addition work bound. The final list/control-plus-shift charge
addition is included. Borrowed event scalar fields fit their retained usage.
Canonical scalar representation formation and full native models remain separate. -/
namespace Blotto.BinaryWrapperScalarWork
open BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryPRGHeapTraceUsage
open BinaryTraceScalarWork
set_option autoImplicit false
set_option maxHeartbeats 1000000

def one (slots frames : ℕ) (trace : Trace) : ℕ := finishWork (.join (.block [.frames frames,.arrayAllocation slots]) (.shifted 2 trace)) []

theorem one_bound (slots frames : ℕ) (trace : Trace) :
    one slots frames trace ≤ 88*(trace.length+6)*(binaryWordWidth (4*trace.length+slots+frames+usage trace+32)+1) := by
  have h0 := traceScalar_usage trace
  have h := finish_bound (.join (.block [.frames frames,.arrayAllocation slots]) (.shifted 2 trace)) [] (4*trace.length+slots+frames+usage trace+32)
    (by simp only [payload,nodes,List.length_cons,List.length_nil]; omega)
    (by simp only [planScalar,traceScalar,eventScalar]; omega)
  simp only [one]
  simp only [payload,nodes,List.length_cons,List.length_nil] at h
  nlinarith only [h]

def two (slots frames : ℕ) (first second : Trace) : ℕ := finishWork (.join (.block [.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.shifted 2 second))) []

theorem two_bound (slots frames : ℕ) (first second : Trace) :
    two slots frames first second ≤ 88*(first.length+second.length+8)*(binaryWordWidth (4*first.length+4*second.length+slots+frames+usage first+usage second+40)+1) := by
  have h0 := traceScalar_usage first
  have h1 := traceScalar_usage second
  have h := finish_bound (.join (.block [.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.shifted 2 second))) [] (4*first.length+4*second.length+slots+frames+usage first+usage second+40)
    (by simp only [payload,nodes,List.length_cons,List.length_nil]; omega)
    (by simp only [planScalar,traceScalar,eventScalar]; omega)
  simp only [two]
  simp only [payload,nodes,List.length_cons,List.length_nil] at h
  nlinarith only [h]

def listTwo (allocated slots frames : ℕ) (first second : Trace) : ℕ := finishWork (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.shifted 2 second))) []

theorem listTwo_bound (allocated slots frames : ℕ) (first second : Trace) :
    listTwo allocated slots frames first second ≤ 88*(first.length+second.length+9)*(binaryWordWidth (4*first.length+4*second.length+allocated+slots+frames+usage first+usage second+44)+1) := by
  have h0 := traceScalar_usage first
  have h1 := traceScalar_usage second
  have h := finish_bound (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.shifted 2 second))) [] (4*first.length+4*second.length+allocated+slots+frames+usage first+usage second+44)
    (by simp only [payload,nodes,List.length_cons,List.length_nil]; omega)
    (by simp only [planScalar,traceScalar,eventScalar]; omega)
  simp only [listTwo]
  simp only [payload,nodes,List.length_cons,List.length_nil] at h
  nlinarith only [h]

def three (slots frames : ℕ) (first second third : Trace) : ℕ := finishWork (.join (.block [.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) []

theorem three_bound (slots frames : ℕ) (first second third : Trace) :
    three slots frames first second third ≤ 88*(first.length+second.length+third.length+10)*(binaryWordWidth (4*first.length+4*second.length+4*third.length+slots+frames+usage first+usage second+usage third+48)+1) := by
  have h0 := traceScalar_usage first
  have h1 := traceScalar_usage second
  have h2 := traceScalar_usage third
  have h := finish_bound (.join (.block [.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) [] (4*first.length+4*second.length+4*third.length+slots+frames+usage first+usage second+usage third+48)
    (by simp only [payload,nodes,List.length_cons,List.length_nil]; omega)
    (by simp only [planScalar,traceScalar,eventScalar]; omega)
  simp only [three]
  simp only [payload,nodes,List.length_cons,List.length_nil] at h
  nlinarith only [h]

def nested (preparation store drawn : Trace) : ℕ := finishWork (.join (.block [.frames 2,.arrayAllocation 32]) (.join (.shifted 2 preparation) (.join (.block [.frames 4,.arrayAllocation 16]) (.join (.shifted 4 store) (.shifted 4 drawn))))) []

theorem nested_bound (preparation store drawn : Trace) :
    nested preparation store drawn ≤ 88*(preparation.length+store.length+drawn.length+14)*(binaryWordWidth (4*preparation.length+4*store.length+4*drawn.length+usage preparation+usage store+usage drawn+120)+1) := by
  have h0 := traceScalar_usage preparation
  have h1 := traceScalar_usage store
  have h2 := traceScalar_usage drawn
  have h := finish_bound (.join (.block [.frames 2,.arrayAllocation 32]) (.join (.shifted 2 preparation) (.join (.block [.frames 4,.arrayAllocation 16]) (.join (.shifted 4 store) (.shifted 4 drawn))))) [] (4*preparation.length+4*store.length+4*drawn.length+usage preparation+usage store+usage drawn+120)
    (by simp only [payload,nodes,List.length_cons,List.length_nil]; omega)
    (by simp only [planScalar,traceScalar,eventScalar]; omega)
  simp only [nested]
  simp only [payload,nodes,List.length_cons,List.length_nil] at h
  nlinarith only [h]

def listThree (allocated slots frames : ℕ) (first second third : Trace) : ℕ := finishWork (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) []

theorem listThree_bound (allocated slots frames : ℕ) (first second third : Trace) :
    listThree allocated slots frames first second third ≤ 88*(first.length+second.length+third.length+11)*(binaryWordWidth (4*first.length+4*second.length+4*third.length+allocated+slots+frames+usage first+usage second+usage third+52)+1) := by
  have h0 := traceScalar_usage first
  have h1 := traceScalar_usage second
  have h2 := traceScalar_usage third
  have h := finish_bound (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots]) (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) [] (4*first.length+4*second.length+4*third.length+allocated+slots+frames+usage first+usage second+usage third+52)
    (by simp only [payload,nodes,List.length_cons,List.length_nil]; omega)
    (by simp only [planScalar,traceScalar,eventScalar]; omega)
  simp only [listThree]
  simp only [payload,nodes,List.length_cons,List.length_nil] at h
  nlinarith only [h]

end Blotto.BinaryWrapperScalarWork

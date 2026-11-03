import Blotto.BinaryObjectReadPlan

/-! Planned physical lookups feed the existing readback plan and emitter.
The preceding complete control/emission record is exact. Actual lookup source
work and its emission are forwarded separately, without a companion replay. -/
namespace Blotto.BinaryPrimitiveReadbackPlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTracePlanMeasured
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryNumericalReadbackPlan (finish)
open BinaryPhysicalNumericalReadbackLifetime (nativeLookupWork pairNativeLookupWork)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def readManyAt {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    List (List Bool) → ℕ → ((Option (List SignedWord) × Plan) × ℕ) × ℕ
  | [],depth => (((some [],.block [.frames (depth+1),.arrayAllocation 8]),1),0)
  | index::rest,depth =>
      let currentProduced := BinaryObjectReadPlan.getWithEmission store index
      let current := currentProduced.1
      let laterProduced := readManyAt store rest (depth+2)
      let later := laterProduced.1
      let result := match current.1.1,later.1.1 with
        | some word,some words => some (word::words)
        | _,_ => none
      (((result,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 16])
        (.join (.shifted (depth+2) current.1.2) later.1.2)),later.2+1),current.2+currentProduced.2+laterProduced.2)

theorem many_compat {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) (depth : ℕ) :
    (readManyAt store indices depth).1 = BinaryNumericalReadbackPlan.readManyAt store indices depth := by
  induction indices generalizing depth with
  | nil => rfl
  | cons index rest ih =>
      simp only [readManyAt,BinaryNumericalReadbackPlan.readManyAt,BinaryObjectReadPlan.get_compat,
        BinaryWordObjectArrayAccessMeasured.get_erases,ih]
      rfl

theorem many_price {n : ℕ} (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) (depth : ℕ) :
    (readManyAt store indices depth).2 ≤ nativeLookupWork store indices+
      25*payload (readManyAt store indices depth).1.1.2 := by
  induction indices generalizing depth with
  | nil => simp only [readManyAt,nativeLookupWork,payload,List.length_cons,List.length_nil]; omega
  | cons index rest ih =>
      have hl := ih (depth+2)
      have hc := BinaryObjectReadPlan.get_emission_bound store index
      simp only [BinaryObjectReadPlan.get_compat] at hc
      simp only [readManyAt,nativeLookupWork,payload,List.length_cons,List.length_nil,
        BinaryObjectReadPlan.get_compat,BinaryWordObjectArrayAccessMeasured.get_work]
      omega

def readAllAt {n : ℕ} (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    ((Option (List SignedWord) × Plan) × ℕ) × ℕ :=
  let indices := BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)
  let produced := readManyAt store indices.1 (depth+2)
  let result := produced.1
  (((result.1.1,.join (.block [.frames (depth+2),.arrayAllocation 32])
    (.join (.shifted (depth+2) indices.2) result.1.2)),result.2+1),produced.2)

theorem all_compat {n : ℕ} (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (readAllAt store depth).1 = BinaryNumericalReadbackPlan.readAllAt store depth := by
  simp only [readAllAt,BinaryNumericalReadbackPlan.readAllAt,many_compat]

theorem all_price {n : ℕ} (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (readAllAt store depth).2 ≤ nativeLookupWork store
      (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1+
      25*payload (readAllAt store depth).1.1.2 := by
  have h := many_price store (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1 (depth+2)
  simp only [readAllAt,payload,List.length_cons,List.length_nil]
  omega

def pairAt {n : ℕ} (request : Request n) (depth : ℕ) :
    ((Option (List SignedWord × List SignedWord) × Plan) × ℕ) × ℕ :=
  let lengthsProduced := readAllAt request.physical.lengthStore (depth+2)
  let poorProduced := readAllAt request.physical.poorStore (depth+2)
  let lengths := lengthsProduced.1
  let poor := poorProduced.1
  let result := do
    let lengthWords ← lengths.1.1
    let poorWords ← poor.1.1
    pure (lengthWords,poorWords)
  (((result,.join (.block [.frames (depth+2),.arrayAllocation 32]) (.join lengths.1.2 poor.1.2)),
    lengths.2+poor.2+1),lengthsProduced.2+poorProduced.2)

theorem pair_compat {n : ℕ} (request : Request n) (depth : ℕ) :
    (pairAt request depth).1 = BinaryNumericalReadbackPlan.pairAt request depth := by
  simp only [pairAt,BinaryNumericalReadbackPlan.pairAt,all_compat]

theorem pair_price {n : ℕ} (request : Request n) (depth : ℕ) :
    (pairAt request depth).2 ≤ pairNativeLookupWork request+25*payload (pairAt request depth).1.1.2 := by
  have hl := all_price request.physical.lengthStore (depth+2)
  have hp := all_price request.physical.poorStore (depth+2)
  simp only [pairAt,payload,List.length_cons,List.length_nil]
  dsimp only [pairNativeLookupWork] at *
  omega

def readPairWithEmission {n : ℕ} (request : Request n) :=
  let produced := pairAt request 0
  (finish produced.1,produced.2)

theorem readPair_compat {n : ℕ} (request : Request n) :
    (readPairWithEmission request).1 = BinaryNumericalReadbackPlan.readPairWithEmission request := by
  simp only [readPairWithEmission,pair_compat]
  rfl

theorem readPair_price {n : ℕ} (request : Request n) :
    (readPairWithEmission request).2 ≤ BinaryPhysicalNumericalReadbackLifetime.pairLookupAllowance request+
      25*(readPairWithEmission request).1.1.1.2.length := by
  have h := pair_price request 0
  have ha := BinaryPhysicalNumericalReadbackLifetime.pairNativeLookupWork_le_allowance request
  simp only [readPairWithEmission,BinaryNumericalReadbackPlan.finish_record,BinaryNumericalReadbackPlan.view,denote_length]
  omega

end Blotto.BinaryPrimitiveReadbackPlan

import Blotto.BinaryPhysicalCachePlan
import Blotto.BinaryObjectReadPlan
import Blotto.BinaryCachePrefixPlan
import Blotto.BinaryTerminalPhysicalRouteLifetime
import Blotto.BinaryWordStoreMeasured

/-! Physical-cache routing consumes the actual planned object getter once.
Its returned source work replaces the prior companion lookup replay. Parent
plans/work/emission remain exact; reached getter emissions are forwarded. -/
namespace Blotto.BinaryObjectCachePlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryCachePrefixPlan BinaryTerminalPhysicalRouteLifetime
set_option autoImplicit false
set_option maxHeartbeats 2500000

open BinaryPhysicalCachePlan (addressAt patchAt)

def readLengthAt {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) (depth : ℕ) :
    ((Option SignedWord × Plan) × ℕ) × ℕ :=
  let encoded := addressAt j (depth+2)
  let produced := BinaryObjectReadPlan.getWithEmission store encoded.1.1
  let fetched := produced.1
  (((fetched.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8])
    (.join encoded.1.2 (.shifted (depth+2) fetched.1.2))),
    encoded.2+fetched.2+4),produced.2)

theorem readLengthAt_compat {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) (depth : ℕ) :
    (readLengthAt store j depth).1 = BinaryPhysicalCachePlan.readLengthAt store j depth := by
  simp only [readLengthAt,BinaryPhysicalCachePlan.readLengthAt,BinaryObjectReadPlan.get_compat,
    BinaryWordObjectArrayAccessMeasured.get_erases,BinaryWordObjectArrayAccessMeasured.get_work]

theorem readLengthAt_price {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) (depth : ℕ) :
    (readLengthAt store j depth).2 ≤ 25*payload (readLengthAt store j depth).1.1.2 := by
  unfold readLengthAt
  dsimp only
  refine (BinaryObjectReadPlan.get_emission_bound _ _).trans ?_
  simp only [payload,List.length_cons,List.length_nil]
  omega

def membersAt {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord) (g : Fin m) :
    List (Fin n) → ℕ → ((List (Fin n × BinaryGroupRoutes.Route m) × Plan) × ℕ) × ℕ
  | [],depth => ((([],.block [.frames (depth+1),.arrayAllocation 8]),1),0)
  | j::rest,depth =>
      let produced := readLengthAt store j (depth+1)
      let fetched := produced.1
      let word := fetched.1.1.getD zero
      let divided := BinaryRationalOpcodeAllocation.applyWithAllocation .div word total
      let returned := membersAt store total g rest (depth+1)
      let later := returned.1
      ((((j,(some g,divided.1))::later.1.1,
        .join (.block [.frames (depth+1),.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div word total)])
          (.join fetched.1.2 later.1.2)),
        fetched.2+(applyWithWork .div word total).2+later.2+1),produced.2+returned.2)

theorem membersAt_compat {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (depth : ℕ) :
    (membersAt store total g items depth).1 = BinaryPhysicalCachePlan.membersAt store total g items depth := by
  induction items generalizing depth with
  | nil => rfl
  | cons item rest ih => simp only [membersAt,BinaryPhysicalCachePlan.membersAt,readLengthAt_compat,ih]

theorem membersAt_price {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (depth : ℕ) :
    (membersAt store total g items depth).2 ≤ 25*payload (membersAt store total g items depth).1.1.2 := by
  induction items generalizing depth with
  | nil => simp only [membersAt,payload,List.length_cons,List.length_nil]; omega
  | cons item rest ih =>
      have hc := readLengthAt_price store item (depth+1)
      have hl := ih (depth+1)
      simp only [membersAt,payload,List.length_cons,List.length_nil]
      omega

def groupsAt {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    List (Fin m) → ℕ → ((List (Fin n × BinaryGroupRoutes.Route m) × Plan) × ℕ) × ℕ
  | [],depth => ((([],.block [.frames (depth+1),.arrayAllocation 8]),1),0)
  | g::rest,depth =>
      let produced := membersAt store (groups.read g).2 g (groups.read g).1 (depth+2)
      let memberResult := produced.1
      let returned := groupsAt store groups rest (depth+2)
      let later := returned.1
      (((memberResult.1.1++later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8,
        .listAllocation memberResult.1.1.length]) (.join memberResult.1.2 later.1.2)),
        memberResult.2+later.2+memberResult.1.1.length+1),produced.2+returned.2)

theorem groupsAt_compat {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) (depth : ℕ) :
    (groupsAt store groups items depth).1 = BinaryPhysicalCachePlan.groupsAt store groups items depth := by
  induction items generalizing depth with
  | nil => rfl
  | cons item rest ih => simp only [groupsAt,BinaryPhysicalCachePlan.groupsAt,membersAt_compat,ih]

theorem groupsAt_price {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) (depth : ℕ) :
    (groupsAt store groups items depth).2 ≤ 25*payload (groupsAt store groups items depth).1.1.2 := by
  induction items generalizing depth with
  | nil => simp only [groupsAt,payload,List.length_cons,List.length_nil]; omega
  | cons item rest ih =>
      have hc := membersAt_price store (groups.read item).2 item (groups.read item).1 (depth+2)
      have hl := ih (depth+2)
      simp only [groupsAt,payload,List.length_cons,List.length_nil]
      omega

def routesAt {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    ((FixedArrayTable n (BinaryGroupRoutes.Route m) × Plan) × ℕ) × ℕ :=
  let produced := groupsAt store groups (List.finRange m) (depth+2)
  let assignments := produced.1
  let initial := initialRoutesWithTrace n m
  let patched := patchAt assignments.1.1 initial.1 (depth+2)
  (((patched.1.1,.join (.block [.frames (depth+(n+m+8)),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)])
    (.join (.shifted (depth+2) initial.2) (.join assignments.1.2 patched.1.2))),
    assignments.2+patched.2+n*(n+1)+m+1),produced.2)

theorem routesAt_compat {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    (routesAt store groups depth).1 = BinaryPhysicalCachePlan.routesAt store groups depth := by
  simp only [routesAt,BinaryPhysicalCachePlan.routesAt,groupsAt_compat]

theorem routesAt_price {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    (routesAt store groups depth).2 ≤ 25*payload (routesAt store groups depth).1.1.2 := by
  unfold routesAt
  dsimp only
  refine (groupsAt_price _ _ _ _).trans ?_
  simp only [payload,List.length_cons,List.length_nil]
  omega

def cacheAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    ((BinaryTerminalCacheLifetime.CacheData input × Plan) × ℕ) × ℕ :=
  let front := prefixAt input depth
  let entries := front.1.1.2
  let count := entries.length
  let packing := BinaryTerminalCacheLifetime.packingOfEntries entries
  let totals := totalsWithTrace packing
  let produced := routesAt store packing (depth+2)
  let routes := produced.1
  let pivot := front.1.1.1.pivot
  let extra := BinaryTerminalCacheLifetime.pivotWithTraceAndWork input pivot
  (((⟨count,packing,totals.1,routes.1.1,pivot,extra.1.1.1,extra.1.1.2⟩,
    .join front.1.2 (.join (.block [.frames (depth+(count+n+8)),.arrayAllocation (2*(count+1)^2+16)])
      (.join (.shifted (depth+2) totals.2) (.join routes.1.2 (.shifted (depth+2) extra.1.2))))),
    front.2+routes.2+extra.2+count+n+5+(count*(count+1)+2*count+5)),produced.2)

theorem cacheAt_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (cacheAt input store depth).1 = BinaryPhysicalCachePlan.cacheAt input store depth := by
  simp only [cacheAt,BinaryPhysicalCachePlan.cacheAt,routesAt_compat]

theorem cacheAt_price {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (cacheAt input store depth).2 ≤ 25*payload (cacheAt input store depth).1.1.2 := by
  unfold cacheAt
  dsimp only
  refine (routesAt_price _ _ _).trans ?_
  simp only [payload,List.length_cons,List.length_nil]
  omega

def cacheWithEmission {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (((BinaryTerminalCacheLifetime.CacheData input × Trace) × ℕ) × ℕ) × ℕ :=
  let produced := cacheAt input store 0
  let planned := produced.1
  let emitted := emitFull planned.1.2 []
  ((((planned.1.1,emitted.1.1),planned.2),emitted.1.2+emitted.2),produced.2)

theorem cache_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithEmission input store).1 = BinaryPhysicalCachePlan.cacheWithEmission input store := by
  simp only [cacheWithEmission,BinaryPhysicalCachePlan.cacheWithEmission,cacheAt_compat]

theorem cache_price {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithEmission input store).2 ≤ 25*(cacheWithEmission input store).1.1.1.2.length := by
  have h := cacheAt_price input store 0
  simpa only [cacheWithEmission,emitFull_erases,emit_length,List.length_nil,Nat.add_zero] using h

end Blotto.BinaryObjectCachePlan

import Blotto.BinaryObjectCachePlan
import Blotto.BinaryCacheArithmeticPrefix

/-! Actual measured arithmetic joins cache classification/packing and physical
member routing. Getter emissions and a reached arithmetic-work counter are
returned with the exact prior cache plan/source/parent-emission record. Other
cache primitives and native observer/ownership costs retain their old scope. -/
namespace Blotto.BinaryCacheArithmeticPlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryTerminalPhysicalRouteLifetime
open BinaryPhysicalCachePlan (patchAt)
open BinaryObjectCachePlan (readLengthAt)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def keep {α : Type*} (returned : α × (ℕ × ℕ)) : α × ℕ := (returned.1,returned.2.1)

def membersAt {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord) (g : Fin m) :
    List (Fin n) → ℕ → ((List (Fin n × BinaryGroupRoutes.Route m) × Plan) × ℕ) × (ℕ × ℕ)
  | [],depth => ((([],.block [.frames (depth+1),.arrayAllocation 8]),1),(0,0))
  | j::rest,depth =>
      let produced := readLengthAt store j (depth+1)
      let fetched := produced.1
      let word := fetched.1.1.getD BinaryRationalOpcode.zero
      let divided := BinaryCubicOpcodeMeasured.apply .div word total
      let returned := membersAt store total g rest (depth+1)
      let later := returned.1
      ((((j,(some g,divided.data))::later.1.1,
        .join (.block [.frames (depth+1),.arrayAllocation 8,.listAllocation 1,
          .listAllocation divided.storage]) (.join fetched.1.2 later.1.2)),
        fetched.2+divided.source+later.2+1),(produced.2+returned.2.1,divided.work+returned.2.2))

theorem members_compat {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (depth : ℕ) :
    keep (membersAt store total g items depth) = BinaryObjectCachePlan.membersAt store total g items depth := by
  induction items generalizing depth with
  | nil => rfl
  | cons item rest ih =>
      simp only [membersAt,BinaryObjectCachePlan.membersAt,← ih,keep,
        ← BinaryCubicOpcodeMeasured.apply_erases,BinaryCubicOpcodeMeasured.apply_storage,
        BinaryCubicOpcodeMeasured.apply_source]

theorem members_work {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (depth : ℕ) :
    (membersAt store total g items depth).2.2 ≤ 4*(membersAt store total g items depth).1.2 := by
  induction items generalizing depth with
  | nil => change 0 ≤ 4*1; omega
  | cons item rest ih =>
      have hd := BinaryCubicOpcodeMeasured.apply_work_bound .div
        ((readLengthAt store item (depth+1)).1.1.1.getD BinaryRationalOpcode.zero) total
      have hl := ih (depth+1)
      simp only [membersAt]
      omega

def groupsAt {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    List (Fin m) → ℕ → ((List (Fin n × BinaryGroupRoutes.Route m) × Plan) × ℕ) × (ℕ × ℕ)
  | [],depth => ((([],.block [.frames (depth+1),.arrayAllocation 8]),1),(0,0))
  | g::rest,depth =>
      let produced := membersAt store (groups.read g).2 g (groups.read g).1 (depth+2)
      let memberResult := produced.1
      let returned := groupsAt store groups rest (depth+2)
      let later := returned.1
      (((memberResult.1.1++later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8,
        .listAllocation memberResult.1.1.length]) (.join memberResult.1.2 later.1.2)),
        memberResult.2+later.2+memberResult.1.1.length+1),
        (produced.2.1+returned.2.1,produced.2.2+returned.2.2))

theorem groups_compat {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) (depth : ℕ) :
    keep (groupsAt store groups items depth) = BinaryObjectCachePlan.groupsAt store groups items depth := by
  induction items generalizing depth with
  | nil => rfl
  | cons item rest ih =>
      simp only [groupsAt,BinaryObjectCachePlan.groupsAt,← members_compat,← ih,keep]

theorem groups_work {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) (depth : ℕ) :
    (groupsAt store groups items depth).2.2 ≤ 4*(groupsAt store groups items depth).1.2 := by
  induction items generalizing depth with
  | nil => change 0 ≤ 4*1; omega
  | cons item rest ih =>
      have hc := members_work store (groups.read item).2 item (groups.read item).1 (depth+2)
      have hl := ih (depth+2)
      simp only [groupsAt]
      omega

def routesAt {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    ((FixedArrayTable n (BinaryGroupRoutes.Route m) × Plan) × ℕ) × (ℕ × ℕ) :=
  let produced := groupsAt store groups (List.finRange m) (depth+2)
  let assignments := produced.1
  let initial := initialRoutesWithTrace n m
  let patched := patchAt assignments.1.1 initial.1 (depth+2)
  (((patched.1.1,.join (.block [.frames (depth+(n+m+8)),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)])
    (.join (.shifted (depth+2) initial.2) (.join assignments.1.2 patched.1.2))),
    assignments.2+patched.2+n*(n+1)+m+1),produced.2)

theorem routes_compat {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    keep (routesAt store groups depth) = BinaryObjectCachePlan.routesAt store groups depth := by
  simp only [routesAt,BinaryObjectCachePlan.routesAt,← groups_compat,keep]

theorem routes_work {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    (routesAt store groups depth).2.2 ≤ 4*(routesAt store groups depth).1.2 := by
  have h := groups_work store groups (List.finRange m) (depth+2)
  simp only [routesAt]
  omega

def cacheAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    ((BinaryTerminalCacheLifetime.CacheData input × Plan) × ℕ) × (ℕ × ℕ) :=
  let prefixProduced := BinaryCacheArithmeticPrefix.prefixAt input depth
  let front := prefixProduced.1
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
    front.2+routes.2+extra.2+count+n+5+(count*(count+1)+2*count+5)),
    (produced.2.1,prefixProduced.2+produced.2.2))

theorem cacheAt_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    keep (cacheAt input store depth) = BinaryObjectCachePlan.cacheAt input store depth := by
  let assemble (front : ((BinaryTerminalPrefixLifetime.Classification n ×
      List (List (Fin n) × SignedWord)) × Plan) × ℕ) :
      ((BinaryTerminalCacheLifetime.CacheData input × Plan) × ℕ) × ℕ :=
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
      front.2+routes.2+extra.2+count+n+5+(count*(count+1)+2*count+5)),produced.2.1)
  change assemble (BinaryCacheArithmeticPrefix.prefixAt input depth).1 = _
  simp only [BinaryObjectCachePlan.cacheAt,← routes_compat,keep]
  change assemble (BinaryCacheArithmeticPrefix.prefixAt input depth).1 =
    assemble (BinaryCachePrefixPlan.prefixAt input depth)
  exact congrArg assemble (BinaryCacheArithmeticPrefix.prefix_compat input depth)

theorem cacheAt_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (cacheAt input store depth).2.2 ≤ 4*(cacheAt input store depth).1.2 := by
  have hp := BinaryCacheArithmeticPrefix.prefix_work input depth
  have hr := routes_work store (BinaryTerminalCacheLifetime.packingOfEntries
    (BinaryCacheArithmeticPrefix.prefixAt input depth).1.1.1.2) (depth+2)
  simp only [cacheAt]
  omega

def cacheWithEmission {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (((BinaryTerminalCacheLifetime.CacheData input × Trace) × ℕ) × ℕ) × (ℕ × ℕ) :=
  let produced := cacheAt input store 0
  let planned := produced.1
  let emitted := emitFull planned.1.2 []
  ((((planned.1.1,emitted.1.1),planned.2),emitted.1.2+emitted.2),produced.2)

theorem cache_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    keep (cacheWithEmission input store) = BinaryObjectCachePlan.cacheWithEmission input store := by
  simp only [cacheWithEmission,BinaryObjectCachePlan.cacheWithEmission,← cacheAt_compat,keep]

theorem cache_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithEmission input store).2.2 ≤ 4*(cacheWithEmission input store).1.1.2 :=
  cacheAt_work input store 0

end Blotto.BinaryCacheArithmeticPlan

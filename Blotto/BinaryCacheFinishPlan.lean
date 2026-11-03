import Blotto.BinaryCacheArithmeticPlan
import Blotto.BinaryCacheTableMeasured

/-! Reached pivot division, index enumeration, packing/totals/initial-route
tables and explicit route-copy patches join the actual cache. Forgetting the
new finishing price preserves every preceding plan/source/emission/arithmetic
field. Native metadata/width/reference/ownership costs and physical space remain. -/
namespace Blotto.BinaryCacheFinishPlan
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured
set_option autoImplicit false
set_option maxHeartbeats 4000000

def pivot {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    Option (Fin n) → (((SignedWord × SignedWord) × Trace) × ℕ) × ℕ
  | none => ((((BinaryRationalOpcode.zero,BinaryRationalOpcode.zero),[.frames 1,.arrayAllocation 8]),0),0)
  | some j =>
      let produced := BinaryCubicOpcodeMeasured.apply .div (input.resource.read j) (input.length.read j)
      ((((input.length.read j,produced.data),[.frames 1,.arrayAllocation 8,.listAllocation produced.storage]),
        produced.source),produced.work)

theorem pivot_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (j : Option (Fin n)) :
    (pivot input j).1 = BinaryTerminalCacheLifetime.pivotWithTraceAndWork input j := by
  cases j <;> simp only [pivot,BinaryTerminalCacheLifetime.pivotWithTraceAndWork,
    ← BinaryCubicOpcodeMeasured.apply_erases,BinaryCubicOpcodeMeasured.apply_storage,BinaryCubicOpcodeMeasured.apply_source]

theorem pivot_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (j : Option (Fin n)) :
    (pivot input j).2 ≤ 4*(pivot input j).1.2 := by
  cases j with
  | none => rfl
  | some j => exact BinaryCubicOpcodeMeasured.apply_work_bound .div _ _

def prefixAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :=
  let indices := BinaryCacheTableMeasured.indices n
  let c := BinaryCacheArithmeticPrefix.classificationAt input indices.1 (depth+2)
  let classified := c.1
  let p := BinaryCacheArithmeticPrefix.packingAt input.length.read input.budget classified.1.1.uniforms (depth+2)
  let packed := p.1
  (((((classified.1.1,packed.1.1),Plan.join (.block [.frames (depth+(n+8)),.listAllocation n,.arrayAllocation 8])
    (.join classified.1.2 packed.1.2)),classified.2+packed.2),c.2+p.2),indices.2)

theorem prefix_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    (prefixAt input depth).1 = BinaryCacheArithmeticPrefix.prefixAt input depth := by
  simp only [prefixAt,BinaryCacheArithmeticPrefix.prefixAt,BinaryCacheTableMeasured.indices_data]

theorem prefix_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    (prefixAt input depth).2 ≤ 32*(n+1)^2 := BinaryCacheTableMeasured.indices_work n

def patchAt {n m : ℕ} : List (Fin n × BinaryGroupRoutes.Route m) →
    FixedArrayTable n (BinaryGroupRoutes.Route m) → ℕ →
      ((FixedArrayTable n (BinaryGroupRoutes.Route m) × Plan) × ℕ) × ℕ
  | [],table,depth => (((table,.block [.frames (depth+1),.arrayAllocation 8]),1),4)
  | entry::rest,table,depth =>
      let copied := BinaryCacheTableMeasured.write table entry.1 entry.2
      let returned := patchAt rest copied.1 (depth+1)
      let later := returned.1
      (((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation
        (table.payloadWordSum BinaryTerminalRouteLifetime.routeWords+
          copied.1.payloadWordSum BinaryTerminalRouteLifetime.routeWords+8)]) later.1.2),n+1+later.2),
        copied.2+returned.2+4)

theorem patch_compat {n m : ℕ} (entries : List (Fin n × BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) (depth : ℕ) :
    (patchAt entries table depth).1 = BinaryPhysicalCachePlan.patchAt entries table depth := by
  induction entries generalizing table depth with
  | nil => rfl
  | cons entry rest ih =>
      simp only [patchAt,BinaryPhysicalCachePlan.patchAt,BinaryCacheTableMeasured.write_data,ih]

theorem patch_source_length {n m : ℕ} (entries : List (Fin n × BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) (depth : ℕ) :
    entries.length ≤ (patchAt entries table depth).1.2 := by
  induction entries generalizing table depth with
  | nil => change 0 ≤ 1; omega
  | cons entry rest ih =>
      have h := ih (BinaryCacheTableMeasured.write table entry.1 entry.2).1 (depth+1)
      simp only [patchAt,List.length_cons]
      omega

theorem patch_work {n m : ℕ} (entries : List (Fin n × BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) (depth : ℕ) :
    (patchAt entries table depth).2 ≤ 80*(entries.length+1)*(n+1)^2 := by
  have hOne : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  induction entries generalizing table depth with
  | nil => simp only [patchAt,List.length_nil]; omega
  | cons entry rest ih =>
      have hc := BinaryCacheTableMeasured.write_work table entry.1 entry.2
      have hl := ih (BinaryCacheTableMeasured.write table entry.1 entry.2).1 (depth+1)
      simp only [patchAt,List.length_cons]
      rw [show 80*(rest.length+1+1)*(n+1)^2 = 80*(rest.length+1)*(n+1)^2+80*(n+1)^2 by ring]
      omega

def routesAt {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :=
  let indices := BinaryCacheTableMeasured.indices m
  let produced := BinaryCacheArithmeticPlan.groupsAt store groups indices.1 (depth+2)
  let assignments := produced.1
  let initial := BinaryCacheTableMeasured.initial n m
  let patched := patchAt assignments.1.1 initial.1.1 (depth+2)
  let routed := patched.1
  ((((routed.1.1,Plan.join (.block [.frames (depth+(n+m+8)),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)])
    (.join (.shifted (depth+2) initial.1.2) (.join assignments.1.2 routed.1.2))),
    assignments.2+routed.2+n*(n+1)+m+1),produced.2),indices.2+initial.2+patched.2+4)

theorem routes_compat {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    (routesAt store groups depth).1 = BinaryCacheArithmeticPlan.routesAt store groups depth := by
  simp only [routesAt,BinaryCacheArithmeticPlan.routesAt,BinaryCacheTableMeasured.indices_data,
    BinaryCacheTableMeasured.initial_compat,patch_compat]

theorem routes_work {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    (routesAt store groups depth).2 ≤ 200*((routesAt store groups depth).1.1.2+1)^3 := by
  let indices := BinaryCacheTableMeasured.indices m
  let assignments := BinaryCacheArithmeticPlan.groupsAt store groups indices.1 (depth+2)
  let initial := BinaryCacheTableMeasured.initial n m
  let patched := patchAt assignments.1.1.1 initial.1.1 (depth+2)
  let S := assignments.1.2+patched.1.2+n*(n+1)+m+1
  have hLength := patch_source_length assignments.1.1.1 initial.1.1 (depth+2)
  have hPatch := patch_work assignments.1.1.1 initial.1.1 (depth+2)
  have hN : n ≤ S := by dsimp only [S]; nlinarith
  have hM : m ≤ S := by dsimp only [S]; omega
  have hA : assignments.1.1.1.length ≤ S := by dsimp only [S,patched] at *; omega
  have hP := Nat.mul_le_mul (Nat.mul_le_mul_left 80 (Nat.add_le_add_right hA 1))
    (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 2)
  have hi := BinaryCacheTableMeasured.indices_work m
  have ht := BinaryCacheTableMeasured.initial_work n m
  have hi' := Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) 2
  have ht' := Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 2
  have hSq : (S+1)^2 ≤ (S+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hOne : 1 ≤ (S+1)^3 := Nat.one_le_pow _ _ (by omega)
  change indices.2+initial.2+patched.2+4 ≤ 200*(S+1)^3
  change patched.2 ≤ _ at hPatch
  rw [show 80*(S+1)*(S+1)^2 = 80*(S+1)^3 by ring] at hP
  nlinarith only [hPatch,hP,hi,ht,hi',ht',hSq,hOne]

def cacheAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :=
  let prefixProduced := prefixAt input depth
  let front := prefixProduced.1.1
  let entries := front.1.1.2
  let count := entries.length
  let packingProduced := BinaryCacheTableMeasured.packTable entries
  let packing := packingProduced.1
  let totalsProduced := BinaryCacheTableMeasured.totals packing
  let totals := totalsProduced.1
  let produced := routesAt store packing (depth+2)
  let routes := produced.1.1
  let selected := front.1.1.1.pivot
  let pivotProduced := pivot input selected
  let extra := pivotProduced.1
  let data : BinaryTerminalCacheLifetime.CacheData input :=
    ⟨count,packing,totals.1,routes.1.1,selected,extra.1.1.1,extra.1.1.2⟩
  let plan := Plan.join front.1.2 (.join (.block [.frames (depth+(count+n+8)),.arrayAllocation (2*(count+1)^2+16)])
    (.join (.shifted (depth+2) totals.2) (.join routes.1.2 (.shifted (depth+2) extra.1.2))))
  let source := front.2+routes.2+extra.2+count+n+5+(count*(count+1)+2*count+5)
  ((((data,plan),source),(produced.1.2.1,prefixProduced.1.2+produced.1.2.2)),
    prefixProduced.2+packingProduced.2+totalsProduced.2+produced.2+pivotProduced.2+4)

theorem cacheAt_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (cacheAt input store depth).1 = BinaryCacheArithmeticPlan.cacheAt input store depth := by
  let assemble (supplied : (((BinaryTerminalPrefixLifetime.Classification n ×
      List (List (Fin n) × SignedWord)) × Plan) × ℕ) × ℕ) :
      ((BinaryTerminalCacheLifetime.CacheData input × Plan) × ℕ) × (ℕ × ℕ) :=
    let front := supplied.1
    let entries := front.1.1.2
    let count := entries.length
    let packing := BinaryTerminalCacheLifetime.packingOfEntries entries
    let totals := BinaryTerminalPhysicalRouteLifetime.totalsWithTrace packing
    let produced := BinaryCacheArithmeticPlan.routesAt store packing (depth+2)
    let routes := produced.1
    let selected := front.1.1.1.pivot
    let extra := BinaryTerminalCacheLifetime.pivotWithTraceAndWork input selected
    let data : BinaryTerminalCacheLifetime.CacheData input :=
      ⟨count,packing,totals.1,routes.1.1,selected,extra.1.1.1,extra.1.1.2⟩
    let plan := Plan.join front.1.2 (.join (.block [.frames (depth+(count+n+8)),.arrayAllocation (2*(count+1)^2+16)])
      (.join (.shifted (depth+2) totals.2) (.join routes.1.2 (.shifted (depth+2) extra.1.2))))
    let source := front.2+routes.2+extra.2+count+n+5+(count*(count+1)+2*count+5)
    (((data,plan),source),(produced.2.1,supplied.2+produced.2.2))
  simp only [cacheAt,BinaryCacheTableMeasured.packTable_data,
    BinaryCacheTableMeasured.totals_compat,routes_compat,pivot_compat]
  change assemble (prefixAt input depth).1 = assemble (BinaryCacheArithmeticPrefix.prefixAt input depth)
  exact congrArg assemble (prefix_compat input depth)

theorem cacheAt_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (cacheAt input store depth).2 ≤ 1000*((cacheAt input store depth).1.1.2+1)^3 := by
  let pre := prefixAt input depth
  let front := pre.1.1
  let entries := front.1.1.2
  let packed := BinaryCacheTableMeasured.packTable entries
  let total := BinaryCacheTableMeasured.totals packed.1
  let routed := routesAt store packed.1 (depth+2)
  let selected := pivot input front.1.1.1.pivot
  let S := front.2+routed.1.1.2+selected.1.2+entries.length+n+5+
    (entries.length*(entries.length+1)+2*entries.length+5)
  have hn : n ≤ S := by dsimp only [S]; omega
  have hc : entries.length ≤ S := by dsimp only [S]; omega
  have hr : routed.1.1.2 ≤ S := by dsimp only [S]; omega
  have hp : selected.1.2 ≤ S := by dsimp only [S]; omega
  have hPre := prefix_work input depth
  have hPack := BinaryCacheTableMeasured.packTable_work entries
  have hTotal := BinaryCacheTableMeasured.totals_work packed.1
  have hRoute := routes_work store packed.1 (depth+2)
  have hPivot := pivot_work input front.1.1.1.pivot
  have hN := Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2
  have hC := Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2
  have hR := Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 3
  have hSq : (S+1)^2 ≤ (S+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hLin : S ≤ (S+1)^3 := by
    have h : S+1 ≤ (S+1)^3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < S+1) (by omega : 1 ≤ 3)
    exact (Nat.le_succ S).trans h
  have hOne : 1 ≤ (S+1)^3 := Nat.one_le_pow _ _ (by omega)
  change pre.2+packed.2+total.2+routed.2+selected.2+4 ≤ 1000*(S+1)^3
  nlinarith only [hPre,hPack,hTotal,hRoute,hPivot,hN,hC,hR,hSq,hLin,hOne,hp]

def cacheWithEmission {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :=
  let produced := cacheAt input store 0
  let planned := produced.1.1
  let emitted := emitFull planned.1.2 []
  (((((planned.1.1,emitted.1.1),planned.2),emitted.1.2+emitted.2),produced.1.2),produced.2)

theorem cache_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithEmission input store).1 = BinaryCacheArithmeticPlan.cacheWithEmission input store := by
  simp only [cacheWithEmission,BinaryCacheArithmeticPlan.cacheWithEmission,cacheAt_compat]

theorem cache_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithEmission input store).2 ≤ 1000*((cacheWithEmission input store).1.1.1.2+1)^3 :=
  cacheAt_work input store 0

end Blotto.BinaryCacheFinishPlan

import Blotto.BinaryCachePrefixPlan
import Blotto.BinaryTerminalPhysicalRouteLifetime
import Blotto.BinaryWordStoreMeasured

/-! The physical terminal cache executes classification, packing, Boolean
address production, physical reads, member/group routing and native patches
once while collecting a final-depth plan. Complete cache data, old trace and
source work are exact. Only the complete cache emits. Primitive arithmetic,
physical-read/array bodies and native scalar/layout/allocator prices retain
their preceding source-model scopes. -/
namespace Blotto.BinaryPhysicalCachePlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryCachePrefixPlan BinaryTerminalPhysicalRouteLifetime
set_option autoImplicit false
set_option maxHeartbeats 2500000

def replicateAt : ℕ → Bool → ℕ → List Bool × Plan
  | 0,_,depth => ([],.block [.frames (depth+1)])
  | k+1,bit,depth =>
      let later := replicateAt k bit (depth+1)
      (bit::later.1,.join (.block [.frames (depth+1),.listAllocation 1]) later.2)

theorem replicate_refines (k : ℕ) (bit : Bool) (depth : ℕ) :
    ((replicateAt k bit depth).1,denote (replicateAt k bit depth).2) =
      ((BinaryPRGOutputLifetime.replicateWithTrace k bit).1,
        under depth (BinaryPRGOutputLifetime.replicateWithTrace k bit).2) := by
  induction k generalizing depth with
  | zero => rfl
  | succ k ih =>
      have hd := congrArg Prod.fst (ih (depth+1))
      have ht := congrArg Prod.snd (ih (depth+1))
      dsimp only at hd ht
      simp only [replicateAt,BinaryPRGOutputLifetime.replicateWithTrace,denote,hd,ht,under_append,under_compose]
      rfl

theorem replicate_bound (k : ℕ) (bit : Bool) (depth : ℕ) : Bounded (replicateAt k bit depth).2 := by
  induction k generalizing depth with
  | zero => exact block_bound _
  | succ k ih =>
      have h := ih (depth+1)
      simp only [Bounded,replicateAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

def countAddressAt {α : Type*} : List α → List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],counter,depth => ((counter,.block [.frames (depth+1),.arrayAllocation 4]),1)
  | _::rest,counter,depth =>
      let advanced := BinaryWordStoreMeasured.carryAt counter (depth+2)
      let later := countAddressAt rest advanced.1.1 (depth+1)
      ((later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 4])
        (.join (.block advanced.1.2) later.1.2)),
        4*BinaryCarryCounter.carryCells counter+4*(counter.length+1)+later.2+4)

theorem countAddress_refines {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    observe (countAddressAt items counter depth) = offset depth (countAddressWithTraceAndWork items counter) := by
  induction items generalizing counter depth with
  | nil => rfl
  | cons item rest ih =>
      have h := ih (BinaryWordStoreLifetime.carryWithTrace counter).1 (depth+1)
      simp only [observe,offset,countAddressAt,countAddressWithTraceAndWork,denote,
        BinaryWordStoreMeasured.carryAt_erases,data_of_refinement h,trace_of_refinement h,
        work_of_refinement h,under_append,under_compose]
      rfl

theorem countAddress_bound {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    Bounded (countAddressAt items counter depth).1.2 := by
  induction items generalizing counter depth with
  | nil => exact block_bound _
  | cons item rest ih =>
      have h := ih (BinaryWordStoreMeasured.carryAt counter (depth+2)).1.1 (depth+1)
      simp only [Bounded,countAddressAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

def addressAt {n : ℕ} (j : Fin n) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let ruler := replicateAt j.val false (depth+2)
  let counted := countAddressAt ruler.1 [] (depth+2)
  ((counted.1.1,.join (.block [.frames (depth+1),.arrayAllocation 8]) (.join ruler.2 counted.1.2)),
    (j.val+1)*(binaryWordWidth n+4)+counted.2)

theorem address_refines {n : ℕ} (j : Fin n) (depth : ℕ) :
    observe (addressAt j depth) = offset depth (addressWithTraceAndWork j) := by
  have hr := replicate_refines j.val false (depth+2)
  have hd := congrArg Prod.fst hr
  have ht := congrArg Prod.snd hr
  dsimp only at hd ht
  have hc := countAddress_refines (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1 [] (depth+2)
  simp only [observe,offset,addressAt,addressWithTraceAndWork,denote,data_of_refinement hc,
    trace_of_refinement hc,work_of_refinement hc,hd,ht,wrap,combine,
    under_append,under_compose,List.append_nil]
  rfl

theorem address_bound {n : ℕ} (j : Fin n) (depth : ℕ) : Bounded (addressAt j depth).1.2 := by
  have hr := replicate_bound j.val false (depth+2)
  have hc := countAddress_bound (replicateAt j.val false (depth+2)).1 [] (depth+2)
  simp only [Bounded,addressAt,nodes,payload,List.length_cons,List.length_nil] at hr hc ⊢
  omega

def readLengthAt {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) (depth : ℕ) :
    (Option SignedWord × Plan) × ℕ :=
  let encoded := addressAt j (depth+2)
  let fetched := BinaryWordObjectArrayAccess.getWithTrace store encoded.1.1
  ((fetched.1,.join (.block [.frames (depth+1),.arrayAllocation 8])
    (.join encoded.1.2 (.shifted (depth+2) fetched.2))),
    encoded.2+(BinaryWordObjectArray.getWithWork store encoded.1.1).2+4)

theorem readLength_refines {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) (depth : ℕ) :
    observe (readLengthAt store j depth) = offset depth (readLengthWithTraceAndWork store j) := by
  have h := address_refines j (depth+2)
  simp only [observe,offset,readLengthAt,readLengthWithTraceAndWork,denote,data_of_refinement h,
    trace_of_refinement h,work_of_refinement h,wrap,combine,
    under_append,under_compose,List.append_nil]
  rfl

theorem readLength_bound {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) (depth : ℕ) :
    Bounded (readLengthAt store j depth).1.2 := by
  have h := address_bound j (depth+2)
  simp only [Bounded,readLengthAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def membersAt {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord) (g : Fin m) :
    List (Fin n) → ℕ → (List (Fin n × BinaryGroupRoutes.Route m) × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),1)
  | j::rest,depth =>
      let fetched := readLengthAt store j (depth+1)
      let word := fetched.1.1.getD zero
      let divided := BinaryRationalOpcodeAllocation.applyWithAllocation .div word total
      let later := membersAt store total g rest (depth+1)
      (((j,(some g,divided.1))::later.1.1,
        .join (.block [.frames (depth+1),.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div word total)])
          (.join fetched.1.2 later.1.2)),
        fetched.2+(applyWithWork .div word total).2+later.2+1)

theorem members_refines {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (depth : ℕ) :
    observe (membersAt store total g items depth) = offset depth (membersWithTraceAndWork store total g items) := by
  induction items generalizing depth with
  | nil => rfl
  | cons j rest ih =>
      have hf := readLength_refines store j (depth+1)
      have hl := ih (depth+1)
      simp only [observe,offset,membersAt,membersWithTraceAndWork,denote,
        data_of_refinement hf,trace_of_refinement hf,work_of_refinement hf,
        data_of_refinement hl,trace_of_refinement hl,work_of_refinement hl,under_append,under_compose]
      rfl

theorem members_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (depth : ℕ) : Bounded (membersAt store total g items depth).1.2 := by
  induction items generalizing depth with
  | nil => exact block_bound _
  | cons j rest ih =>
      have hf := readLength_bound store j (depth+1)
      have hl := ih (depth+1)
      simp only [Bounded,membersAt,nodes,payload,List.length_cons,List.length_nil] at hf hl ⊢
      omega

def groupsAt {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    List (Fin m) → ℕ → (List (Fin n × BinaryGroupRoutes.Route m) × Plan) × ℕ
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),1)
  | g::rest,depth =>
      let memberResult := membersAt store (groups.read g).2 g (groups.read g).1 (depth+2)
      let later := groupsAt store groups rest (depth+2)
      ((memberResult.1.1++later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8,
        .listAllocation memberResult.1.1.length]) (.join memberResult.1.2 later.1.2)),
        memberResult.2+later.2+memberResult.1.1.length+1)

theorem groups_refines {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) (depth : ℕ) :
    observe (groupsAt store groups items depth) = offset depth (groupsWithTraceAndWork store groups items) := by
  induction items generalizing depth with
  | nil => rfl
  | cons g rest ih =>
      have hm := members_refines store (groups.read g).2 g (groups.read g).1 (depth+2)
      have hl := ih (depth+2)
      simp only [observe,offset,groupsAt,groupsWithTraceAndWork,denote,
        data_of_refinement hm,trace_of_refinement hm,work_of_refinement hm,
        data_of_refinement hl,trace_of_refinement hl,work_of_refinement hl,under_append,under_compose]
      rfl

theorem groups_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) (depth : ℕ) :
    Bounded (groupsAt store groups items depth).1.2 := by
  induction items generalizing depth with
  | nil => exact block_bound _
  | cons g rest ih =>
      have hm := members_bound store (groups.read g).2 g (groups.read g).1 (depth+2)
      have hl := ih (depth+2)
      simp only [Bounded,groupsAt,nodes,payload,List.length_cons,List.length_nil] at hm hl ⊢
      omega

def patchAt {n m : ℕ} : List (Fin n × BinaryGroupRoutes.Route m) →
    FixedArrayTable n (BinaryGroupRoutes.Route m) → ℕ → (FixedArrayTable n (BinaryGroupRoutes.Route m) × Plan) × ℕ
  | [],table,depth => ((table,.block [.frames (depth+1),.arrayAllocation 8]),1)
  | entry::rest,table,depth =>
      let next := table.write entry.1 entry.2
      let later := patchAt rest next (depth+1)
      ((later.1.1,.join (.block [.frames (depth+1),.arrayAllocation
        (table.payloadWordSum BinaryTerminalRouteLifetime.routeWords+
          next.payloadWordSum BinaryTerminalRouteLifetime.routeWords+8)]) later.1.2),n+1+later.2)

theorem patch_refines {n m : ℕ} (entries : List (Fin n × BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) (depth : ℕ) :
    observe (patchAt entries table depth) = offset depth (BinaryTerminalRouteLifetime.patchWithTraceAndWork entries table) := by
  induction entries generalizing table depth with
  | nil => rfl
  | cons entry rest ih =>
      have h := ih (table.write entry.1 entry.2) (depth+1)
      simp only [observe,offset,patchAt,BinaryTerminalRouteLifetime.patchWithTraceAndWork,denote,
        data_of_refinement h,trace_of_refinement h,work_of_refinement h,under_append,under_compose]
      rfl

theorem patch_bound {n m : ℕ} (entries : List (Fin n × BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) (depth : ℕ) : Bounded (patchAt entries table depth).1.2 := by
  induction entries generalizing table depth with
  | nil => exact block_bound _
  | cons entry rest ih =>
      have h := ih (table.write entry.1 entry.2) (depth+1)
      simp only [Bounded,patchAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

def routesAt {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    (FixedArrayTable n (BinaryGroupRoutes.Route m) × Plan) × ℕ :=
  let assignments := groupsAt store groups (List.finRange m) (depth+2)
  let initial := initialRoutesWithTrace n m
  let patched := patchAt assignments.1.1 initial.1 (depth+2)
  ((patched.1.1,.join (.block [.frames (depth+(n+m+8)),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)])
    (.join (.shifted (depth+2) initial.2) (.join assignments.1.2 patched.1.2))),
    assignments.2+patched.2+n*(n+1)+m+1)

theorem routes_refines {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    observe (routesAt store groups depth) = offset depth (routesWithTraceAndWork store groups) := by
  have ha := groups_refines store groups (List.finRange m) (depth+2)
  have hp := patch_refines (groupsWithTraceAndWork store groups (List.finRange m)).1.1
    (initialRoutesWithTrace n m).1 (depth+2)
  simp only [observe,offset,routesAt,routesWithTraceAndWork,denote,
    data_of_refinement ha,trace_of_refinement ha,work_of_refinement ha,
    data_of_refinement hp,trace_of_refinement hp,work_of_refinement hp,
    under_append,under_compose,List.append_assoc]
  rfl

theorem routes_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) : Bounded (routesAt store groups depth).1.2 := by
  have ha := groups_bound store groups (List.finRange m) (depth+2)
  have hp := patch_bound (groupsAt store groups (List.finRange m) (depth+2)).1.1
    (initialRoutesWithTrace n m).1 (depth+2)
  simp only [Bounded,routesAt,nodes,payload,List.length_cons,List.length_nil] at ha hp ⊢
  omega

def cacheAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    (BinaryTerminalCacheLifetime.CacheData input × Plan) × ℕ :=
  let front := prefixAt input depth
  let entries := front.1.1.2
  let count := entries.length
  let packing := BinaryTerminalCacheLifetime.packingOfEntries entries
  let totals := totalsWithTrace packing
  let routes := routesAt store packing (depth+2)
  let pivot := front.1.1.1.pivot
  let extra := BinaryTerminalCacheLifetime.pivotWithTraceAndWork input pivot
  ((⟨count,packing,totals.1,routes.1.1,pivot,extra.1.1.1,extra.1.1.2⟩,
    .join front.1.2 (.join (.block [.frames (depth+(count+n+8)),.arrayAllocation (2*(count+1)^2+16)])
      (.join (.shifted (depth+2) totals.2) (.join routes.1.2 (.shifted (depth+2) extra.1.2))))),
    front.2+routes.2+extra.2+count+n+5+(count*(count+1)+2*count+5))

theorem cache_refines {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    observe (cacheAt input store depth) = offset depth (cacheWithTraceAndWork input store) := by
  have hf := prefix_refines input depth
  generalize hFront : prefixAt input depth = front
  rcases front with ⟨⟨⟨classified,entries⟩,plan⟩,work⟩
  rw [hFront] at hf
  have hd := data_of_refinement hf
  have ht := trace_of_refinement hf
  have hw := work_of_refinement hf
  have hc := congrArg Prod.fst hd
  have he := congrArg Prod.snd hd
  dsimp only [prefixReference] at hc he hw ht
  subst classified
  subst entries
  subst work
  have hr := routes_refines store (BinaryTerminalCacheLifetime.packingOfEntries
    (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1) (depth+2)
  unfold cacheAt
  rw [hFront]
  dsimp only
  simp only [observe,offset,cacheWithTraceAndWork,denote,ht,
    data_of_refinement hr,trace_of_refinement hr,work_of_refinement hr,
    under_append,under_compose,List.append_assoc]
  rfl

theorem cache_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    Bounded (cacheAt input store depth).1.2 := by
  have hf := prefix_bound input depth
  have hr := routes_bound store (BinaryTerminalCacheLifetime.packingOfEntries (prefixAt input depth).1.1.2) (depth+2)
  simp only [Bounded,cacheAt,nodes,payload,List.length_cons,List.length_nil] at hf hr ⊢
  omega

def cacheWithEmission {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    ((BinaryTerminalCacheLifetime.CacheData input × Trace) × ℕ) × ℕ :=
  let planned := cacheAt input store 0
  let emitted := emitFull planned.1.2 []
  (((planned.1.1,emitted.1.1),planned.2),emitted.1.2+emitted.2)

theorem cacheWithEmission_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithEmission input store).1 = cacheWithTraceAndWork input store := by
  have h := cache_refines input store 0
  simpa only [cacheWithEmission,emitFull_erases,emit_data,List.append_nil,observe,offset,under_zero] using h

theorem cacheWithEmission_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithEmission input store).2 ≤ 25*(cacheWithTraceAndWork input store).1.2.length+5 := by
  have hb := cache_bound input store 0
  have ht := trace_of_refinement (cache_refines input store 0)
  rw [under_zero] at ht
  have hp : payload (cacheAt input store 0).1.2 = (cacheWithTraceAndWork input store).1.2.length := by
    rw [← denote_length,ht]
  have he := emitFull_total (cacheAt input store 0).1.2 []
    (5*(cacheWithTraceAndWork input store).1.2.length+1) (by unfold Bounded at hb; omega)
  dsimp only [cacheWithEmission]
  omega

end Blotto.BinaryPhysicalCachePlan

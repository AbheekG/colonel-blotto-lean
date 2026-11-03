import Blotto.BinaryTerminalPrefixLifetime
import Blotto.BinaryTerminalRouteLifetime

/-! The cached terminal data program erases its work field and composes the
traced classification/packing, packing/totals array conversions, route builder
and optional pivot division. Input words, member indices and unchanged tails
remain borrowed; every new reservation remains retained. The model uses the
existing arithmetic allocation producer, with native records/allocator/GC and
the later selected factory/draw kept distinct. -/
set_option autoImplicit false
namespace Blotto.BinaryTerminalCacheLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedTerminalPreparation BinaryCachedTerminalWork
open BinaryTerminalPrefixLifetime BinaryTerminalRouteLifetime

structure CacheData {n : ℕ} (input : BinaryTerminalGrouping.Input n) where
  count : ℕ
  packing : FixedArrayTable count (List (Fin n)×SignedWord)
  totals : FixedArrayTable count SignedWord
  routes : FixedArrayTable n (BinaryGroupRoutes.Route count)
  pivot : Option (Fin n)
  ell : SignedWord
  probability : SignedWord

def erase {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) : CacheData input :=
  ⟨prepared.count,prepared.packing,prepared.totals,prepared.routes,prepared.pivot,prepared.ell,prepared.probability⟩

def pivotWithTraceAndWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    Option (Fin n) → ((SignedWord×SignedWord) × Trace) × ℕ
  | none => (((zero,zero),[.frames 1,.arrayAllocation 8]),0)
  | some j =>
      let probability := BinaryRationalOpcodeAllocation.applyWithAllocation .div (input.resource.read j) (input.length.read j)
      (((input.length.read j,probability.1),[.frames 1,.arrayAllocation 8,
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div (input.resource.read j) (input.length.read j))]),
        (applyWithWork .div (input.resource.read j) (input.length.read j)).2)

def pivotWithTrace {n : ℕ} (input : BinaryTerminalGrouping.Input n)
    (pivot : Option (Fin n)) : (SignedWord×SignedWord) × Trace :=
  (pivotWithTraceAndWork input pivot).1

theorem pivotWithTraceAndWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) (pivot : Option (Fin n)) :
    (pivotWithTraceAndWork input pivot).2 =
      match pivot with
      | none => 0
      | some j => (applyWithWork .div (input.resource.read j) (input.length.read j)).2 := by
  cases pivot <;> rfl

theorem pivotWithTrace_erases {n : ℕ} (input : BinaryTerminalGrouping.Input n) (pivot : Option (Fin n)) :
    (pivotWithTrace input pivot).1 = (selectedLength input pivot,selectedProbability input pivot) := by
  cases pivot with
  | none => rfl
  | some j => simp [pivotWithTrace,pivotWithTraceAndWork,selectedLength,selectedProbability,
      BinaryRationalOpcodeAllocation.applyWithAllocation_state]

theorem pivotWithTraceAndWork_state {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) (pivot : Option (Fin n)) :
    (pivotWithTraceAndWork input pivot).1.1 =
      (selectedLength input pivot,selectedProbability input pivot) :=
  pivotWithTrace_erases input pivot

def cacheWithTraceAndClassificationWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (CacheData input × Trace) × ℕ :=
  let front := prefixWithTraceAndWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  let totals := FixedArrayTable.ofFn (fun g => (packing.read g).2)
  let routes := routesWithTrace input.length packing
  let pivot := front.1.1.pivot
  let extra := pivotWithTrace input pivot
  ((⟨count,packing,totals,routes.1,pivot,extra.1.1,extra.1.2⟩,
    front.1.2.2 ++ [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
      under 2 routes.2 ++ under 2 extra.2),front.2)

def cacheWithTraceAndArithmeticWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (CacheData input × Trace) × ℕ :=
  let front := prefixWithTraceAndArithmeticWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  let totals := FixedArrayTable.ofFn (fun g => (packing.read g).2)
  let routes := routesWithTrace input.length packing
  let pivot := front.1.1.pivot
  let extra := pivotWithTrace input pivot
  ((⟨count,packing,totals,routes.1,pivot,extra.1.1,extra.1.2⟩,
    front.1.2.2 ++ [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
      under 2 routes.2 ++ under 2 extra.2),front.2)

def cacheWithTraceAndPivotWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (CacheData input × Trace) × ℕ :=
  let front := prefixWithTraceAndArithmeticWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  let totals := FixedArrayTable.ofFn (fun g => (packing.read g).2)
  let routes := routesWithTrace input.length packing
  let pivot := front.1.1.pivot
  let extra := pivotWithTraceAndWork input pivot
  ((⟨count,packing,totals,routes.1,pivot,extra.1.1.1,extra.1.1.2⟩,
    front.1.2.2 ++ [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
      under 2 routes.2 ++ under 2 extra.1.2),front.2+extra.2)

def cacheWithTraceAndRouteWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (CacheData input × Trace) × ℕ :=
  let front := prefixWithTraceAndArithmeticWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  let totals := FixedArrayTable.ofFn (fun g => (packing.read g).2)
  let routes := routesWithTraceAndWork input.length packing
  let pivot := front.1.1.pivot
  let extra := pivotWithTraceAndWork input pivot
  ((⟨count,packing,totals,routes.1.1,pivot,extra.1.1.1,extra.1.1.2⟩,
    front.1.2.2 ++ [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
      under 2 routes.1.2 ++ under 2 extra.1.2),front.2+routes.2+extra.2)

theorem cacheWithTraceAndRouteWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndRouteWork input).1 = (cacheWithTraceAndPivotWork input).1 := by
  simp only [cacheWithTraceAndRouteWork,cacheWithTraceAndPivotWork,routesWithTraceAndWork_erases]

def cacheWithTraceAndPatchWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (CacheData input × Trace) × ℕ :=
  let front := prefixWithTraceAndArithmeticWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  let totals := FixedArrayTable.ofFn (fun g => (packing.read g).2)
  let routes := routesWithTraceAndPatchWork input.length packing
  let pivot := front.1.1.pivot
  let extra := pivotWithTraceAndWork input pivot
  ((⟨count,packing,totals,routes.1.1,pivot,extra.1.1.1,extra.1.1.2⟩,
    front.1.2.2 ++ [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
      under 2 routes.1.2 ++ under 2 extra.1.2),front.2+routes.2+extra.2)

theorem cacheWithTraceAndPatchWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndPatchWork input).1 = (cacheWithTraceAndRouteWork input).1 := by
  simp only [cacheWithTraceAndPatchWork,cacheWithTraceAndRouteWork,
    routesWithTraceAndPatchWork_erases]

def cacheWithTraceAndListWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (CacheData input × Trace) × ℕ :=
  let front := prefixWithTraceAndArithmeticWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  let totals := FixedArrayTable.ofFn (fun g => (packing.read g).2)
  let routes := routesWithTraceAndListWork input.length packing
  let pivot := front.1.1.pivot
  let extra := pivotWithTraceAndWork input pivot
  ((⟨count,packing,totals,routes.1.1,pivot,extra.1.1.1,extra.1.1.2⟩,
    front.1.2.2 ++ [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
      under 2 routes.1.2 ++ under 2 extra.1.2),front.2+routes.2+extra.2)

theorem cacheWithTraceAndListWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndListWork input).1 = (cacheWithTraceAndPatchWork input).1 := by
  simp only [cacheWithTraceAndListWork,cacheWithTraceAndPatchWork,
    routesWithTraceAndListWork_erases]

def cacheWithTrace {n : ℕ} (input : BinaryTerminalGrouping.Input n) : CacheData input × Trace :=
  (cacheWithTraceAndListWork input).1

theorem cacheWithTraceAndPivotWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndPivotWork input).1 =
      (cacheWithTraceAndArithmeticWork input).1 := rfl

theorem cacheWithTraceAndClassificationWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndClassificationWork input).1 = cacheWithTrace input := by
  rw [cacheWithTrace,cacheWithTraceAndListWork_erases,cacheWithTraceAndPatchWork_erases,
    cacheWithTraceAndRouteWork_erases]
  rfl

theorem cacheWithTraceAndArithmeticWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndArithmeticWork input).2 =
      (BinaryTerminalClassificationWork.classifyAndPack input).1.booleanWork +
        (BinaryGreedyPackingWork.pack input.length.read input.budget
          (BinaryTerminalGrouping.uniformItems input)).2 :=
  prefixWithTraceAndArithmeticWork_charge input

theorem cacheWithTraceAndPivotWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndPivotWork input).2 =
      (BinaryTerminalClassificationWork.classifyAndPack input).1.booleanWork +
        (BinaryGreedyPackingWork.pack input.length.read input.budget
          (BinaryTerminalGrouping.uniformItems input)).2 +
        BinaryCachedTerminalWork.pivotArithmeticWork (prepare input) := by
  unfold cacheWithTraceAndPivotWork
  dsimp only
  rw [prefixWithTraceAndArithmeticWork_charge,pivotWithTraceAndWork_charge]
  have hPivot := (prefixWithTrace_erases input).2.1
  simp only [prefixWithTrace] at hPivot
  rw [hPivot]
  rfl

theorem cacheWithTraceAndPivotWork_reached_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (cacheWithTraceAndPivotWork (terminalInput request rich state)).2 ≤
      (166000*n+96000)*(request.source.originalInputWordWidth+2)^3 := by
  have hPrefix := prefixWithTraceAndArithmeticWork_reached_bound
    request rich N bits state h
  rw [prefixWithTraceAndArithmeticWork_charge] at hPrefix
  have hPivot := BinaryCachedTerminalWork.reached_pivotArithmeticWork_bound
    request rich N bits state h
  rw [cacheWithTraceAndPivotWork_charge]
  nlinarith only [hPrefix,hPivot]

theorem cacheWithTraceAndClassificationWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndClassificationWork input).2 =
      (BinaryTerminalClassificationWork.classifyAndPack input).1.booleanWork :=
  prefixWithTraceAndWork_charge input

def buildCache {n : ℕ} (input : BinaryTerminalGrouping.Input n) (entries : List (List (Fin n)×SignedWord))
    (pivot : Option (Fin n)) : CacheData input :=
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  ⟨count,packing,FixedArrayTable.ofFn (fun g => (packing.read g).2),BinaryGroupRoutes.prepare input.length packing,
    pivot,selectedLength input pivot,selectedProbability input pivot⟩

theorem cacheWithTrace_build {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTrace input).1=buildCache input (prefixWithTrace input).2.1 (prefixWithTrace input).1.pivot := by
  rw [cacheWithTrace,cacheWithTraceAndListWork_erases,cacheWithTraceAndPatchWork_erases,
    cacheWithTraceAndRouteWork_erases]
  unfold cacheWithTraceAndPivotWork buildCache
  simp only [prefixWithTrace]
  simp only [routesWithTrace_erases,pivotWithTraceAndWork_state]

-- The complete runtime cache fields agree, while the old arithmetic-work
-- observer field is absent from CacheData.
theorem cacheWithTrace_erases {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTrace input).1 = erase (prepare input) := by
  have hFront := prefixWithTrace_erases input
  rw [cacheWithTrace_build,hFront.2.2,hFront.2.1]
  unfold buildCache erase prepare
  dsimp only
  split <;> simp_all [selectedLength,selectedProbability]

def packingOfEntries {n : ℕ} (entries : List (List (Fin n)×SignedWord)) :
    FixedArrayTable entries.length (List (Fin n)×SignedWord) :=
  ⟨entries.toArray,by simp⟩

theorem selected_route_work_eq_prepared {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (routesWithTraceAndWork input.length
      (packingOfEntries (prefixWithTraceAndArithmeticWork input).1.2.1)).2 =
    (routesWithTraceAndWork input.length (prepare input).packing).2 := by
  have hEntries := (prefixWithTrace_erases input).2.2
  simp only [prefixWithTrace] at hEntries
  have h := congrArg (fun entries =>
    (routesWithTraceAndWork input.length (packingOfEntries entries)).2) hEntries
  simpa only [prepare,packingOfEntries] using h

theorem selected_patch_work_eq_prepared {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (routesWithTraceAndPatchWork input.length
      (packingOfEntries (prefixWithTraceAndArithmeticWork input).1.2.1)).2 =
    (routesWithTraceAndPatchWork input.length (prepare input).packing).2 := by
  have hEntries := (prefixWithTrace_erases input).2.2
  simp only [prefixWithTrace] at hEntries
  have h := congrArg (fun entries =>
    (routesWithTraceAndPatchWork input.length (packingOfEntries entries)).2) hEntries
  simpa only [prepare,packingOfEntries] using h

theorem selected_list_work_eq_prepared {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (routesWithTraceAndListWork input.length
      (packingOfEntries (prefixWithTraceAndArithmeticWork input).1.2.1)).2 =
    (routesWithTraceAndListWork input.length (prepare input).packing).2 := by
  have hEntries := (prefixWithTrace_erases input).2.2
  simp only [prefixWithTrace] at hEntries
  have h := congrArg (fun entries =>
    (routesWithTraceAndListWork input.length (packingOfEntries entries)).2) hEntries
  simpa only [prepare,packingOfEntries] using h

theorem cacheWithTraceAndRouteWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndRouteWork input).2 =
      (cacheWithTraceAndPivotWork input).2 +
        (routesWithTraceAndWork input.length
          (⟨(prefixWithTraceAndArithmeticWork input).1.2.1.toArray,
            by simp⟩ : FixedArrayTable (prefixWithTraceAndArithmeticWork input).1.2.1.length
              (List (Fin n)×SignedWord))).2 := by
  unfold cacheWithTraceAndRouteWork cacheWithTraceAndPivotWork
  dsimp only
  omega

theorem cacheWithTraceAndRouteWork_ledger {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndRouteWork input).2 =
      (BinaryTerminalClassificationWork.classifyAndPack input).1.booleanWork +
        (BinaryGreedyPackingWork.pack input.length.read input.budget
          (BinaryTerminalGrouping.uniformItems input)).2 +
        routeArithmeticWork (prepare input) + pivotArithmeticWork (prepare input) := by
  rw [cacheWithTraceAndRouteWork_charge]
  change (cacheWithTraceAndPivotWork input).2 +
    (routesWithTraceAndWork input.length
      (packingOfEntries (prefixWithTraceAndArithmeticWork input).1.2.1)).2 = _
  rw [selected_route_work_eq_prepared,routesWithTraceAndWork_prepared_charge,
    cacheWithTraceAndPivotWork_charge]
  omega

theorem cacheWithTraceAndRouteWork_reached_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (cacheWithTraceAndRouteWork (terminalInput request rich state)).2 ≤
      (454000*n+96000)*(request.source.originalInputWordWidth+2)^3 := by
  have hPrior := cacheWithTraceAndPivotWork_reached_bound request rich N bits state h
  have hRoute := reached_routesWithTraceAndWork_bound request rich N bits state h
  rw [cacheWithTraceAndRouteWork_charge]
  change (cacheWithTraceAndPivotWork (terminalInput request rich state)).2 +
    (routesWithTraceAndWork (terminalInput request rich state).length
      (packingOfEntries (prefixWithTraceAndArithmeticWork
        (terminalInput request rich state)).1.2.1)).2 ≤ _
  rw [selected_route_work_eq_prepared]
  nlinarith only [hPrior,hRoute]

theorem cacheWithTraceAndPatchWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndPatchWork input).2 =
      (cacheWithTraceAndPivotWork input).2 +
        (routesWithTraceAndPatchWork input.length
          (packingOfEntries (prefixWithTraceAndArithmeticWork input).1.2.1)).2 := by
  unfold cacheWithTraceAndPatchWork cacheWithTraceAndPivotWork packingOfEntries
  dsimp only
  omega

theorem cacheWithTraceAndPatchWork_reached_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (cacheWithTraceAndPatchWork (terminalInput request rich state)).2 ≤
      (454000*n+96000)*(request.source.originalInputWordWidth+2)^3 + 3*n*(n+1)+1 := by
  have hPrior := cacheWithTraceAndPivotWork_reached_bound request rich N bits state h
  have hRoute := reached_routesWithTraceAndPatchWork_bound request rich N bits state h
  rw [cacheWithTraceAndPatchWork_charge,selected_patch_work_eq_prepared]
  nlinarith only [hPrior,hRoute]

theorem cacheWithTraceAndListWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTraceAndListWork input).2 =
      (cacheWithTraceAndPivotWork input).2 +
        (routesWithTraceAndListWork input.length
          (packingOfEntries (prefixWithTraceAndArithmeticWork input).1.2.1)).2 := by
  unfold cacheWithTraceAndListWork cacheWithTraceAndPivotWork packingOfEntries
  dsimp only
  omega

theorem cacheWithTraceAndListWork_reached_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (cacheWithTraceAndListWork (terminalInput request rich state)).2 ≤
      (454000*n+96000)*(request.source.originalInputWordWidth+2)^3 +
        3*n*(n+1)+7*n+12 := by
  have hPrior := cacheWithTraceAndPivotWork_reached_bound request rich N bits state h
  have hRoute := reached_routesWithTraceAndListWork_bound request rich N bits state h
  rw [cacheWithTraceAndListWork_charge,selected_list_work_eq_prepared]
  nlinarith only [hPrior,hRoute]


theorem pivotWithTrace_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (pivot : Option (Fin n)) (W : ℕ)
    (hL : ∀ j,width (input.length.read j) ≤ W) (hR : ∀ j,width (input.resource.read j) ≤ W) :
    listCells (pivotWithTrace input pivot).2+arraySlots (pivotWithTrace input pivot).2 ≤ 2000000*(W+2)^4+8 ∧
    framePeak (pivotWithTrace input pivot).2 ≤ 1 := by
  cases pivot with
  | none => simp [pivotWithTrace,pivotWithTraceAndWork,listCells,arraySlots,framePeak]
  | some j =>
      have hp := (BinaryRationalOpcodeAllocation.opcodeStorage_bound .div (input.resource.read j) (input.length.read j)).trans
        (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le (hR j) (hL j)) 2) 4))
      simp only [pivotWithTrace,pivotWithTraceAndWork,listCells,arraySlots,framePeak]
      exact ⟨by omega,by omega⟩

-- A trace helper hides dependent count/array sizes behind a fixed result type.
def assemblyTrace {n : ℕ} (input : BinaryTerminalGrouping.Input n) (entries : List (List (Fin n)×SignedWord))
    (pivot : Option (Fin n)) : Trace :=
  let count := entries.length
  let packing : FixedArrayTable count (List (Fin n)×SignedWord) := ⟨entries.toArray,by simp [count]⟩
  [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
    under 2 (routesWithTrace input.length packing).2 ++ under 2 (pivotWithTrace input pivot).2

theorem cacheWithTrace_trace {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (cacheWithTrace input).2 = (prefixWithTrace input).2.2 ++
      assemblyTrace input (prefixWithTrace input).2.1 (prefixWithTrace input).1.pivot := by
  rw [cacheWithTrace,cacheWithTraceAndListWork_erases,cacheWithTraceAndPatchWork_erases,
    cacheWithTraceAndRouteWork_erases]
  unfold cacheWithTraceAndPivotWork assemblyTrace
  simp only [prefixWithTrace]
  simp only [pivotWithTrace]
  simp only [List.append_assoc]

noncomputable def cacheBound {n : ℕ} (request : BinaryPRGRequest.Request n) : ℕ :=
  prefixBound request+reachedRouteBound request+2000000*(5+2*request.source.originalInputWordWidth)^4+56

theorem reached_assembly_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    listCells (assemblyTrace (terminalInput request rich state)
      (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).2.1
      (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).1.pivot)+
      arraySlots (assemblyTrace (terminalInput request rich state)
        (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).2.1
        (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).1.pivot) ≤
      reachedRouteBound request+2000000*(5+2*request.source.originalInputWordWidth)^4+56 ∧
    framePeak (assemblyTrace (terminalInput request rich state)
      (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).2.1
      (BinaryTerminalClassificationWork.classifyAndPack (terminalInput request rich state)).1.pivot) ≤ 4*n+18 := by
  let input := terminalInput request rich state
  let cached := prepare input
  have hc := terminal_canonical request rich state
  have ha := terminal_admissible request rich N bits state h
  have hCount : cached.count ≤ 3 := by rcases cached.count_bound hc ha with he|he <;> omega
  have hRoutes := reached_routes_bound request rich N bits state h
  have hPivot := pivotWithTrace_bound input (BinaryTerminalClassificationWork.classifyAndPack input).1.pivot
    (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)
    (terminal_length_width request rich state) (terminal_resource_width request rich N bits state h)
  have hW : 1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator+2 ≤
      5+2*request.source.originalInputWordWidth := by
    have hd := request.source.normalized_lattice_wordWidth_original
    omega
  have hPivotTop := hPivot.1.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left hW 4)) 8)
  have hRegions : 2*(cached.count+1)^2+16 ≤ 48 := by nlinarith only [hCount]
  have hRouteFrames := framePeak_under 2 (routesWithTrace input.length cached.packing).2
  have hPivotFrames := framePeak_under 2 (pivotWithTrace input (BinaryTerminalClassificationWork.classifyAndPack input).1.pivot).2
  unfold assemblyTrace
  dsimp only
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  change _ ≤ _ ∧ _
  dsimp only [cached,input,prepare] at hRoutes hPivotTop hRouteFrames hPivotFrames hPivot hRegions hCount
  exact ⟨by nlinarith only [hRoutes.1,hPivotTop,hRegions],by omega⟩

theorem reached_cache_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    listCells (cacheWithTrace (terminalInput request rich state)).2+arraySlots (cacheWithTrace (terminalInput request rich state)).2 ≤
      cacheBound request ∧ framePeak (cacheWithTrace (terminalInput request rich state)).2 ≤ 4*n+18 := by
  have hFront := prefixWithTrace_erases (terminalInput request rich state)
  have hPrefix := reached_prefix_bound request rich N bits state h
  have hAssembly := reached_assembly_bound request rich N bits state h
  rw [cacheWithTrace_trace]
  simp only [listCells_append,arraySlots_append,framePeak_append]
  rw [hFront.2.2,hFront.2.1]
  unfold cacheBound
  exact ⟨by nlinarith only [hPrefix.1,hAssembly.1],by omega⟩

theorem reached_cache_all_prefix {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) (borrowedSeedCells retainedInputCells steps : ℕ) :
    retainedHeap (borrowedSeedCells+retainedInputCells) (cacheWithTrace (terminalInput request rich state)).2 steps ≤
      borrowedSeedCells+retainedInputCells+cacheBound request := by
  have hSpace := (reached_cache_bound request rich N bits state h).1
  have hl := listCells_take_le (cacheWithTrace (terminalInput request rich state)).2 steps
  have ha := arraySlots_take_le (cacheWithTrace (terminalInput request rich state)).2 steps
  unfold retainedHeap
  omega


def envelope (n S : ℕ) : ℕ :=
  n*(7500*(4+2*S)^3+9)+8+n*packingStepBound (3+2*S)+n*(n+12)+9+n+8+
    routeBound n 3 (3+2*S)+2000000*(5+2*S)^4+56

theorem cacheBound_eq {n : ℕ} (request : BinaryPRGRequest.Request n) : cacheBound request=envelope n request.source.originalInputWordWidth := rfl

theorem envelope_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) : envelope n S ≤ envelope m T := by
  unfold envelope packingStepBound routeBound
  gcongr

def frameBound (length : ℕ) : ℕ := envelope length (3*length+6)
def polynomialBound (length : ℕ) : ℕ := 2^60*(length+1)^5

set_option maxHeartbeats 1000000 in
theorem frameBound_polynomial (length : ℕ) : frameBound length ≤ polynomialBound length := by
  let t := length+1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hN : length ≤ t := by dsimp [t]; omega
  have hS : 3*length+6 ≤ 6*t := by dsimp [t]; omega
  have hTop := envelope_mono hN hS
  have h0 : 1 ≤ t^5 := Nat.one_le_pow 5 t ht
  have h1 : t ≤ t^5 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<t) (by decide : 1 ≤ 5)
  have h2 : t^2 ≤ t^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : t^3 ≤ t^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : t^4 ≤ t^5 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold frameBound polynomialBound
  change envelope length (3*length+6) ≤ 2^60*t^5
  unfold envelope packingStepBound routeBound
  unfold envelope packingStepBound routeBound at hTop
  norm_num only [Nat.reducePow] at ⊢
  ring_nf at hTop
  nlinarith only [hTop,h0,h1,h2,h3,h4]

theorem parsed_cache_all_prefix_polynomial (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n)×List Bool)
    (hParsed : (BinaryPRGAccuracyRulerRequest.read frame).1=some parsed) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision)
    (state : BinaryResourcePair.Certified (resourceInput parsed.1.2.request rich).length)
    (hState : (resourceWork parsed.1.2.request rich
      (RationalLottoResourceSystem.coinBitBudget parsed.1.1 parsed.1.2.request.precision) tables.choice.read).1.1=some state)
    (originalSeedLength retainedInputCells steps : ℕ) :
    retainedHeap (originalSeedLength+retainedInputCells) (cacheWithTrace (terminalInput parsed.1.2.request rich state)).2 steps ≤
      originalSeedLength+retainedInputCells+2^60*(frame.length+1)^5 := by
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hParsed
  have hS := BinaryPRGFrameCostJoin.read_source_width frame parsed hParsed
  have hCache := reached_cache_all_prefix parsed.1.2.request rich _ tables.choice.read state hState originalSeedLength retainedInputCells steps
  have hEnvelope := envelope_mono hn hS
  rw [← cacheBound_eq] at hEnvelope
  exact hCache.trans (Nat.add_le_add_left (hEnvelope.trans (frameBound_polynomial frame.length)) _)

end Blotto.BinaryTerminalCacheLifetime

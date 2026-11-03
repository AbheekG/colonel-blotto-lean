import Blotto.ArrayStoreRAM
import Blotto.BinaryPRGResourceLifetime
import Blotto.BinaryCachedTerminalWork

/-! Transient cached-route construction reserves every division workspace,
assignment list/record, initial full-region array and old/new patch arrays.
All versions remain retained. Input/group words are borrowed. Exact native
assignments and route contents are preserved. This is the old arithmetic
allocation model; native spare capacity/layout, scalar records and GC remain
separate. The source trace counts reserve slots, not native heap bytes. -/
set_option autoImplicit false
namespace Blotto.BinaryTerminalRouteLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryRationalOpcode BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedTerminalPreparation
open BinaryCachedTerminalWork
open scoped BigOperators

def membersWithTrace {n m : ℕ} (length : FixedArrayTable n SignedWord) (total : SignedWord) (g : Fin m) :
    List (Fin n) → List (Fin n×BinaryGroupRoutes.Route m) × Trace
  | [] => ([],[.frames 1,.arrayAllocation 8])
  | j::rest =>
      let divided := BinaryRationalOpcodeAllocation.applyWithAllocation .div (length.read j) total
      let later := membersWithTrace length total g rest
      ((j,(some g,divided.1))::later.1,[.frames 1,.arrayAllocation 8,.listAllocation 1,
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div (length.read j) total)] ++ under 1 later.2)

theorem membersWithTrace_erases {n m : ℕ} (length : FixedArrayTable n SignedWord) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) :
    (membersWithTrace length total g items).1 = items.map (fun j =>
      (j,(some g,apply .div (length.read j) total))) := by
  induction items with
  | nil => rfl
  | cons j rest ih => simp only [membersWithTrace,ih,BinaryRationalOpcodeAllocation.applyWithAllocation_state,List.map_cons]

theorem membersWithTrace_bounds {n m : ℕ} (length : FixedArrayTable n SignedWord) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (W : ℕ) (hL : ∀ j,width (length.read j) ≤ W) (hT : width total ≤ W) :
    listCells (membersWithTrace length total g items).2+arraySlots (membersWithTrace length total g items).2 ≤
      items.length*(2000000*(W+2)^4+9)+8 ∧ framePeak (membersWithTrace length total g items).2 ≤ items.length+1 := by
  induction items with
  | nil => simp [membersWithTrace,listCells,arraySlots,framePeak]
  | cons j rest ih =>
      have hOpcode := (BinaryRationalOpcodeAllocation.opcodeStorage_bound .div (length.read j) total).trans
        (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le (hL j) hT) 2) 4))
      have hf := framePeak_under 1 (membersWithTrace length total g rest).2
      simp only [membersWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,List.length_cons]
      exact ⟨by nlinarith only [ih.1,hOpcode],by omega⟩

def groupsWithTrace {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    List (Fin m) → List (Fin n×BinaryGroupRoutes.Route m) × Trace
  | [] => ([],[.frames 1,.arrayAllocation 8])
  | g::rest =>
      let memberResult := membersWithTrace length (groups.read g).2 g (groups.read g).1
      let later := groupsWithTrace length groups rest
      (memberResult.1++later.1,[.frames 2,.arrayAllocation 8,.listAllocation memberResult.1.length] ++
        under 2 memberResult.2 ++ under 2 later.2)

theorem groupsWithTrace_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m)) :
    (groupsWithTrace length groups items).1 = items.flatMap (fun g => (groups.read g).1.map (fun j =>
      (j,(some g,apply .div (length.read j) (groups.read g).2)))) := by
  induction items with
  | nil => rfl
  | cons g rest ih => simp only [groupsWithTrace,membersWithTrace_erases,ih,List.flatMap_cons]

theorem groupsWithTrace_bounds {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m)) (W : ℕ)
    (hL : ∀ j,width (length.read j) ≤ W) (hT : ∀ g,width (groups.read g).2 ≤ W)
    (hM : ∀ g,(groups.read g).1.length ≤ n) :
    listCells (groupsWithTrace length groups items).2+arraySlots (groupsWithTrace length groups items).2 ≤
      items.length*(n*(2000000*(W+2)^4+10)+16)+8 ∧
    framePeak (groupsWithTrace length groups items).2 ≤ 2*items.length+n+1 := by
  induction items with
  | nil => simp [groupsWithTrace,listCells,arraySlots,framePeak]
  | cons g rest ih =>
      have hl := membersWithTrace_bounds length (groups.read g).2 g (groups.read g).1 W hL (hT g)
      have hlen : (membersWithTrace length (groups.read g).2 g (groups.read g).1).1.length = (groups.read g).1.length := by
        rw [membersWithTrace_erases,List.length_map]
      have hlu := framePeak_under 2 (membersWithTrace length (groups.read g).2 g (groups.read g).1).2
      have hru := framePeak_under 2 (groupsWithTrace length groups rest).2
      have hm := hM g
      have hMono := Nat.mul_le_mul_right (2000000*(W+2)^4+10) hm
      simp only [groupsWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,List.length_cons]
      rw [hlen]
      exact ⟨by nlinarith only [hl.1,ih.1,hMono],by omega⟩

def routeWords {m : ℕ} (route : BinaryGroupRoutes.Route m) : ℕ := 4+BinaryRationalRegisterProgram.payloadWords route.2

def patchWithTrace {n m : ℕ} : List (Fin n×BinaryGroupRoutes.Route m) → FixedArrayTable n (BinaryGroupRoutes.Route m) →
    FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace
  | [],table => (table,[.frames 1,.arrayAllocation 8])
  | entry::rest,table =>
      let next := table.write entry.1 entry.2
      let later := patchWithTrace rest next
      (later.1,[.frames 1,.arrayAllocation (table.payloadWordSum routeWords+next.payloadWordSum routeWords+8)] ++ under 1 later.2)

-- Each native `Array.set` receives an allowance of one control visit plus
-- a full scan of the fixed n-slot region. Native copy-on-write ownership and
-- reference-bit costs are separate from this source-loop charge.
def patchWithTraceAndWork {n m : ℕ} :
    List (Fin n×BinaryGroupRoutes.Route m) →
    FixedArrayTable n (BinaryGroupRoutes.Route m) →
    (FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace) × ℕ
  | [],table => ((table,[.frames 1,.arrayAllocation 8]),1)
  | entry::rest,table =>
      let next := table.write entry.1 entry.2
      let later := patchWithTraceAndWork rest next
      ((later.1.1,[.frames 1,.arrayAllocation
        (table.payloadWordSum routeWords+next.payloadWordSum routeWords+8)] ++ under 1 later.1.2),
        n+1+later.2)

theorem patchWithTraceAndWork_erases {n m : ℕ}
    (entries : List (Fin n×BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    (patchWithTraceAndWork entries table).1 = patchWithTrace entries table := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry rest ih => simp only [patchWithTraceAndWork,patchWithTrace,ih]

theorem patchWithTraceAndWork_charge {n m : ℕ}
    (entries : List (Fin n×BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    (patchWithTraceAndWork entries table).2 = entries.length*(n+1)+1 := by
  induction entries generalizing table with
  | nil => simp [patchWithTraceAndWork]
  | cons entry rest ih =>
      simp only [patchWithTraceAndWork,ih,List.length_cons]
      ring

theorem patchWithTrace_erases {n m : ℕ} (entries : List (Fin n×BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) : (patchWithTrace entries table).1=table.patch entries := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry rest ih => exact ih (table.write entry.1 entry.2)

theorem patchWithTrace_bound {n m : ℕ} (entries : List (Fin n×BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) (P : ℕ) (hTable : ∀ j,routeWords (table.read j) ≤ P)
    (hEntries : ∀ entry∈entries,routeWords entry.2 ≤ P) :
    listCells (patchWithTrace entries table).2+arraySlots (patchWithTrace entries table).2 ≤
      entries.length*(2*n*P+8)+8 ∧ framePeak (patchWithTrace entries table).2 ≤ entries.length+1 := by
  induction entries generalizing table with
  | nil => simp [patchWithTrace,listCells,arraySlots,framePeak]
  | cons entry rest ih =>
      have he := hEntries entry (by simp)
      have hNext := table.write_words_bound routeWords P hTable entry.1 entry.2 he
      have hOld := table.payloadWordSum_bound routeWords P hTable
      have hNew := (table.write entry.1 entry.2).payloadWordSum_bound routeWords P hNext
      have hLater := ih (table.write entry.1 entry.2) hNext (fun e hm => hEntries e (List.mem_cons_of_mem _ hm))
      have hFrames := framePeak_under 1 (patchWithTrace rest (table.write entry.1 entry.2)).2
      simp only [patchWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,List.length_cons]
      exact ⟨by nlinarith only [hLater.1,hOld,hNew],by omega⟩

def routesWithTrace {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) : FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace :=
  let assignments := groupsWithTrace length groups (List.finRange m)
  let initial := FixedArrayTable.ofFn (fun _ : Fin n => (none,zero) : Fin n→BinaryGroupRoutes.Route m)
  let patched := patchWithTrace assignments.1 initial
  (patched.1,[.frames (n+m+8),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)] ++ under 2 assignments.2 ++ under 2 patched.2)

-- The arithmetic charge is produced at each division in the same recursive
-- traversal that constructs the assignment and its allocation trace.
def membersWithTraceAndWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (total : SignedWord) (g : Fin m) :
    List (Fin n) → (List (Fin n×BinaryGroupRoutes.Route m) × Trace) × ℕ
  | [] => (([],[.frames 1,.arrayAllocation 8]),0)
  | j::rest =>
      let divided := BinaryRationalOpcodeAllocation.applyWithAllocation .div (length.read j) total
      let later := membersWithTraceAndWork length total g rest
      (((j,(some g,divided.1))::later.1.1,[.frames 1,.arrayAllocation 8,.listAllocation 1,
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div (length.read j) total)] ++ under 1 later.1.2),
        (applyWithWork .div (length.read j) total).2 + later.2)

theorem membersWithTraceAndWork_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (total : SignedWord) (g : Fin m) (items : List (Fin n)) :
    (membersWithTraceAndWork length total g items).1 = membersWithTrace length total g items := by
  induction items with
  | nil => rfl
  | cons j rest ih => simp only [membersWithTraceAndWork,membersWithTrace,ih]

theorem membersWithTraceAndWork_charge {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (total : SignedWord) (g : Fin m) (items : List (Fin n)) :
    (membersWithTraceAndWork length total g items).2 =
      (items.map (fun j => (applyWithWork .div (length.read j) total).2)).sum := by
  induction items with
  | nil => rfl
  | cons j rest ih => simp only [membersWithTraceAndWork,ih,List.map_cons,List.sum_cons]

def membersWithTraceAndListWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (total : SignedWord) (g : Fin m) :
    List (Fin n) → (List (Fin n×BinaryGroupRoutes.Route m) × Trace) × ℕ
  | [] => (([],[.frames 1,.arrayAllocation 8]),1)
  | j::rest =>
      let divided := BinaryRationalOpcodeAllocation.applyWithAllocation .div (length.read j) total
      let later := membersWithTraceAndListWork length total g rest
      (((j,(some g,divided.1))::later.1.1,[.frames 1,.arrayAllocation 8,.listAllocation 1,
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div (length.read j) total)] ++ under 1 later.1.2),
        (applyWithWork .div (length.read j) total).2 + later.2 + 1)

theorem membersWithTraceAndListWork_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (total : SignedWord) (g : Fin m) (items : List (Fin n)) :
    (membersWithTraceAndListWork length total g items).1 =
      (membersWithTraceAndWork length total g items).1 := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      simp only [membersWithTraceAndListWork,membersWithTraceAndWork,ih]

theorem membersWithTraceAndListWork_charge {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (total : SignedWord) (g : Fin m) (items : List (Fin n)) :
    (membersWithTraceAndListWork length total g items).2 =
      (membersWithTraceAndWork length total g items).2 + items.length + 1 := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      simp only [membersWithTraceAndListWork,membersWithTraceAndWork,ih,List.length_cons]
      omega

def groupsWithTraceAndWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    List (Fin m) → (List (Fin n×BinaryGroupRoutes.Route m) × Trace) × ℕ
  | [] => (([],[.frames 1,.arrayAllocation 8]),0)
  | g::rest =>
      let memberResult := membersWithTraceAndWork length (groups.read g).2 g (groups.read g).1
      let later := groupsWithTraceAndWork length groups rest
      ((memberResult.1.1++later.1.1,[.frames 2,.arrayAllocation 8,.listAllocation memberResult.1.1.length] ++
        under 2 memberResult.1.2 ++ under 2 later.1.2),memberResult.2+later.2)

theorem groupsWithTraceAndWork_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m)) :
    (groupsWithTraceAndWork length groups items).1 = groupsWithTrace length groups items := by
  induction items with
  | nil => rfl
  | cons g rest ih =>
      simp only [groupsWithTraceAndWork,groupsWithTrace,membersWithTraceAndWork_erases,ih]

theorem groupsWithTraceAndWork_charge {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m)) :
    (groupsWithTraceAndWork length groups items).2 =
      (items.map (fun g => ((groups.read g).1.map (fun j =>
        (applyWithWork .div (length.read j) (groups.read g).2).2)).sum)).sum := by
  induction items with
  | nil => rfl
  | cons g rest ih =>
      simp only [groupsWithTraceAndWork,membersWithTraceAndWork_charge,ih,List.map_cons,List.sum_cons]

def groupsWithTraceAndListWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    List (Fin m) → (List (Fin n×BinaryGroupRoutes.Route m) × Trace) × ℕ
  | [] => (([],[.frames 1,.arrayAllocation 8]),1)
  | g::rest =>
      let memberResult := membersWithTraceAndListWork length (groups.read g).2 g (groups.read g).1
      let later := groupsWithTraceAndListWork length groups rest
      ((memberResult.1.1++later.1.1,[.frames 2,.arrayAllocation 8,.listAllocation memberResult.1.1.length] ++
        under 2 memberResult.1.2 ++ under 2 later.1.2),
        memberResult.2+later.2+memberResult.1.1.length+1)

theorem groupsWithTraceAndListWork_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m)) :
    (groupsWithTraceAndListWork length groups items).1 =
      (groupsWithTraceAndWork length groups items).1 := by
  induction items with
  | nil => rfl
  | cons g rest ih =>
      simp only [groupsWithTraceAndListWork,groupsWithTraceAndWork,
        membersWithTraceAndListWork_erases,ih]

theorem groupsWithTraceAndListWork_charge {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m)) :
    (groupsWithTraceAndListWork length groups items).2 =
      (groupsWithTraceAndWork length groups items).2 +
        (items.map (fun g => 2*(groups.read g).1.length+2)).sum+1 := by
  induction items with
  | nil => rfl
  | cons g rest ih =>
      have hlen : (membersWithTraceAndListWork length (groups.read g).2 g
          (groups.read g).1).1.1.length = (groups.read g).1.length := by
        rw [membersWithTraceAndListWork_erases,membersWithTraceAndWork_erases,
          membersWithTrace_erases,List.length_map]
      simp only [groupsWithTraceAndListWork,groupsWithTraceAndWork,
        membersWithTraceAndListWork_charge,ih,List.map_cons,List.sum_cons]
      rw [hlen]
      omega

theorem groupsWithTraceAndListWork_extra_bound {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m))
    (hM : ∀ g,(groups.read g).1.length ≤ n) :
    (groupsWithTraceAndListWork length groups items).2 ≤
      (groupsWithTraceAndWork length groups items).2 + items.length*(2*n+2)+1 := by
  have hSum : (items.map (fun g => 2*(groups.read g).1.length+2)).sum ≤
      items.length*(2*n+2) := by
    induction items with
    | nil => simp
    | cons g rest ih =>
        have hm := hM g
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith only [hm,ih]
  rw [groupsWithTraceAndListWork_charge]
  omega

def routesWithTraceAndWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace) × ℕ :=
  let assignments := groupsWithTraceAndWork length groups (List.finRange m)
  let initial := FixedArrayTable.ofFn (fun _ : Fin n => (none,zero) : Fin n→BinaryGroupRoutes.Route m)
  let patched := patchWithTrace assignments.1.1 initial
  ((patched.1,[.frames (n+m+8),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)] ++
      under 2 assignments.1.2 ++ under 2 patched.2),assignments.2)

def routesWithTraceAndPatchWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace) × ℕ :=
  let assignments := groupsWithTraceAndWork length groups (List.finRange m)
  let initial := FixedArrayTable.ofFn (fun _ : Fin n => (none,zero) : Fin n→BinaryGroupRoutes.Route m)
  let patched := patchWithTraceAndWork assignments.1.1 initial
  ((patched.1.1,[.frames (n+m+8),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)] ++
      under 2 assignments.1.2 ++ under 2 patched.1.2),assignments.2+patched.2)

theorem routesWithTraceAndPatchWork_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (routesWithTraceAndPatchWork length groups).1 =
      (routesWithTraceAndWork length groups).1 := by
  simp only [routesWithTraceAndPatchWork,routesWithTraceAndWork,patchWithTraceAndWork_erases]

theorem routesWithTraceAndPatchWork_charge {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (routesWithTraceAndPatchWork length groups).2 =
      (routesWithTraceAndWork length groups).2 +
        (groupsWithTraceAndWork length groups (List.finRange m)).1.1.length*(n+1)+1 := by
  simp only [routesWithTraceAndPatchWork,routesWithTraceAndWork,patchWithTraceAndWork_charge]
  omega

def routesWithTraceAndListWork {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace) × ℕ :=
  let assignments := groupsWithTraceAndListWork length groups (List.finRange m)
  let initial := FixedArrayTable.ofFn (fun _ : Fin n => (none,zero) : Fin n→BinaryGroupRoutes.Route m)
  let patched := patchWithTraceAndWork assignments.1.1 initial
  ((patched.1.1,[.frames (n+m+8),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)] ++
      under 2 assignments.1.2 ++ under 2 patched.1.2),assignments.2+patched.2+m+n+1)

theorem routesWithTraceAndListWork_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (routesWithTraceAndListWork length groups).1 =
      (routesWithTraceAndPatchWork length groups).1 := by
  simp only [routesWithTraceAndListWork,routesWithTraceAndPatchWork,
    groupsWithTraceAndListWork_erases]

theorem routesWithTraceAndListWork_extra_bound {n m : ℕ}
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord))
    (hM : ∀ g,(groups.read g).1.length ≤ n) :
    (routesWithTraceAndListWork length groups).2 ≤
      (routesWithTraceAndPatchWork length groups).2 + m*(2*n+3)+n+2 := by
  have hGroups := groupsWithTraceAndListWork_extra_bound length groups (List.finRange m) hM
  simp only [List.length_finRange] at hGroups
  have hEntries := congrArg Prod.fst (groupsWithTraceAndListWork_erases length groups (List.finRange m))
  unfold routesWithTraceAndListWork routesWithTraceAndPatchWork
  dsimp only
  rw [hEntries]
  nlinarith only [hGroups]

theorem routesWithTraceAndWork_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (routesWithTraceAndWork length groups).1 = routesWithTrace length groups := by
  simp only [routesWithTraceAndWork,routesWithTrace,groupsWithTraceAndWork_erases]

theorem routesWithTraceAndWork_charge {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (routesWithTraceAndWork length groups).2 =
      ∑ g : Fin m, ((groups.read g).1.map (fun j =>
        (applyWithWork .div (length.read j) (groups.read g).2).2)).sum := by
  simp only [routesWithTraceAndWork,groupsWithTraceAndWork_charge]
  rw [← List.sum_toFinset _ (List.nodup_finRange m), List.toFinset_finRange]

theorem routesWithTraceAndWork_uniform_bound {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (W : ℕ)
    (hL : ∀ j,width (length.read j) ≤ W) (hT : ∀ g,width (groups.read g).2 ≤ W)
    (hM : ∀ g,(groups.read g).1.length ≤ n) :
    (routesWithTraceAndWork length groups).2 ≤ m*n*(12000*(W+1)^3) := by
  have hMember : ∀ g : Fin m,
      ((groups.read g).1.map (fun j =>
        (applyWithWork .div (length.read j) (groups.read g).2).2)).sum ≤
        n*(12000*(W+1)^3) := by
    intro g
    have hPrice : ∀ j : Fin n,
        (applyWithWork .div (length.read j) (groups.read g).2).2 ≤
          12000*(W+1)^3 := fun j =>
      BinaryPRGPreparationWork.operation_uniform_bound .div _ _ W (hL j) (hT g)
    have hSum : ∀ items : List (Fin n),
        (items.map (fun j => (applyWithWork .div (length.read j) (groups.read g).2).2)).sum ≤
          items.length*(12000*(W+1)^3) := by
      intro items
      induction items with
      | nil => simp
      | cons j rest ih =>
          simp only [List.map_cons,List.sum_cons,List.length_cons]
          exact (Nat.add_le_add (hPrice j) ih).trans_eq (by ring)
    exact (hSum _).trans (Nat.mul_le_mul_right _ (hM g))
  rw [routesWithTraceAndWork_charge]
  calc
    _ ≤ ∑ _g : Fin m,n*(12000*(W+1)^3) := Finset.sum_le_sum (fun g _ => hMember g)
    _ = m*(n*(12000*(W+1)^3)) := by simp
    _ = _ := by ring

theorem routesWithTraceAndWork_prepared_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (routesWithTraceAndWork input.length (prepare input).packing).2 =
      routeArithmeticWork (prepare input) := by
  rw [routesWithTraceAndWork_charge]
  rfl

theorem routesWithTrace_erases {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) :
    (routesWithTrace length groups).1=BinaryGroupRoutes.prepare length groups := by
  unfold routesWithTrace BinaryGroupRoutes.prepare BinaryGroupRoutes.assignments
  rw [patchWithTrace_erases,groupsWithTrace_erases]


theorem groupsWithTrace_length {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (items : List (Fin m))
    (hM : ∀ g,(groups.read g).1.length ≤ n) : (groupsWithTrace length groups items).1.length ≤ items.length*n := by
  induction items with
  | nil => simp [groupsWithTrace]
  | cons g rest ih =>
      have hm := hM g
      simp only [groupsWithTrace,List.length_append,membersWithTrace_erases,List.length_map,List.length_cons]
      nlinarith only [hm,ih]

theorem routesWithTraceAndPatchWork_extra_bound {n m : ℕ}
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord))
    (hM : ∀ g,(groups.read g).1.length ≤ n) :
    (routesWithTraceAndPatchWork length groups).2 ≤
      (routesWithTraceAndWork length groups).2 + m*n*(n+1)+1 := by
  have hLen := groupsWithTrace_length length groups (List.finRange m) hM
  have hErase := congrArg Prod.fst
    (groupsWithTraceAndWork_erases length groups (List.finRange m))
  rw [← hErase] at hLen
  simp only [List.length_finRange] at hLen
  rw [routesWithTraceAndPatchWork_charge]
  have hPatch := Nat.mul_le_mul_right (n+1) hLen
  omega

def routeBound (n m W : ℕ) : ℕ :=
  m*(n*(2000000*(W+2)^4+10)+16)+8+
    (m*n)*(2*n*(6*W+7)+8)+8+m+8*(n+1)^2+8

theorem routesWithTrace_bound {n m : ℕ} (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n)×SignedWord)) (W : ℕ)
    (hL : ∀ j,width (length.read j) ≤ W) (hT : ∀ g,width (groups.read g).2 ≤ W)
    (hM : ∀ g,(groups.read g).1.length ≤ n) :
    listCells (routesWithTrace length groups).2+arraySlots (routesWithTrace length groups).2 ≤ routeBound n m W ∧
    framePeak (routesWithTrace length groups).2 ≤ n+2*m+m*n+10 := by
  let assignments := groupsWithTrace length groups (List.finRange m)
  let initial := FixedArrayTable.ofFn (fun _ : Fin n => (none,zero) : Fin n→BinaryGroupRoutes.Route m)
  have hGroups := groupsWithTrace_bounds length groups (List.finRange m) W hL hT hM
  have hLen := groupsWithTrace_length length groups (List.finRange m) hM
  simp only [List.length_finRange] at hGroups hLen
  have hInitial : ∀ j,routeWords (initial.read j) ≤ 6*W+7 := by
    intro j
    norm_num [initial,FixedArrayTable.read_ofFn,routeWords,BinaryRationalRegisterProgram.payloadWords,zero]
  have hEntries : ∀ entry∈assignments.1,routeWords entry.2 ≤ 6*W+7 := by
    intro entry he
    change entry∈(groupsWithTrace length groups (List.finRange m)).1 at he
    rw [groupsWithTrace_erases] at he
    obtain ⟨g,hg,he⟩ := List.mem_flatMap.mp he
    obtain ⟨j,hj,hEq⟩ := List.mem_map.mp he
    subst entry
    have hWidth : width (apply .div (length.read j) (groups.read g).2) ≤ 3*W+1 :=
      (BinaryPRGPreparationWork.apply_stored_width .div _ _).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le (hL j) (hT g))) 1)
    have hp := BinaryRationalRegisterProgram.payloadWords_bound _ (3*W+1) hWidth
    unfold routeWords
    dsimp only
    omega
  have hPatch := patchWithTrace_bound assignments.1 initial (6*W+7) hInitial hEntries
  have hPatchMono := Nat.mul_le_mul_right (2*n*(6*W+7)+8) hLen
  have hGroupsFrames := framePeak_under 2 assignments.2
  have hPatchFrames := framePeak_under 2 (patchWithTrace assignments.1 initial).2
  unfold routesWithTrace routeBound
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  dsimp only [assignments,initial] at hPatch hPatchMono hGroupsFrames hPatchFrames
  exact ⟨by nlinarith only [hGroups.1,hPatch.1,hPatchMono],by omega⟩

theorem routeBound_mono {n m a b W V : ℕ} (hn : n ≤ m) (ha : a ≤ b) (hW : W ≤ V) :
    routeBound n a W ≤ routeBound m b V := by
  unfold routeBound
  gcongr

-- Actual cached group totals have their native reached lattice width.
theorem reached_total_width {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state)
    (g : Fin (prepare (terminalInput request rich state)).count) :
    width ((prepare (terminalInput request rich state)).packing.read g).2 ≤ 1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator := by
  let input := terminalInput request rich state
  let cached := prepare input
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hTotal := Prepared.total_box cached hC hAd g
  have hLattice := Prepared.total_lattice cached hC _ (fun j => (resource_lattice_boxes request rich).1 j) g
  exact (Prepared.total_canonical cached hC g).2.trans
    (rationalWordWidth_lattice_bound request.source.normalizedInput.latticeDenominator_pos hLattice
      ⟨hTotal.1.le,hTotal.2.trans (budget_box request rich).2⟩)

theorem reached_routesWithTraceAndWork_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (routesWithTraceAndWork (terminalInput request rich state).length
      (prepare (terminalInput request rich state)).packing).2 ≤
      288000*n*(request.source.originalInputWordWidth+2)^3 := by
  let input := terminalInput request rich state
  let cached := prepare input
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hCount : cached.count ≤ 3 := by
    rcases cached.count_bound hC hAd with he | he <;> omega
  have hRoute := routesWithTraceAndWork_uniform_bound input.length cached.packing
    (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)
    (terminal_length_width request rich state)
    (reached_total_width request rich N bits state h)
    (Prepared.members_length cached hC hAd)
  have hd := request.source.normalized_lattice_wordWidth_original
  have hw : 1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator+1 ≤
      2*(request.source.originalInputWordWidth+2) := by omega
  calc
    _ ≤ cached.count*n*(12000*(1+2*binaryWordWidth
        request.source.normalizedInput.latticeDenominator+1)^3) := hRoute
    _ ≤ 3*n*(12000*(2*(request.source.originalInputWordWidth+2))^3) := by gcongr
    _ = 288000*n*(request.source.originalInputWordWidth+2)^3 := by ring

theorem reached_routesWithTraceAndPatchWork_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (routesWithTraceAndPatchWork (terminalInput request rich state).length
      (prepare (terminalInput request rich state)).packing).2 ≤
      288000*n*(request.source.originalInputWordWidth+2)^3 + 3*n*(n+1)+1 := by
  let input := terminalInput request rich state
  let cached := prepare input
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hCount : cached.count ≤ 3 := by
    rcases cached.count_bound hC hAd with he | he <;> omega
  have hExtra := routesWithTraceAndPatchWork_extra_bound input.length cached.packing
    (Prepared.members_length cached hC hAd)
  have hRoute := reached_routesWithTraceAndWork_bound request rich N bits state h
  have hMono := Nat.mul_le_mul_right (n*(n+1)) hCount
  dsimp only [input,cached] at hExtra hMono
  nlinarith only [hExtra,hRoute,hMono]

theorem reached_routesWithTraceAndListWork_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (routesWithTraceAndListWork (terminalInput request rich state).length
      (prepare (terminalInput request rich state)).packing).2 ≤
      288000*n*(request.source.originalInputWordWidth+2)^3 + 3*n*(n+1)+7*n+12 := by
  let input := terminalInput request rich state
  let cached := prepare input
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hCount : cached.count ≤ 3 := by
    rcases cached.count_bound hC hAd with he | he <;> omega
  have hExtra := routesWithTraceAndListWork_extra_bound input.length cached.packing
    (Prepared.members_length cached hC hAd)
  have hRoute := reached_routesWithTraceAndPatchWork_bound request rich N bits state h
  have hMono := Nat.mul_le_mul_right (2*n+3) hCount
  dsimp only [input,cached] at hExtra hMono
  nlinarith only [hExtra,hRoute,hMono]

noncomputable def reachedRouteBound {n : ℕ} (request : BinaryPRGRequest.Request n) : ℕ :=
  routeBound n 3 (3+2*request.source.originalInputWordWidth)

theorem reached_routes_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    listCells (routesWithTrace (terminalInput request rich state).length (prepare (terminalInput request rich state)).packing).2+
      arraySlots (routesWithTrace (terminalInput request rich state).length (prepare (terminalInput request rich state)).packing).2 ≤ reachedRouteBound request ∧
    framePeak (routesWithTrace (terminalInput request rich state).length (prepare (terminalInput request rich state)).packing).2 ≤ 4*n+16 := by
  let input := terminalInput request rich state
  let cached := prepare input
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hm : cached.count ≤ 3 := by rcases cached.count_bound hC hAd with he|he <;> omega
  have hb := routesWithTrace_bound input.length cached.packing
    (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)
    (terminal_length_width request rich state) (reached_total_width request rich N bits state h)
    (Prepared.members_length cached hC hAd)
  have hd := request.source.normalized_lattice_wordWidth_original
  refine ⟨hb.1.trans (routeBound_mono le_rfl hm (by omega)),?_⟩
  have hp := Nat.mul_le_mul_right n hm
  dsimp only [input,cached] at hb hm hp
  omega

theorem reached_routes_all_prefix {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells
      (routesWithTrace (terminalInput request rich state).length (prepare (terminalInput request rich state)).packing).2 steps ≤
      borrowedCells+reachedRouteBound request := by
  have hb := (reached_routes_bound request rich N bits state h).1
  have hl := listCells_take_le
    (routesWithTrace (terminalInput request rich state).length (prepare (terminalInput request rich state)).packing).2 steps
  have ha := arraySlots_take_le
    (routesWithTrace (terminalInput request rich state).length (prepare (terminalInput request rich state)).packing).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryTerminalRouteLifetime

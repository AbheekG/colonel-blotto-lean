import Blotto.BinaryInitialTraceSparsity
import Blotto.BinaryTerminalPhysicalRouteLifetime

/-! Structural event counts for the actual physical cache. Positive allocation
headers pay for local events and recursive terminal slack. Existing accepted
storage bounds then price wrapper emission without a free cache-trace length.
No structural certificate is evaluated by a selected runtime producer. -/
namespace Blotto.BinaryCacheTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryInitialTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryTerminalPhysicalRouteLifetime
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem classification_sparse {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) :
    Sparse (BinaryTerminalPrefixLifetime.classificationWithTrace input items).2 := by
  induction items with
  | nil => simp [BinaryTerminalPrefixLifetime.classificationWithTrace,Sparse,cells,listCells,arraySlots]
  | cons j rest ih =>
      exact prefix_one _ _ 1 (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega) ih

theorem packing_loop_sparse {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    Sparse (BinaryTerminalPrefixLifetime.packAuxWithTrace length budget current total rest).2 := by
  induction rest generalizing current total with
  | nil => simp [BinaryTerminalPrefixLifetime.packAuxWithTrace,Sparse,cells,listCells,arraySlots]
  | cons item rest ih =>
      unfold BinaryTerminalPrefixLifetime.packAuxWithTrace
      dsimp only
      split
      · exact prefix_one _ _ 1 (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega) (ih _ _)
      · exact prefix_one _ _ 1 (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega) (ih _ _)

theorem packing_sparse {α : Type*} (length : α → SignedWord) (budget : SignedWord) (items : List α) :
    Sparse (BinaryTerminalPrefixLifetime.packingWithTrace length budget items).2 := by
  cases items with
  | nil => simp [BinaryTerminalPrefixLifetime.packingWithTrace,Sparse,cells,listCells,arraySlots]
  | cons item rest =>
      exact prefix_one _ _ 1
        (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
        (packing_loop_sparse length budget [item] (length item) rest)

theorem prefix_sparse {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    Sparse (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.2 := by
  simp only [BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork,
    BinaryTerminalPrefixLifetime.classificationWithTraceAndWork_erases,
    BinaryTerminalPrefixLifetime.packingWithTraceAndWork_erases]
  exact prefix_two _ _ _ 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (classification_sparse input (List.finRange n))
    (packing_sparse input.length.read input.budget _)

theorem replicate_sparse (n : ℕ) (bit : Bool) :
    Sparse (BinaryPRGOutputLifetime.replicateWithTrace n bit).2 := by
  induction n with
  | zero => simp [BinaryPRGOutputLifetime.replicateWithTrace,Sparse,cells,listCells,arraySlots]
  | succ n ih =>
      exact prefix_one _ _ 1
        (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega) ih

theorem address_count_sparse {α : Type*} (items : List α) (counter : List Bool) :
    Sparse (countAddressWithTraceAndWork items counter).1.2 := by
  induction items generalizing counter with
  | nil => simp [countAddressWithTraceAndWork,Sparse,cells,listCells,arraySlots]
  | cons item rest ih =>
      exact prefix_two _ _ _ 2 1
        (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
        (carry_sparse counter) (ih _)

theorem address_sparse {n : ℕ} (j : Fin n) : Sparse (addressWithTraceAndWork j).1.2 := by
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨replicate_sparse j.val false,address_count_sparse _ []⟩
  · simp only [List.length_cons,List.length_nil]; omega

theorem read_length_sparse {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) :
    Sparse (readLengthWithTraceAndWork store j).1.2 := by
  apply wrap_sparse
  · simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨address_sparse j,object_get_sparse store _⟩
  · simp only [List.length_cons,List.length_nil]; omega

theorem members_sparse {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (total : SignedWord) (g : Fin m) (items : List (Fin n)) :
    Sparse (membersWithTraceAndWork store total g items).1.2 := by
  induction items with
  | nil => simp [membersWithTraceAndWork,Sparse,cells,listCells,arraySlots]
  | cons j rest ih =>
      exact prefix_two _ _ _ 1 1
        (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
        (read_length_sparse store j) ih

theorem groups_sparse {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) :
    Sparse (groupsWithTraceAndWork store groups items).1.2 := by
  induction items with
  | nil => simp [groupsWithTraceAndWork,Sparse,cells,listCells,arraySlots]
  | cons g rest ih =>
      exact prefix_two _ _ _ 2 2
        (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
        (members_sparse store (groups.read g).2 g (groups.read g).1) ih

theorem patch_sparse {n m : ℕ} (entries : List (Fin n × BinaryGroupRoutes.Route m))
    (table : FixedArrayTable n (BinaryGroupRoutes.Route m)) :
    Sparse (BinaryTerminalRouteLifetime.patchWithTraceAndWork entries table).1.2 := by
  induction entries generalizing table with
  | nil => simp [BinaryTerminalRouteLifetime.patchWithTraceAndWork,Sparse,cells,listCells,arraySlots]
  | cons entry rest ih =>
      exact prefix_one _ _ 1
        (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega) (ih _)

theorem build_empty_sparse {α : Type*} (n : ℕ) (produce : Fin n → α) :
    Sparse (BinaryLifetimeArray.build n (fun j => (produce j,[]))).2 := by
  rw [BinaryLifetimeArray.build_reference]
  have h : BinaryLifetimeArray.children n (fun _ => []) = [] := by
    simp [BinaryLifetimeArray.children]
  simp [BinaryLifetimeArray.buildReference,h,Sparse,cells,listCells,arraySlots,under]
  omega

theorem initial_routes_sparse (n m : ℕ) : Sparse (initialRoutesWithTrace n m).2 :=
  build_empty_sparse n (fun _ : Fin n => ((none,⟨false,[],[true]⟩) : BinaryGroupRoutes.Route m))

theorem routes_sparse {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    Sparse (routesWithTraceAndWork store groups).1.2 := by
  exact prefix_three _ _ _ _ 2 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (initial_routes_sparse n m) (groups_sparse store groups (List.finRange m)) (patch_sparse _ _)

theorem totals_sparse {n m : ℕ} (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    Sparse (totalsWithTrace packing).2 := build_empty_sparse m (fun g => (packing.read g).2)

theorem pivot_sparse {n : ℕ} (input : BinaryTerminalGrouping.Input n) (pivot : Option (Fin n)) :
    Sparse (BinaryTerminalCacheLifetime.pivotWithTraceAndWork input pivot).1.2 := by
  cases pivot <;> simp [BinaryTerminalCacheLifetime.pivotWithTraceAndWork,Sparse,cells,listCells,arraySlots]

theorem middle_three (front header first second third : Trace) (a b c : ℕ)
    (hHeader : header.length+3 ≤ 2*cells header)
    (hFront : Sparse front) (hFirst : Sparse first) (hSecond : Sparse second) (hThird : Sparse third) :
    Sparse (front++header++under a first++under b second++under c third) := by
  unfold Sparse at hFront hFirst hSecond hThird ⊢
  simp only [List.length_append,BinaryResourceTraceLength.under_length,
    BinaryPRGHeapPrimitiveLifetime.cells_append,BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem cache_sparse {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    Sparse (cacheWithTraceAndWork input store).1.2 := by
  exact middle_three _ _ _ _ _ 2 2 2
    (by simp only [cells,listCells,arraySlots,List.length_cons,List.length_nil]; omega)
    (prefix_sparse input) (totals_sparse _) (routes_sparse store _) (pivot_sparse input _)

theorem cache_length_usage {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    (cacheWithTraceAndWork input store).1.2.length ≤ 2*usage (cacheWithTraceAndWork input store).1.2+1 :=
  sparse_length_usage _ (cache_sparse input store)

theorem accepted_reached_cache_length (frame : List Bool)
    (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.logical.request rich).1.1 = some state) :
    let input := BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state
    (cacheWithTraceAndWork input parsed.1.2.physical.lengthStore).1.2.length ≤
      (2^62+1)*(frame.length+3)^8 := by
  have h := cache_length_usage (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state)
    parsed.1.2.physical.lengthStore
  have hu := accepted_reached_cache_polynomial_usage frame parsed hParsed rich seed state hState
  have hOne := Nat.one_le_pow 8 (frame.length+3) (by omega)
  dsimp only [cacheWithTrace] at hu
  dsimp only
  nlinarith only [h,hu,hOne]

end Blotto.BinaryCacheTraceSparsity

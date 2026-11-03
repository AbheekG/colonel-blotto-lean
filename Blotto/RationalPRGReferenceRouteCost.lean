import Blotto.ReferenceTablePatchCost
import Blotto.RationalRouteArrayCopyWork
import Blotto.RationalPRGSharpArithmeticLedger
import Blotto.SharedTerminalWindowWork

/-! The cached route table is constructed from references to its actual
coefficient objects. The returned table is exactly the previous raw-list
router, while even whole-array reference copies fit the paper's soft bound.
Coefficient arithmetic and packing are charged in their existing ledgers. -/

namespace Blotto.RationalPRGReferenceRouteCost
set_option autoImplicit false

def initial {α : Type*} (n : ℕ) (value : α) : FixedArrayTable n α :=
  ⟨ReferenceArrayBuilder.array (List.replicate n value), by
    rw [ReferenceArrayBuilder.array_data,List.size_toArray,List.length_replicate]⟩

theorem initial_eq {α : Type*} (n : ℕ) (value : α) :
    initial n value = FixedArrayTable.ofFn (fun _ : Fin n => value) := by
  unfold initial FixedArrayTable.ofFn
  congr 1
  rw [ReferenceArrayBuilder.array_data]
  apply Array.ext <;> simp

def repeatWork (primitive : ℕ → ℕ) (A n : ℕ) : ℕ :=
  n*(2*A+2*primitive (binaryWordWidth (n+1))+4)+1

def run {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (A : ℕ) : FixedArrayTable n (GroupRoute i.groups.length) × ℕ :=
  let value : GroupRoute i.groups.length := (none,0)
  let values := List.replicate n value
  let returned := ReferenceTablePatchCost.run primitive A (initial n value) p.routeAssignments
  (returned.1,repeatWork primitive A n+ReferenceArrayBuilder.work primitive A values 0+
    returned.2+2*A+6)

theorem run_data {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (A : ℕ) : (run p primitive A).1 = p.prepareOutput.table := by
  unfold run
  dsimp only
  rw [ReferenceTablePatchCost.run_data,initial_eq]
  rfl

def prepared {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (A : ℕ) : PreparedGroupOutput i.partition :=
  ⟨(run p primitive A).1,by intro j; rw [run_data]; exact p.prepareOutput.correct j⟩

theorem prepared_table {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (A : ℕ) : (prepared p primitive A).table = p.prepareOutput.table :=
  run_data p primitive A

def payloads {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    List (GroupRoute i.groups.length) := (none,0)::p.routeAssignments.map Prod.snd

theorem payloads_length {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    (payloads p).length ≤ n+1 := by
  have h := p.routeAssignments_length_le
  simp only [payloads,List.length_cons,List.length_map]
  omega

theorem run_values_mem {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (A : ℕ) (j : Fin n) : (run p primitive A).1.read j ∈ (payloads p) := by
  apply ReferenceTablePatchCost.run_values_mem
  · intro k
    rw [initial_eq,FixedArrayTable.read_ofFn]
    exact List.mem_cons_self
  · intro entry hEntry
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry,hEntry,rfl⟩)

theorem payload_width {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth D ≤ s) :
    ∀ value ∈ (payloads p), routePayloadWordWidth value ≤ RationalTerminalPacking.routePayloadWidth n s := by
  intro value hValue
  rcases List.mem_cons.mp hValue with he | hRest
  · subst value
    have hz := rationalWordWidth_of_height ((show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs)
    change 1+0+rationalWordWidth (0 : ℚ) ≤
      1+binaryWordWidth (n+4)+(1+2*s)
    omega
  · obtain ⟨entry,hEntry,rfl⟩ := List.mem_map.mp hRest
    exact p.assignmentPayloadWidth_bound D s h hD hB hWidth entry hEntry

theorem run_work_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (A : ℕ) :
    (run p primitive A).2 ≤ (3*n+1)*ReferenceTablePatchCost.writeBound c A n+3 := by
  have hPush := ReferenceArrayBuilder.work_bound primitive c hPrimitive A n
    (List.replicate n ((none,0):GroupRoute i.groups.length)) 0 (by simp)
  simp only [List.length_replicate] at hPush
  have hPatch := ReferenceTablePatchCost.run_work_bound primitive c hPrimitive A
    (initial n ((none,0):GroupRoute i.groups.length)) p.routeAssignments
  have hCount := p.routeAssignments_length_le
  have hP := Nat.mul_le_mul_right (ReferenceTablePatchCost.writeBound c A n) hCount
  have hScalar := hPrimitive (binaryWordWidth (n+1))
  have hRepeat := Nat.mul_le_mul_left (2*n) hScalar
  unfold run repeatWork
  dsimp only
  unfold ReferenceTablePatchCost.writeBound at *
  nlinarith only [hPush,hPatch,hP,hRepeat]

def addressWidth (n s : ℕ) : ℕ :=
  StoredArrayReferenceList.poolAddressWidth (n+1) (RationalTerminalPacking.routePayloadWidth n s)

def bound (c n s : ℕ) : ℕ := (32*c+112)*(n+1)^2*(addressWidth n s+1)+3

theorem pool_run_work_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (s : ℕ) :
    (run p primitive (addressWidth n s)).2 ≤ bound c n s := by
  have h := run_work_bound p primitive c hPrimitive (addressWidth n s)
  have hIndex : binaryWordWidth (n+1) ≤ addressWidth n s :=
    (binaryWordWidth_mono (Nat.le_succ _)).trans
      (ReferenceTablePatchCost.index_width_le_pool (n+1) (RationalTerminalPacking.routePayloadWidth n s))
  have hw := ReferenceTablePatchCost.write_bound_of_index_width c n (addressWidth n s) hIndex
  have hm := Nat.mul_le_mul_left (3*n+1) hw
  unfold bound
  change _ ≤ (32*c+112)*(n+1)^2*(addressWidth n s+1)+3
  calc
    _ ≤ (3*n+1)*((8*c+28)*(n+1)*(addressWidth n s+1))+3 := by omega
    _ ≤ _ := by ring_nf; omega

theorem terminal_contract {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth D ≤ s) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) :
    (run p primitive (addressWidth n s)).1 = p.prepareOutput.table ∧
      (payloads p).length ≤ n+1 ∧
      (∀ value ∈ payloads p, routePayloadWordWidth value ≤ RationalTerminalPacking.routePayloadWidth n s) ∧
      (run p primitive (addressWidth n s)).2 ≤ bound c n s :=
  ⟨run_data p primitive _,payloads_length p,payload_width p D s h hD hB hs hWidth,
    pool_run_work_bound p primitive c hPrimitive s⟩

theorem address_log_bound (n s : ℕ) :
    addressWidth n s ≤ binaryWordWidth (n+2)+
      binaryWordWidth (RationalTerminalPacking.routePayloadWidth n s+1) :=
  StoredArrayReferenceList.poolAddressWidth_log_bound (n+1) _

theorem original_input_bound {n : ℕ} (input : RationalPRGOriginalInput n) (c : ℕ) :
    bound c n (3+input.originalInputWordWidth) ≤
      (32*c+112)*(n+1)*(input.originalInputWordWidth+1)*
        (binaryWordWidth (n+2)+binaryWordWidth
          (RationalTerminalPacking.routePayloadWidth n (3+input.originalInputWordWidth)+1)+1)+3 := by
  have hn := RationalPRGLinearFramingWork.count_le_inputWidth input
  have hN := Nat.mul_le_mul_left (n+1) (Nat.add_le_add_right hn 1)
  have hA := Nat.add_le_add_right (address_log_bound n (3+input.originalInputWordWidth)) 1
  unfold bound
  simpa only [pow_two,Nat.mul_assoc] using Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.mul_le_mul_left (32*c+112) hN) hA) 3

end Blotto.RationalPRGReferenceRouteCost

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedRouteReferenceWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (s R : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits (fun value _ _ =>
    (RationalPRGReferenceRouteCost.run (RationalTerminalPacking.prepare (i.terminalData value))
      primitive (RationalPRGReferenceRouteCost.addressWidth n s)).2)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedRouteReferenceWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (s R : ℕ) (bits : Fin R → Bool) :
    i.sharedRouteReferenceWork primitive s R bits ≤ RationalPRGReferenceRouteCost.bound c n s := by
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hw := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value _ _ => (RationalPRGReferenceRouteCost.run
      (RationalTerminalPacking.prepare (i.terminalData value)) primitive
      (RationalPRGReferenceRouteCost.addressWidth n s)).2)
    (RationalPRGReferenceRouteCost.bound c n s) 0
    (fun value _ _ _ => by
      simpa only [Nat.zero_mul,Nat.add_zero] using
        (RationalPRGReferenceRouteCost.pool_run_work_bound
          (RationalTerminalPacking.prepare (i.terminalData value)) primitive c hPrimitive s))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  simpa only [sharedRouteReferenceWork,Nat.zero_mul,Nat.add_zero] using hw

noncomputable def paperRouteReferenceWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (primitive : ℕ → ℕ) (s K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  i.sharedRouteReferenceWork primitive s (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))

end Blotto.RationalLottoResourceSystem

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedRouteReferenceWork {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.paperRouteReferenceWork primitive (3+i.originalInputWordWidth) K bits
  else i.normalizedInput.poorNativeSystem.paperRouteReferenceWork primitive (3+i.originalInputWordWidth) K bits

theorem selectedRouteReferenceWork_bound {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedRouteReferenceWork primitive rich K bits ≤
      RationalPRGReferenceRouteCost.bound c n (3+i.originalInputWordWidth) := by
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.sharedRouteReferenceWork_bound
      primitive c hPrimitive (3+i.originalInputWordWidth) _ _
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.sharedRouteReferenceWork_bound
      primitive c hPrimitive (3+i.originalInputWordWidth) _ _

theorem selectedRouteReferenceWork_fast {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedRouteReferenceWork primitive rich K bits ≤
      (32*c+112)*(n+1)*(i.originalInputWordWidth+1)*
        (binaryWordWidth (n+2)+binaryWordWidth
          (RationalTerminalPacking.routePayloadWidth n (3+i.originalInputWordWidth)+1)+1)+3 :=
  (i.selectedRouteReferenceWork_bound primitive c hPrimitive rich K bits).trans
    (RationalPRGReferenceRouteCost.original_input_bound i c)

end Blotto.RationalPRGOriginalInput

import Blotto.BinaryTerminalRouteLifetime
import Blotto.BinaryTerminalCacheLifetime
import Blotto.BinaryPRGHeapCachedPrefixLifetime
import Blotto.BinaryPRGHeapCallerLifetimePolynomial
import Blotto.BinaryPRGHeapSeededPrefixLifetime
import Blotto.BinaryPRGPhysicalRawRequestLifetime
import Blotto.BinaryPRGPhysicalResourceRawBound
import Blotto.BinaryAddressFormation
import Blotto.BinaryPhysicalHeapRequestLifetime
import Blotto.BinaryWordStoreLifetime
import Blotto.BinaryPRGOutputLifetime
import Blotto.BinaryLifetimeArray

/-! A route builder reads each member length from the retained physical word
object store before dividing it by the group's total. The fallback on an
invalid read makes the program total; the accepted-frame theorem proves that
the fallback is unreachable. A Boolean carry loop materializes each member
address from its native index, with the ruler's recursive cons/control trace
and carry lifetimes charged. Native member-index production and group packing
remain separate from this address conversion. The zero route table uses a
traced array builder. -/
set_option autoImplicit false
namespace Blotto.BinaryTerminalPhysicalRouteLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryRationalOpcode BinaryPRGHeapTraceUsage BinaryTerminalRouteLifetime

def countAddressWithTraceAndWork {α : Type*} :
    List α → List Bool → (List Bool × Trace) × ℕ
  | [], counter => ((counter,[.frames 1,.arrayAllocation 4]),1)
  | _ :: rest, counter =>
      let advanced := BinaryWordStoreLifetime.carryWithTrace counter
      let later := countAddressWithTraceAndWork rest advanced.1
      ((later.1.1,[.frames 2,.arrayAllocation 4] ++
          under 2 advanced.2 ++ under 1 later.1.2),
        4*BinaryCarryCounter.carryCells counter+
          4*(counter.length+1)+later.2+4)

theorem countAddress_trace {α : Type*} (items : List α) (counter : List Bool) :
    (countAddressWithTraceAndWork items counter).1 =
      BinaryWordStoreLifetime.countWithTrace items counter := by
  induction items generalizing counter with
  | nil => rfl
  | cons item rest ih =>
      simp only [countAddressWithTraceAndWork,
        BinaryWordStoreLifetime.countWithTrace,ih]

theorem countAddress_work {α : Type*} (items : List α) (counter : List Bool) :
    (countAddressWithTraceAndWork items counter).2 =
      (BinaryPRGWordStoreHeapMachine.countWithWork items counter).2.work := by
  induction items generalizing counter with
  | nil => rfl
  | cons item rest ih =>
      simp only [countAddressWithTraceAndWork,
        BinaryPRGWordStoreHeapMachine.countWithWork,
        BinaryWordStoreLifetime.carryWithTrace_erases,ih]

def addressWithTraceAndWork {n : ℕ} (j : Fin n) : (List Bool × Trace) × ℕ :=
  let ruler := BinaryPRGOutputLifetime.replicateWithTrace j.val false
  let counted := countAddressWithTraceAndWork ruler.1 []
  ((counted.1.1,wrap 8 1 [ruler.2,counted.1.2]),
    (j.val+1)*(binaryWordWidth n+4)+counted.2)

def addressWithTrace {n : ℕ} (j : Fin n) : List Bool × Trace :=
  (addressWithTraceAndWork j).1

theorem address_measured_word {n : ℕ} (j : Fin n) :
    (addressWithTraceAndWork j).1.1 =
      (BinaryPRGWordStoreHeapMachine.countWithWork
        (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1 []).1 := by
  simp only [addressWithTraceAndWork,
    countAddress_trace,BinaryWordStoreLifetime.countWithTrace_erases,
    BinaryPRGWordStoreHeapMachine.countWithWork_erasure]

theorem address_work_bound {n : ℕ} (j : Fin n) :
    (addressWithTraceAndWork j).2 ≤
      n*(binaryWordWidth n+4)+12*(n+1)^2 := by
  have hCount := (BinaryPRGWordStoreHeapMachine.countWithWork_bounds
    (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1
    ([] : List Bool)).1
  have hLength : (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1.length = j.val := by
    simp [BinaryPRGOutputLifetime.replicateWithTrace_state]
  rw [hLength] at hCount
  have hj : j.val+1 ≤ n := by omega
  have hMul := Nat.mul_le_mul_right (binaryWordWidth n+4) hj
  have hSquare := Nat.mul_le_mul hj hj
  unfold BinaryPRGWordStoreHeapMachine.countBound at hCount
  simp only [List.length_nil,Nat.zero_add] at hCount
  change (j.val+1)*(binaryWordWidth n+4)+
    (countAddressWithTraceAndWork
      (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1 []).2 ≤ _
  rw [countAddress_work]
  nlinarith only [hCount,hMul,hSquare]

def address {n : ℕ} (j : Fin n) : List Bool := (addressWithTrace j).1

theorem address_value {n : ℕ} (j : Fin n) :
    BinaryBigEndian.littleValue (address j) = j.val := by
  change BinaryBigEndian.littleValue
    (countAddressWithTraceAndWork
      (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1 []).1.1 = j.val
  rw [countAddress_trace,BinaryWordStoreLifetime.countWithTrace_erases,
    BinaryPRGOutputLifetime.replicateWithTrace_state]
  change BinaryCarryCounter.value (BinaryCarryCounter.count (List.replicate j.val false) []) = j.val
  rw [BinaryCarryCounter.count_value]
  simp [BinaryCarryCounter.value,BinaryBigEndian.littleValue]

theorem address_length {n : ℕ} (j : Fin n) :
    (address j).length ≤ binaryWordWidth n := by
  have h := BinaryCarryCounter.canonical_length_bound
    (BinaryCarryCounter.count
      (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1 [])
    (BinaryCarryCounter.count_canonical _ [] trivial)
  rw [BinaryCarryCounter.count_value] at h
  simp [BinaryCarryCounter.value,BinaryBigEndian.littleValue,
    BinaryPRGOutputLifetime.replicateWithTrace_state] at h
  change (countAddressWithTraceAndWork
    (BinaryPRGOutputLifetime.replicateWithTrace j.val false).1 []).1.1.length ≤ binaryWordWidth n
  rw [countAddress_trace,BinaryWordStoreLifetime.countWithTrace_erases]
  rw [BinaryPRGOutputLifetime.replicateWithTrace_state]
  exact h.trans (binaryWordWidth_mono j.isLt.le)

theorem address_usage {n : ℕ} (j : Fin n) :
    usage (addressWithTrace j).2 ≤ 32*(j.val+1) := by
  let ruler := BinaryPRGOutputLifetime.replicateWithTrace j.val false
  have hRulerCells := BinaryPRGOutputLifetime.replicateWithTrace_cells j.val false
  have hRulerArrays := BinaryPRGOutputLifetime.replicateWithTrace_arrays j.val false
  have hRulerFrames := BinaryPRGOutputLifetime.replicateWithTrace_frames j.val false
  have hRulerUsage : usage ruler.2 ≤ 2*j.val+1 := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    dsimp only [ruler]
    omega
  have hCount := BinaryWordStoreLifetime.countWithTrace_bounds
    ruler.1 ([] : List Bool)
  have hCarry := BinaryCarryCounter.countCarryCells_bound
    ruler.1 ([] : List Bool)
  have hRulerLength : ruler.1.length = j.val := by
    simp [ruler,BinaryPRGOutputLifetime.replicateWithTrace_state]
  have hCountUsage : usage (BinaryWordStoreLifetime.countWithTrace
      ruler.1 ([] : List Bool)).2 ≤ 16*(j.val+1) := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    simp only [hRulerLength,List.length_nil,BinaryCarryCounter.ones] at *
    omega
  have hWrap := wrap_usage 8 1
    [ruler.2,(BinaryWordStoreLifetime.countWithTrace ruler.1 []).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change usage (wrap 8 1 [ruler.2,
    (countAddressWithTraceAndWork ruler.1 []).1.2]) ≤ _
  rw [countAddress_trace]
  omega

def readLengthWithTraceAndWork {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (j : Fin n) :
    (Option SignedWord × Trace) × ℕ :=
  let encoded := addressWithTraceAndWork j
  let fetched := BinaryWordObjectArrayAccess.getWithTrace store encoded.1.1
  ((fetched.1,wrap 8 1 [encoded.1.2,fetched.2]),
    encoded.2+(BinaryWordObjectArray.getWithWork store encoded.1.1).2+4)

def readLength {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) :
    Option SignedWord × Trace :=
  (readLengthWithTraceAndWork store j).1

theorem readLength_measured_state {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (j : Fin n) :
    (readLengthWithTraceAndWork store j).1.1 =
      (BinaryWordObjectArray.getWithWork store (address j)).1 := by
  unfold readLengthWithTraceAndWork
  dsimp only
  exact BinaryWordObjectArrayAccess.get_state store (address j)

theorem readLength_work_bound {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (j : Fin n) :
    (readLengthWithTraceAndWork store j).2 ≤
      n*(binaryWordWidth n+4)+12*(n+1)^2+
        BinaryWordObjectArray.readBound store (binaryWordWidth n)+4 := by
  have hAddress := address_work_bound j
  have hRead := BinaryWordObjectArray.getWithWork_bound store (address j)
  have hWidth := address_length j
  have hMono : BinaryWordObjectArray.readBound store (address j).length ≤
      BinaryWordObjectArray.readBound store (binaryWordWidth n) := by
    unfold BinaryWordObjectArray.readBound BinaryReferenceVector.readBound
    gcongr
  unfold readLengthWithTraceAndWork
  dsimp only
  change (addressWithTraceAndWork j).2 +
    (BinaryWordObjectArray.getWithWork store (address j)).2 + 4 ≤ _
  omega

theorem readLength_usage {n : ℕ} (store : BinaryWordObjectArray.Store n) (j : Fin n) :
    usage (readLength store j).2 ≤
      BinaryWordObjectArrayAccess.envelope store (binaryWordWidth n)+32*n+32 := by
  have hAddress := address_usage j
  have hFetched := BinaryWordObjectArrayAccess.get_usage store (address j)
  have hWidth := address_length j
  have hMono : BinaryWordObjectArrayAccess.envelope store (address j).length ≤
      BinaryWordObjectArrayAccess.envelope store (binaryWordWidth n) := by
    unfold BinaryWordObjectArrayAccess.envelope BinaryReferenceVector.readBound
    gcongr
  have hWrap := wrap_usage 8 1
    [(addressWithTrace j).2,
      (BinaryWordObjectArrayAccess.getWithTrace store (address j)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change usage (wrap 8 1 [(addressWithTrace j).2,
    (BinaryWordObjectArrayAccess.getWithTrace store (address j)).2]) ≤ _
  omega

def membersWithTraceAndWork {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (total : SignedWord) (g : Fin m) :
    List (Fin n) → (List (Fin n × BinaryGroupRoutes.Route m) × Trace) × ℕ
  | [] => (([],[.frames 1,.arrayAllocation 8]),1)
  | j :: rest =>
      let fetched := readLengthWithTraceAndWork store j
      let word := fetched.1.1.getD zero
      let divided := BinaryRationalOpcodeAllocation.applyWithAllocation .div word total
      let later := membersWithTraceAndWork store total g rest
      (((j,(some g,divided.1)) :: later.1.1,
        [.frames 1,.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div word total)] ++
          under 1 fetched.1.2 ++ under 1 later.1.2),
        fetched.2+(applyWithWork .div word total).2+later.2+1)

def membersWithTrace {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (total : SignedWord) (g : Fin m) (items : List (Fin n)) :
    List (Fin n × BinaryGroupRoutes.Route m) × Trace :=
  (membersWithTraceAndWork store total g items).1

theorem members_erases {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord) (total : SignedWord) (g : Fin m)
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (items : List (Fin n)) :
    (membersWithTrace store total g items).1 =
      (BinaryTerminalRouteLifetime.membersWithTrace length total g items).1 := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      have hMeasured : (readLengthWithTraceAndWork store j).1.1 =
          some (length.read j) := hRead j
      change (membersWithTraceAndWork store total g rest).1.1 =
        (BinaryTerminalRouteLifetime.membersWithTrace length total g rest).1 at ih
      simp only [membersWithTrace,membersWithTraceAndWork,
        BinaryTerminalRouteLifetime.membersWithTrace,ih]
      rw [hMeasured]
      rfl

theorem members_usage {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord) (total : SignedWord) (g : Fin m)
    (items : List (Fin n)) (W : ℕ)
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (hL : ∀ j, width (length.read j) ≤ W) (hT : width total ≤ W) :
    usage (membersWithTrace store total g items).2 ≤
      items.length * (2000000*(W+2)^4 +
        BinaryWordObjectArrayAccess.envelope store (binaryWordWidth n)+32*n+44) + 9 := by
  induction items with
  | nil => simp [membersWithTrace,membersWithTraceAndWork,usage,BinaryPRGHeapPrimitiveLifetime.cells,
      listCells,arraySlots,framePeak]
  | cons j rest ih =>
      have hWord : (readLengthWithTraceAndWork store j).1.1.getD zero = length.read j := by
        rw [show (readLengthWithTraceAndWork store j).1.1 =
          some (length.read j) from hRead j]
        rfl
      have hOpcode := (BinaryRationalOpcodeAllocation.opcodeStorage_bound
        .div (length.read j) total).trans
        (Nat.mul_le_mul_left 2000000
          (Nat.pow_le_pow_left (Nat.add_le_add_right
            (max_le (hL j) hT) 2) 4))
      have hFetched := readLength_usage store j
      change usage (readLengthWithTraceAndWork store j).1.2 ≤ _ at hFetched
      have hHead : usage [.frames 1,.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage
            .div (length.read j) total)] =
          BinaryRationalOpcodeAllocation.opcodeStorage .div (length.read j) total + 10 := by
        simp [usage,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,framePeak]
        omega
      have hAppend1 := usage_append
        ([.frames 1,.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage
            .div (length.read j) total)])
        (under 1 (readLengthWithTraceAndWork store j).1.2 ++
          under 1 (membersWithTrace store total g rest).2)
      have hAppend2 := usage_append (under 1 (readLengthWithTraceAndWork store j).1.2)
        (under 1 (membersWithTrace store total g rest).2)
      have hUnder1 := usage_under 1 (readLengthWithTraceAndWork store j).1.2
      have hUnder2 := usage_under 1 (membersWithTrace store total g rest).2
      simp only [membersWithTrace,membersWithTraceAndWork,
        List.length_cons,List.append_assoc] at *
      rw [hWord] at *
      rw [Nat.add_mul,one_mul]
      omega

def memberWorkEnvelope {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (W : ℕ) : ℕ :=
  n*(binaryWordWidth n+4)+12*(n+1)^2+
    BinaryWordObjectArray.readBound store (binaryWordWidth n)+
    12000*(W+1)^3+5

theorem members_work_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord) (total : SignedWord) (g : Fin m)
    (items : List (Fin n)) (W : ℕ)
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (hL : ∀ j, width (length.read j) ≤ W) (hT : width total ≤ W) :
    (membersWithTraceAndWork store total g items).2 ≤
      items.length * memberWorkEnvelope store W + 1 := by
  induction items with
  | nil => simp [membersWithTraceAndWork]
  | cons j rest ih =>
      have hWord : (readLengthWithTraceAndWork store j).1.1.getD zero =
          length.read j := by
        rw [show (readLengthWithTraceAndWork store j).1.1 =
          some (length.read j) from hRead j]
        rfl
      have hFetched := readLength_work_bound store j
      have hPair : BinaryRationalArithmetic.pairWidth (length.read j) total ≤ W :=
        max_le (hL j) hT
      have hOpcode := (BinaryRationalOpcode.applyWithWork_bound
        .div (length.read j) total).trans
        (Nat.mul_le_mul_left 12000
          (Nat.pow_le_pow_left (Nat.add_le_add_right hPair 1) 3))
      change (readLengthWithTraceAndWork store j).2 +
        (applyWithWork .div
          ((readLengthWithTraceAndWork store j).1.1.getD zero) total).2 +
        (membersWithTraceAndWork store total g rest).2 + 1 ≤ _
      rw [hWord]
      simp only [List.length_cons]
      rw [Nat.add_mul,one_mul]
      unfold memberWorkEnvelope at *
      omega

def groupsWithTraceAndWork {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    List (Fin m) → (List (Fin n × BinaryGroupRoutes.Route m) × Trace) × ℕ
  | [] => (([],[.frames 1,.arrayAllocation 8]),1)
  | g :: rest =>
      let memberResult := membersWithTraceAndWork store (groups.read g).2 g (groups.read g).1
      let later := groupsWithTraceAndWork store groups rest
      ((memberResult.1.1 ++ later.1.1,
        [.frames 2,.arrayAllocation 8,.listAllocation memberResult.1.1.length] ++
          under 2 memberResult.1.2 ++ under 2 later.1.2),
        memberResult.2+later.2+memberResult.1.1.length+1)

def groupsWithTrace {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (items : List (Fin m)) : List (Fin n × BinaryGroupRoutes.Route m) × Trace :=
  (groupsWithTraceAndWork store groups items).1

theorem groups_erases {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (items : List (Fin m)) :
    (groupsWithTrace store groups items).1 =
      (BinaryTerminalRouteLifetime.groupsWithTrace length groups items).1 := by
  induction items with
  | nil => rfl
  | cons g rest ih =>
      have hMembers := members_erases store length (groups.read g).2 g hRead
        (groups.read g).1
      change (groupsWithTraceAndWork store groups rest).1.1 =
        (BinaryTerminalRouteLifetime.groupsWithTrace length groups rest).1 at ih
      simp only [groupsWithTrace,groupsWithTraceAndWork,
        BinaryTerminalRouteLifetime.groupsWithTrace,ih]
      exact congrArg (fun head => head ++
        (BinaryTerminalRouteLifetime.groupsWithTrace length groups rest).1)
        hMembers

theorem groups_usage {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (items : List (Fin m)) (W : ℕ)
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (hL : ∀ j, width (length.read j) ≤ W)
    (hT : ∀ g, width (groups.read g).2 ≤ W)
    (hM : ∀ g, (groups.read g).1.length ≤ n) :
    usage (groupsWithTrace store groups items).2 ≤
      items.length * (n*(2000000*(W+2)^4 +
        BinaryWordObjectArrayAccess.envelope store (binaryWordWidth n)+32*n+45)+23)+9 := by
  induction items with
  | nil => simp [groupsWithTrace,groupsWithTraceAndWork,usage,BinaryPRGHeapPrimitiveLifetime.cells,
      listCells,arraySlots,framePeak]
  | cons g rest ih =>
      let members := membersWithTrace store (groups.read g).2 g (groups.read g).1
      let later := groupsWithTrace store groups rest
      have hMembers := members_usage store length (groups.read g).2 g
        (groups.read g).1 W hRead hL (hT g)
      have hMemberLength : members.1.length = (groups.read g).1.length := by
        dsimp only [members]
        rw [members_erases store length _ g hRead,
          BinaryTerminalRouteLifetime.membersWithTrace_erases,List.length_map]
      have hHeader : usage [.frames 2,.arrayAllocation 8,
          .listAllocation members.1.length] = members.1.length+10 := by
        simp [usage,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,framePeak]
      have hAppend1 := usage_append
        [.frames 2,.arrayAllocation 8,.listAllocation members.1.length]
        (under 2 members.2 ++ under 2 later.2)
      have hAppend2 := usage_append (under 2 members.2) (under 2 later.2)
      have hUnder1 := usage_under 2 members.2
      have hUnder2 := usage_under 2 later.2
      have hMul := Nat.mul_le_mul_right
        (2000000*(W+2)^4 + BinaryWordObjectArrayAccess.envelope store
          (binaryWordWidth n)+32*n+45) (hM g)
      simp only [groupsWithTrace,groupsWithTraceAndWork,
        List.length_cons,List.append_assoc] at *
      dsimp only [members,later] at *
      change usage (membersWithTrace store (groups.read g).2 g
        (groups.read g).1).2 ≤ _ at hMembers
      change usage (groupsWithTrace store groups rest).2 ≤ _ at ih
      have hPrice : (groups.read g).1.length *
          (2000000*(W+2)^4 + BinaryWordObjectArrayAccess.envelope store
            (binaryWordWidth n)+32*n+44) + (groups.read g).1.length =
          (groups.read g).1.length *
          (2000000*(W+2)^4 + BinaryWordObjectArrayAccess.envelope store
            (binaryWordWidth n)+32*n+45) := by ring
      rw [Nat.add_mul,one_mul]
      change usage ([.frames 2,.arrayAllocation 8,
        .listAllocation (membersWithTrace store (groups.read g).2 g
          (groups.read g).1).1.length] ++
        (under 2 (membersWithTrace store (groups.read g).2 g
          (groups.read g).1).2 ++
        under 2 (groupsWithTrace store groups rest).2)) ≤ _
      omega

def groupWorkEnvelope {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (W : ℕ) : ℕ :=
  n*memberWorkEnvelope store W+n+2

theorem groups_work_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (items : List (Fin m)) (W : ℕ)
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (hL : ∀ j, width (length.read j) ≤ W)
    (hT : ∀ g, width (groups.read g).2 ≤ W)
    (hM : ∀ g, (groups.read g).1.length ≤ n) :
    (groupsWithTraceAndWork store groups items).2 ≤
      items.length * groupWorkEnvelope store W + 1 := by
  induction items with
  | nil => simp [groupsWithTraceAndWork]
  | cons g rest ih =>
      have hMembers := members_work_bound store length (groups.read g).2 g
        (groups.read g).1 W hRead hL (hT g)
      have hMemberLength :
          (membersWithTraceAndWork store (groups.read g).2 g
            (groups.read g).1).1.1.length = (groups.read g).1.length := by
        change (membersWithTrace store (groups.read g).2 g
          (groups.read g).1).1.length = _
        rw [members_erases store length _ g hRead,
          BinaryTerminalRouteLifetime.membersWithTrace_erases,List.length_map]
      have hMul := Nat.mul_le_mul_right
        (memberWorkEnvelope store W) (hM g)
      have hLen := hM g
      change (membersWithTraceAndWork store (groups.read g).2 g
        (groups.read g).1).2 +
        (groupsWithTraceAndWork store groups rest).2 +
        (membersWithTraceAndWork store (groups.read g).2 g
          (groups.read g).1).1.1.length + 1 ≤ _
      rw [hMemberLength]
      simp only [List.length_cons]
      rw [Nat.add_mul,one_mul]
      unfold groupWorkEnvelope at *
      omega

def initialRoutesWithTrace (n m : ℕ) :
    FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace :=
  BinaryLifetimeArray.build n
    (fun _ : Fin n => ((none,zero),[]))

theorem initialRoutes_erases (n m : ℕ) :
    (initialRoutesWithTrace n m).1 =
      FixedArrayTable.ofFn (fun _ : Fin n => (none,zero)) := by
  exact BinaryLifetimeArray.build_erases n
    (fun _ : Fin n => ((none,zero),[]))

theorem initialRoutes_usage (n m : ℕ) :
    usage (initialRoutesWithTrace n m).2 ≤ 2*(n+1)^2+n+14 := by
  have h := BinaryLifetimeArray.build_bounds n
    (fun _ : Fin n => (((none,zero) : BinaryGroupRoutes.Route m),[])) 0 0
    (by intro j; simp [listCells,arraySlots])
    (by intro j; simp [framePeak])
  unfold initialRoutesWithTrace
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

def routesWithTraceAndWork {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    (FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace) × ℕ :=
  let assignments := groupsWithTraceAndWork store groups (List.finRange m)
  let initial := initialRoutesWithTrace n m
  let patched := patchWithTraceAndWork assignments.1.1 initial.1
  ((patched.1.1,[.frames (n+m+8),.listAllocation m,
      .arrayAllocation (8*(n+1)^2+8)] ++
      under 2 initial.2 ++ under 2 assignments.1.2 ++ under 2 patched.1.2),
    assignments.2+patched.2+n*(n+1)+m+1)

def routesWithTrace {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) :
    FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace :=
  (routesWithTraceAndWork store groups).1

theorem routes_erases {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord))
    (hRead : ∀ j, (readLength store j).1 = some (length.read j)) :
    (routesWithTrace store groups).1 =
      (BinaryTerminalRouteLifetime.routesWithTrace length groups).1 := by
  have hGroups := groups_erases store length groups hRead (List.finRange m)
  change (groupsWithTraceAndWork store groups (List.finRange m)).1.1 =
    (BinaryTerminalRouteLifetime.groupsWithTrace length groups (List.finRange m)).1 at hGroups
  simp only [routesWithTrace,routesWithTraceAndWork,
    BinaryTerminalRouteLifetime.routesWithTrace,initialRoutes_erases,
    BinaryTerminalRouteLifetime.patchWithTraceAndWork_erases]
  rw [hGroups]

def routeEnvelope {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (m W : ℕ) : ℕ :=
  m*(n*(2000000*(W+2)^4+
      BinaryWordObjectArrayAccess.envelope store (binaryWordWidth n)+32*n+45)+23) +
    m*n*(2*n*(6*W+7)+9)+2*n+2*m+10*(n+1)^2+80

theorem routes_usage {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (W : ℕ)
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (hL : ∀ j, width (length.read j) ≤ W)
    (hT : ∀ g, width (groups.read g).2 ≤ W)
    (hM : ∀ g, (groups.read g).1.length ≤ n) :
    usage (routesWithTrace store groups).2 ≤ routeEnvelope store m W := by
  let assignments := groupsWithTrace store groups (List.finRange m)
  let initial := initialRoutesWithTrace n m
  let patched := patchWithTrace assignments.1 initial.1
  have hGroups := groups_usage store length groups (List.finRange m) W
    hRead hL hT hM
  have hErase := groups_erases store length groups hRead (List.finRange m)
  have hLen := BinaryTerminalRouteLifetime.groupsWithTrace_length
    length groups (List.finRange m) hM
  rw [← hErase] at hLen
  simp only [List.length_finRange] at hGroups hLen
  have hInitial : ∀ j, routeWords (initial.1.read j) ≤ 6*W+7 := by
    intro j
    norm_num [initial,initialRoutes_erases,FixedArrayTable.read_ofFn,routeWords,
      BinaryRationalRegisterProgram.payloadWords,zero]
  have hEntries : ∀ entry ∈ assignments.1, routeWords entry.2 ≤ 6*W+7 := by
    intro entry he
    change entry ∈ (groupsWithTrace store groups (List.finRange m)).1 at he
    rw [hErase,BinaryTerminalRouteLifetime.groupsWithTrace_erases] at he
    obtain ⟨g,_hg,he⟩ := List.mem_flatMap.mp he
    obtain ⟨j,_hj,hEq⟩ := List.mem_map.mp he
    subst entry
    have hWidth : width (apply .div (length.read j) (groups.read g).2) ≤ 3*W+1 :=
      (BinaryPRGPreparationWork.apply_stored_width .div _ _).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3
          (max_le (hL j) (hT g))) 1)
    have hp := BinaryRationalRegisterProgram.payloadWords_bound _ (3*W+1) hWidth
    unfold routeWords
    dsimp only
    omega
  have hPatch := patchWithTrace_bound assignments.1 initial.1 (6*W+7)
    hInitial hEntries
  have hPatchUsage : usage patched.2 ≤
      assignments.1.length*(2*n*(6*W+7)+9)+9 := by
    have hEq : assignments.1.length*(2*n*(6*W+7)+9)+9 =
        assignments.1.length*(2*n*(6*W+7)+8)+8 +
          (assignments.1.length+1) := by ring
    dsimp only [patched]
    rw [hEq]
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hPatchMono := Nat.mul_le_mul_right (2*n*(6*W+7)+9) hLen
  have hHeader : usage [.frames (n+m+8),.listAllocation m,
      .arrayAllocation (8*(n+1)^2+8)] =
      n+2*m+8*(n+1)^2+16 := by
    simp [usage,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,framePeak]
    omega
  have hInitialUsage := initialRoutes_usage n m
  have hAppend1 := usage_append
    [.frames (n+m+8),.listAllocation m,.arrayAllocation (8*(n+1)^2+8)]
    (under 2 initial.2 ++ under 2 assignments.2 ++ under 2 patched.2)
  have hAppend2 := usage_append (under 2 initial.2)
    (under 2 assignments.2 ++ under 2 patched.2)
  have hAppend3 := usage_append (under 2 assignments.2) (under 2 patched.2)
  have hUnder0 := usage_under 2 initial.2
  have hUnder1 := usage_under 2 assignments.2
  have hUnder2 := usage_under 2 patched.2
  have hRouteTrace : (routesWithTrace store groups).2 =
      [.frames (n+m+8),.listAllocation m,
        .arrayAllocation (8*(n+1)^2+8)] ++
        under 2 initial.2 ++ under 2 assignments.2 ++ under 2 patched.2 := by
    unfold routesWithTrace routesWithTraceAndWork
    dsimp only
    rw [BinaryTerminalRouteLifetime.patchWithTraceAndWork_erases]
    rfl
  rw [hRouteTrace]
  unfold routeEnvelope
  dsimp only [assignments,initial,patched] at *
  simp only [List.append_assoc] at *
  omega

def routeWorkEnvelope {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (m W : ℕ) : ℕ :=
  m*groupWorkEnvelope store W + m*n*(n+1)+n*(n+1)+m+3

theorem readBound_le_lifetimeEnvelope {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (indexWidth : ℕ) :
    BinaryWordObjectArray.readBound store indexWidth ≤
      BinaryWordObjectArrayAccess.envelope store indexWidth := by
  unfold BinaryWordObjectArray.readBound BinaryWordObjectArrayAccess.envelope
    BinaryWordObjectArrayAccess.heapReadEnvelope
  omega

theorem routes_work_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (length : FixedArrayTable n SignedWord)
    (groups : FixedArrayTable m (List (Fin n) × SignedWord)) (W : ℕ)
    (hRead : ∀ j, (readLength store j).1 = some (length.read j))
    (hL : ∀ j, width (length.read j) ≤ W)
    (hT : ∀ g, width (groups.read g).2 ≤ W)
    (hM : ∀ g, (groups.read g).1.length ≤ n) :
    (routesWithTraceAndWork store groups).2 ≤ routeWorkEnvelope store m W := by
  let assignments := groupsWithTraceAndWork store groups (List.finRange m)
  let initial := initialRoutesWithTrace n m
  let patched := patchWithTraceAndWork assignments.1.1 initial.1
  have hGroups := groups_work_bound store length groups (List.finRange m) W
    hRead hL hT hM
  simp only [List.length_finRange] at hGroups
  have hLength : assignments.1.1.length ≤ m*n := by
    change (groupsWithTrace store groups (List.finRange m)).1.length ≤ _
    rw [groups_erases store length groups hRead]
    simpa only [List.length_finRange] using
      (BinaryTerminalRouteLifetime.groupsWithTrace_length
        length groups (List.finRange m) hM)
  have hPatch := BinaryTerminalRouteLifetime.patchWithTraceAndWork_charge
    assignments.1.1 initial.1
  have hPatchMul := Nat.mul_le_mul_right (n+1) hLength
  change assignments.2 + patched.2 + n*(n+1)+m+1 ≤ _
  rw [hPatch]
  unfold routeWorkEnvelope groupWorkEnvelope
  dsimp only [assignments,patched] at *
  unfold groupWorkEnvelope at hGroups
  omega

theorem accepted_length_read (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (j : Fin parsed.1.1) :
    (readLength parsed.1.2.physical.lengthStore j).1 =
      some ((BinaryPRGTerminalWork.terminalInput
        parsed.1.2.logical.request rich state).length.read j) := by
  have h := (BinaryPRGPhysicalRawRequestLifetime.returned_resource_reads
    frame parsed hParsed rich (address j) j (address_value j)).1
  exact h

theorem accepted_routes_erases (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    {m : ℕ} (groups : FixedArrayTable m
      (List (Fin parsed.1.1) × SignedWord)) :
    (routesWithTrace parsed.1.2.physical.lengthStore groups).1 =
      (BinaryTerminalRouteLifetime.routesWithTrace
        (BinaryPRGTerminalWork.terminalInput
          parsed.1.2.logical.request rich state).length groups).1 := by
  exact routes_erases _ _ _ (accepted_length_read frame parsed hParsed rich state)

def rawRouteEnvelope (L W : ℕ) : ℕ :=
  3*(L*(2000000*(W+2)^4+
      PRGPhysicalArrayInterface.readEnvelope L+32*L+45)+23) +
    3*L*(2*L*(6*W+7)+9)+2*L+6+10*(L+1)^2+80

def rawRouteWorkEnvelope (L W : ℕ) : ℕ :=
  3*(L*(L*(binaryWordWidth L+4)+12*(L+1)^2+
    PRGPhysicalArrayInterface.readEnvelope L+12000*(W+1)^3+5)+L+2) +
    3*L*(L+1)+L*(L+1)+6

theorem rawRouteWorkEnvelope_mono (L : ℕ) {W V : ℕ} (h : W ≤ V) :
    rawRouteWorkEnvelope L W ≤ rawRouteWorkEnvelope L V := by
  unfold rawRouteWorkEnvelope
  gcongr

theorem rawRouteWorkEnvelope_polynomial (L : ℕ) :
    rawRouteWorkEnvelope L (6*(L+3)) ≤ 10000000000*(L+3)^8 := by
  let t := L+3
  have ht : 1 ≤ t := by dsimp only [t]; omega
  have hL : L ≤ t := by dsimp only [t]; omega
  have hWidth : binaryWordWidth L ≤ t := by
    have hLog := Nat.log2_le_self L
    unfold binaryWordWidth
    dsimp only [t]
    omega
  have hOne : L+1 ≤ t := by dsimp only [t]; omega
  have hW : 6*t+1 ≤ 7*t := by omega
  have hRead := BinaryPRGPhysicalResourceRawBound.readEnvelope_polynomial L
  have hUpper : rawRouteWorkEnvelope L (6*t) ≤
      3*(t*(t*(t+4)+12*t^2+600000000*t^6+12000*(7*t)^3+5)+t+2)+
        3*t*(t+1)+t*(t+1)+6 := by
    unfold rawRouteWorkEnvelope
    gcongr
  have h0 : 1 ≤ t^8 := Nat.one_le_pow 8 t ht
  have h1 : t ≤ t^8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<t)
      (by decide : 1 ≤ 8)
  have h2 : t^2 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : t^3 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : t^4 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h5 : t^5 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : t^6 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : t^7 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  change rawRouteWorkEnvelope L (6*t) ≤ 10000000000*t^8
  nlinarith only [hUpper,h0,h1,h2,h3,h4,h5,h6,h7]

theorem rawRouteEnvelope_mono (L : ℕ) {W V : ℕ} (h : W ≤ V) :
    rawRouteEnvelope L W ≤ rawRouteEnvelope L V := by
  unfold rawRouteEnvelope
  gcongr

theorem rawRouteEnvelope_polynomial (L : ℕ) :
    rawRouteEnvelope L (6*(L+3)) ≤ 20000000000*(L+3)^8 := by
  let t := L+3
  have ht : 1 ≤ t := by dsimp only [t]; omega
  have hL : L ≤ t := by dsimp only [t]; omega
  have hWidth : 6*t+2 ≤ 7*t := by omega
  have hPatch : 6*(6*t)+7 ≤ 43*t := by omega
  have hOne : L+1 ≤ t := by dsimp only [t]; omega
  have hRead := BinaryPRGPhysicalResourceRawBound.readEnvelope_polynomial L
  have hUpper : rawRouteEnvelope L (6*t) ≤
      3*(t*(2000000*(7*t)^4+600000000*t^6+32*t+45)+23)+
        3*t*(2*t*(43*t)+9)+2*t+6+10*t^2+80 := by
    unfold rawRouteEnvelope
    gcongr
  have h0 : 1 ≤ t^8 := Nat.one_le_pow 8 t ht
  have h1 : t ≤ t^8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<t)
      (by decide : 1 ≤ 8)
  have h2 : t^2 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : t^3 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h5 : t^5 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : t^7 ≤ t^8 := Nat.pow_le_pow_right (by omega) (by decide)
  change rawRouteEnvelope L (6*t) ≤ 20000000000*t^8
  nlinarith only [hUpper,h0,h1,h2,h3,h5,h7]

theorem accepted_dimension (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.1 ≤ frame.length := by
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  exact BinaryPRGSeedRequestBound.read_dimension_bound frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRead

theorem accepted_source_width (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.2.logical.request.source.originalInputWordWidth ≤
      3*frame.length+6 := by
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  change parsed.1.2.logical.request.source.originalInputWordWidth ≤
    3*frame.length+6
  exact BinaryPRGFrameCostJoin.read_source_width frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRead

theorem accepted_length_envelope (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    BinaryWordObjectArrayAccess.envelope parsed.1.2.physical.lengthStore
      (binaryWordWidth parsed.1.1) ≤
      PRGPhysicalArrayInterface.readEnvelope frame.length := by
  have hLookup := BinaryPRGPhysicalResourceRawBound.returned_lookupEnvelope_raw
    frame parsed hParsed true
  unfold BinaryPRGPhysicalResourceInitialLifetime.lookupEnvelope
    BinaryPRGPhysicalResourceInitialLifetime.resourceStore at hLookup
  simp only [ite_true] at hLookup
  omega

theorem accepted_lattice_width (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    1+2*binaryWordWidth
      parsed.1.2.logical.request.source.normalizedInput.latticeDenominator ≤
        6*(frame.length+3) := by
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hSource := BinaryPRGFrameCostJoin.read_source_width frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRead
  change parsed.1.2.logical.request.source.originalInputWordWidth ≤
    3*frame.length+6 at hSource
  have hLattice := parsed.1.2.logical.request.source.normalized_lattice_wordWidth_original
  omega

theorem accepted_prefixBound_raw (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    BinaryTerminalPrefixLifetime.prefixBound parsed.1.2.logical.request ≤
      BinaryTerminalCacheLifetime.polynomialBound frame.length := by
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hSource := BinaryPRGFrameCostJoin.read_source_width frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRead
  change parsed.1.2.logical.request.source.originalInputWordWidth ≤
    3*frame.length+6 at hSource
  have hDimension := accepted_dimension frame parsed hParsed
  have hMono := BinaryTerminalCacheLifetime.envelope_mono hDimension hSource
  have hSub : BinaryTerminalPrefixLifetime.prefixBound
      parsed.1.2.logical.request ≤
      BinaryTerminalCacheLifetime.envelope parsed.1.1
        parsed.1.2.logical.request.source.originalInputWordWidth := by
    unfold BinaryTerminalPrefixLifetime.prefixBound
      BinaryTerminalCacheLifetime.envelope
    omega
  exact hSub.trans (hMono.trans
    (BinaryTerminalCacheLifetime.frameBound_polynomial frame.length))

theorem accepted_routes_raw_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    {m : ℕ} (groups : FixedArrayTable m (List (Fin parsed.1.1) × SignedWord))
    (W : ℕ) (hCount : m ≤ 3)
    (hL : ∀ j, width ((BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state).length.read j) ≤ W)
    (hT : ∀ g, width (groups.read g).2 ≤ W)
    (hM : ∀ g, (groups.read g).1.length ≤ parsed.1.1) :
    usage (routesWithTrace parsed.1.2.physical.lengthStore groups).2 ≤
      rawRouteEnvelope frame.length W := by
  have hNative := routes_usage parsed.1.2.physical.lengthStore
    (BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state).length groups W
    (accepted_length_read frame parsed hParsed rich state) hL hT hM
  have hn := accepted_dimension frame parsed hParsed
  have hRead := accepted_length_envelope frame parsed hParsed
  apply hNative.trans
  unfold routeEnvelope rawRouteEnvelope
  gcongr
  omega

theorem accepted_routes_raw_work (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    {m : ℕ} (groups : FixedArrayTable m (List (Fin parsed.1.1) × SignedWord))
    (W : ℕ) (hCount : m ≤ 3)
    (hL : ∀ j, width ((BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state).length.read j) ≤ W)
    (hT : ∀ g, width (groups.read g).2 ≤ W)
    (hM : ∀ g, (groups.read g).1.length ≤ parsed.1.1) :
    (routesWithTraceAndWork parsed.1.2.physical.lengthStore groups).2 ≤
      rawRouteWorkEnvelope frame.length W := by
  let store := parsed.1.2.physical.lengthStore
  let n := parsed.1.1
  let L := frame.length
  let upper := L*(binaryWordWidth L+4)+12*(L+1)^2+
    PRGPhysicalArrayInterface.readEnvelope L+12000*(W+1)^3+5
  have hNative := routes_work_bound store
    (BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state).length groups W
    (accepted_length_read frame parsed hParsed rich state) hL hT hM
  have hDimension : n ≤ L := accepted_dimension frame parsed hParsed
  have hRead := (readBound_le_lifetimeEnvelope store (binaryWordWidth n)).trans
    (accepted_length_envelope frame parsed hParsed)
  have hWidth := binaryWordWidth_mono hDimension
  have hMember : memberWorkEnvelope store W ≤ upper := by
    unfold memberWorkEnvelope upper
    gcongr
  have hGroup : groupWorkEnvelope store W ≤ L*upper+L+2 := by
    unfold groupWorkEnvelope
    gcongr
  have hMG := Nat.mul_le_mul hCount hGroup
  have hPatchA : m*n*(n+1) ≤ 3*L*(L+1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hCount hDimension) (by omega)
  have hPatchB : n*(n+1) ≤ L*(L+1) := by gcongr
  apply hNative.trans
  unfold routeWorkEnvelope rawRouteWorkEnvelope
  dsimp only [store,n,L,upper] at *
  omega

theorem accepted_reached_routes_raw_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 = some state) :
    let input := BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state
    let cached := BinaryCachedTerminalPreparation.prepare input
    usage (routesWithTrace parsed.1.2.physical.lengthStore cached.packing).2 ≤
      rawRouteEnvelope frame.length
        (1+2*binaryWordWidth
          parsed.1.2.logical.request.source.normalizedInput.latticeDenominator) := by
  let request := parsed.1.2.logical.request
  let input := BinaryPRGTerminalWork.terminalInput request rich state
  let cached := BinaryCachedTerminalPreparation.prepare input
  have hNative : (BinaryPRGWordControllerResource.requestRun seed request rich).1 =
      some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (BinaryPRGResourceWork.resourceWork request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst
      (BinaryPRGWordControllerResource.requestRun_state seed request rich)
    exact h.symm.trans hNative
  have hC := BinaryPRGTerminalWork.terminal_canonical request rich state
  have hAd := BinaryPRGTerminalWork.terminal_admissible request rich
    seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource
  have hCount : cached.count ≤ 3 := by
    rcases cached.count_bound hC hAd with he | he <;> omega
  exact accepted_routes_raw_usage frame parsed hParsed rich state cached.packing
    _ hCount
    (BinaryPRGTerminalWork.terminal_length_width request rich state)
    (BinaryTerminalRouteLifetime.reached_total_width request rich
      seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource)
    (BinaryCachedTerminalWork.Prepared.members_length cached hC hAd)

theorem accepted_reached_routes_polynomial_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 = some state) :
    let input := BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state
    let cached := BinaryCachedTerminalPreparation.prepare input
    usage (routesWithTrace parsed.1.2.physical.lengthStore cached.packing).2 ≤
      20000000000*(frame.length+3)^8 := by
  have hRoute := accepted_reached_routes_raw_usage frame parsed hParsed rich seed
    state hState
  have hWidth := accepted_lattice_width frame parsed hParsed
  exact hRoute.trans ((rawRouteEnvelope_mono frame.length hWidth).trans
    (rawRouteEnvelope_polynomial frame.length))

theorem accepted_reached_routes_polynomial_work (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 = some state) :
    let input := BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state
    let cached := BinaryCachedTerminalPreparation.prepare input
    (routesWithTraceAndWork parsed.1.2.physical.lengthStore cached.packing).2 ≤
      10000000000*(frame.length+3)^8 := by
  let request := parsed.1.2.logical.request
  let input := BinaryPRGTerminalWork.terminalInput request rich state
  let cached := BinaryCachedTerminalPreparation.prepare input
  have hNative : (BinaryPRGWordControllerResource.requestRun seed request rich).1 =
      some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (BinaryPRGResourceWork.resourceWork request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst
      (BinaryPRGWordControllerResource.requestRun_state seed request rich)
    exact h.symm.trans hNative
  have hC := BinaryPRGTerminalWork.terminal_canonical request rich state
  have hAd := BinaryPRGTerminalWork.terminal_admissible request rich
    seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource
  have hCount : cached.count ≤ 3 := by
    rcases cached.count_bound hC hAd with he | he <;> omega
  have hRoute := accepted_routes_raw_work frame parsed hParsed rich state
    cached.packing _ hCount
    (BinaryPRGTerminalWork.terminal_length_width request rich state)
    (BinaryTerminalRouteLifetime.reached_total_width request rich
      seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource)
    (BinaryCachedTerminalWork.Prepared.members_length cached hC hAd)
  have hWidth := accepted_lattice_width frame parsed hParsed
  exact hRoute.trans ((rawRouteWorkEnvelope_mono frame.length hWidth).trans
    (rawRouteWorkEnvelope_polynomial frame.length))

def totalsWithTrace {n m : ℕ}
    (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    FixedArrayTable m SignedWord × Trace :=
  BinaryLifetimeArray.build m (fun g => ((packing.read g).2,[]))

@[simp] theorem totalsWithTrace_erases {n m : ℕ}
    (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    (totalsWithTrace packing).1 = FixedArrayTable.ofFn (fun g => (packing.read g).2) := by
  exact BinaryLifetimeArray.build_erases m (fun g => ((packing.read g).2,[]))

theorem totalsWithTrace_usage {n m : ℕ}
    (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    usage (totalsWithTrace packing).2 ≤ 2*(m+1)^2+m+14 := by
  have h := BinaryLifetimeArray.build_bounds m
    (fun g => ((packing.read g).2,[])) 0 0
    (by intro g; simp [listCells,arraySlots])
    (by intro g; simp [framePeak])
  unfold totalsWithTrace
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

def cacheWithTraceAndWork {n : ℕ} (input : BinaryTerminalGrouping.Input n)
    (store : BinaryWordObjectArray.Store n) :
    (BinaryTerminalCacheLifetime.CacheData input × Trace) × ℕ :=
  let front := BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing := BinaryTerminalCacheLifetime.packingOfEntries entries
  let totals := totalsWithTrace packing
  let routes := routesWithTraceAndWork store packing
  let pivot := front.1.1.pivot
  let extra := BinaryTerminalCacheLifetime.pivotWithTraceAndWork input pivot
  ((⟨count,packing,totals.1,routes.1.1,pivot,extra.1.1.1,extra.1.1.2⟩,
    front.1.2.2 ++ [.frames (count+n+8),.arrayAllocation (2*(count+1)^2+16)] ++
      under 2 totals.2 ++ under 2 routes.1.2 ++ under 2 extra.1.2),
    front.2+routes.2+extra.2+count+n+5+
      (count*(count+1)+2*count+5))

def cacheWithTrace {n : ℕ} (input : BinaryTerminalGrouping.Input n)
    (store : BinaryWordObjectArray.Store n) :
    BinaryTerminalCacheLifetime.CacheData input × Trace :=
  (cacheWithTraceAndWork input store).1

theorem selected_routes_trace_eq_prepared {n : ℕ}
    (input : BinaryTerminalGrouping.Input n)
    (store : BinaryWordObjectArray.Store n) :
    (routesWithTrace store (BinaryTerminalCacheLifetime.packingOfEntries
      (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1)).2 =
    (routesWithTrace store
      (BinaryCachedTerminalPreparation.prepare input).packing).2 := by
  have hEntries := (BinaryTerminalPrefixLifetime.prefixWithTrace_erases input).2.2
  simp only [BinaryTerminalPrefixLifetime.prefixWithTrace] at hEntries
  have h := congrArg (fun entries => (routesWithTrace store
    (BinaryTerminalCacheLifetime.packingOfEntries entries)).2) hEntries
  simpa only [BinaryCachedTerminalPreparation.prepare,
    BinaryTerminalCacheLifetime.packingOfEntries] using h

theorem selected_routes_work_eq_prepared {n : ℕ}
    (input : BinaryTerminalGrouping.Input n)
    (store : BinaryWordObjectArray.Store n) :
    (routesWithTraceAndWork store (BinaryTerminalCacheLifetime.packingOfEntries
      (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1)).2 =
    (routesWithTraceAndWork store
      (BinaryCachedTerminalPreparation.prepare input).packing).2 := by
  have hEntries := (BinaryTerminalPrefixLifetime.prefixWithTrace_erases input).2.2
  simp only [BinaryTerminalPrefixLifetime.prefixWithTrace] at hEntries
  have h := congrArg (fun entries => (routesWithTraceAndWork store
    (BinaryTerminalCacheLifetime.packingOfEntries entries)).2) hEntries
  simpa only [BinaryCachedTerminalPreparation.prepare,
    BinaryTerminalCacheLifetime.packingOfEntries] using h

theorem accepted_reached_cache_polynomial_work (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 = some state) :
    let input := BinaryPRGTerminalWork.terminalInput
      parsed.1.2.logical.request rich state
    (cacheWithTraceAndWork input parsed.1.2.physical.lengthStore).2 ≤
      11000000000*(frame.length+3)^8 := by
  let request := parsed.1.2.logical.request
  let input := BinaryPRGTerminalWork.terminalInput request rich state
  let store := parsed.1.2.physical.lengthStore
  let front := BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input
  let count := front.1.2.1.length
  let packing := BinaryTerminalCacheLifetime.packingOfEntries front.1.2.1
  let route := routesWithTraceAndWork store packing
  let extra := BinaryTerminalCacheLifetime.pivotWithTraceAndWork input front.1.1.pivot
  have hNative : (BinaryPRGWordControllerResource.requestRun seed request rich).1 =
      some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (BinaryPRGResourceWork.resourceWork request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst
      (BinaryPRGWordControllerResource.requestRun_state seed request rich)
    exact h.symm.trans hNative
  have hPrior := BinaryTerminalCacheLifetime.cacheWithTraceAndPivotWork_reached_bound
    request rich seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource
  change front.2 + extra.2 ≤
    (166000*parsed.1.1+96000)*(request.source.originalInputWordWidth+2)^3 at hPrior
  have hRoute := accepted_reached_routes_polynomial_work
    frame parsed hParsed rich seed state hState
  have hSelectedRoute : route.2 ≤ 10000000000*(frame.length+3)^8 := by
    dsimp only [route,packing,front]
    rw [selected_routes_work_eq_prepared input store]
    exact hRoute
  have hEntries := (BinaryTerminalPrefixLifetime.prefixWithTrace_erases input).2.2
  simp only [BinaryTerminalPrefixLifetime.prefixWithTrace] at hEntries
  have hC := BinaryPRGTerminalWork.terminal_canonical request rich state
  have hAd := BinaryPRGTerminalWork.terminal_admissible request rich
    seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource
  have hCachedCount : (BinaryCachedTerminalPreparation.prepare input).count ≤ 3 := by
    rcases (BinaryCachedTerminalPreparation.prepare input).count_bound hC hAd
      with he | he <;> omega
  have hCount : count ≤ 3 := by
    dsimp only [count,front]
    rw [hEntries]
    simpa only [BinaryCachedTerminalPreparation.prepare] using hCachedCount
  have hDim := accepted_dimension frame parsed hParsed
  have hWidth := accepted_source_width frame parsed hParsed
  let t := frame.length+3
  have ht : 1 ≤ t := by dsimp only [t]; omega
  have hn : parsed.1.1 ≤ t := by dsimp only [t]; omega
  have hw : request.source.originalInputWordWidth+2 ≤ 3*t := by
    dsimp only [t,request]
    omega
  have hc : 166000*parsed.1.1+96000 ≤ 262000*t := by omega
  have hPriorTop : front.2+extra.2 ≤ 7074000*t^8 := by
    have hCube := Nat.pow_le_pow_left hw 3
    have hBase : (166000*parsed.1.1+96000)*
        (request.source.originalInputWordWidth+2)^3 ≤ 7074000*t^4 := by
      calc
        _ ≤ (262000*t)*(3*t)^3 := Nat.mul_le_mul hc hCube
        _ = 7074000*t^4 := by ring
    have hPow : t^4 ≤ t^8 := Nat.pow_le_pow_right ht (by decide)
    exact hPrior.trans (hBase.trans (Nat.mul_le_mul_left _ hPow))
  have hTotalsControl : count*(count+1)+2*count+5 ≤ 23 := by
    nlinarith only [hCount]
  have hSmall : count+parsed.1.1+5+(count*(count+1)+2*count+5) ≤
      40*t^8 := by
    have hOne : t ≤ t^8 := by
      simpa only [pow_one] using Nat.pow_le_pow_right ht (by decide : 1 ≤ 8)
    have hZero : 1 ≤ t^8 := Nat.one_le_pow 8 t ht
    omega
  change route.2 ≤ 10000000000*t^8 at hSelectedRoute
  change front.2+route.2+extra.2+count+parsed.1.1+5+
    (count*(count+1)+2*count+5) ≤ _
  calc
    _ ≤ 7074000*t^8+10000000000*t^8+40*t^8 := by omega
    _ ≤ 11000000000*t^8 := by nlinarith [Nat.zero_le (t^8)]

theorem accepted_reached_cache_raw_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 = some state) :
    let request := parsed.1.2.logical.request
    let input := BinaryPRGTerminalWork.terminalInput request rich state
    usage (cacheWithTrace input parsed.1.2.physical.lengthStore).2 ≤
      BinaryTerminalPrefixLifetime.prefixBound request +
        rawRouteEnvelope frame.length
          (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator) +
        2000000*(3+2*binaryWordWidth
          request.source.normalizedInput.latticeDenominator)^4 +
        3*parsed.1.1+200 := by
  let request := parsed.1.2.logical.request
  let input := BinaryPRGTerminalWork.terminalInput request rich state
  let store := parsed.1.2.physical.lengthStore
  let front := BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input
  let entries := front.1.2.1
  let count := entries.length
  let packing := BinaryTerminalCacheLifetime.packingOfEntries entries
  let totals := totalsWithTrace packing
  let routes := routesWithTrace store packing
  let pivot := front.1.1.pivot
  let extra := BinaryTerminalCacheLifetime.pivotWithTrace input pivot
  have hNative : (BinaryPRGWordControllerResource.requestRun seed request rich).1 =
      some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (BinaryPRGResourceWork.resourceWork request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst
      (BinaryPRGWordControllerResource.requestRun_state seed request rich)
    exact h.symm.trans hNative
  have hCachedCount : (BinaryCachedTerminalPreparation.prepare input).count ≤ 3 := by
    have hC := BinaryPRGTerminalWork.terminal_canonical request rich state
    have hAd := BinaryPRGTerminalWork.terminal_admissible request rich
      seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource
    rcases (BinaryCachedTerminalPreparation.prepare input).count_bound hC hAd
      with he | he <;> omega
  have hEntries := (BinaryTerminalPrefixLifetime.prefixWithTrace_erases input).2.2
  simp only [BinaryTerminalPrefixLifetime.prefixWithTrace] at hEntries
  have hCount : count ≤ 3 := by
    dsimp only [count,entries,front]
    rw [hEntries]
    simpa only [BinaryCachedTerminalPreparation.prepare] using hCachedCount
  have hPrefix := BinaryTerminalPrefixLifetime.reached_prefix_bound request rich
    seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource
  change listCells (BinaryTerminalPrefixLifetime.prefixWithTrace input).2.2+
      arraySlots (BinaryTerminalPrefixLifetime.prefixWithTrace input).2.2 ≤
        BinaryTerminalPrefixLifetime.prefixBound request ∧
      framePeak (BinaryTerminalPrefixLifetime.prefixWithTrace input).2.2 ≤
        2*parsed.1.1+10 at hPrefix
  have hPrefixUsage : usage front.1.2.2 ≤
      BinaryTerminalPrefixLifetime.prefixBound request+2*parsed.1.1+10 := by
    dsimp only [front]
    change usage (BinaryTerminalPrefixLifetime.prefixWithTrace input).2.2 ≤ _
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hRoute := accepted_reached_routes_raw_usage frame parsed hParsed rich seed state hState
  have hSelectedRoute : usage routes.2 ≤
      rawRouteEnvelope frame.length
        (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator) := by
    dsimp only [routes,packing,entries,front]
    rw [selected_routes_trace_eq_prepared input store]
    exact hRoute
  have hPivot := BinaryTerminalCacheLifetime.pivotWithTrace_bound input pivot
    (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)
    (BinaryPRGTerminalWork.terminal_length_width request rich state)
    (BinaryPRGTerminalWork.terminal_resource_width request rich
      seed.cap.value (BinaryWordIndexCoinController.reader seed) state hResource)
  have hPivotUsage : usage extra.2 ≤
      2000000*(3+2*binaryWordWidth
        request.source.normalizedInput.latticeDenominator)^4+9 := by
    dsimp only [extra]
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    have hWidth : 1+2*binaryWordWidth
        request.source.normalizedInput.latticeDenominator+2 =
        3+2*binaryWordWidth request.source.normalizedInput.latticeDenominator := by omega
    rw [hWidth] at hPivot
    omega
  have hRegions : 2*(count+1)^2+16 ≤ 48 := by nlinarith only [hCount]
  have hTotals : usage totals.2 ≤ 49 := by
    have h := totalsWithTrace_usage packing
    have hBound : 2*(count+1)^2+count+14 ≤ 49 := by nlinarith only [hCount]
    exact h.trans hBound
  have hHeader : usage [.frames (count+parsed.1.1+8),
      .arrayAllocation (2*(count+1)^2+16)] ≤ parsed.1.1+59 := by
    simp [usage,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,framePeak]
    omega
  have hAppend1 := usage_append front.1.2.2
    ([.frames (count+parsed.1.1+8),.arrayAllocation (2*(count+1)^2+16)] ++
      (under 2 totals.2 ++ (under 2 routes.2 ++ under 2 extra.2)))
  have hAppend2 := usage_append
    [.frames (count+parsed.1.1+8),.arrayAllocation (2*(count+1)^2+16)]
    (under 2 totals.2 ++ (under 2 routes.2 ++ under 2 extra.2))
  have hAppend3 := usage_append (under 2 totals.2)
    (under 2 routes.2 ++ under 2 extra.2)
  have hAppend4 := usage_append (under 2 routes.2) (under 2 extra.2)
  have hUnder0 := usage_under 2 totals.2
  have hUnder1 := usage_under 2 routes.2
  have hUnder2 := usage_under 2 extra.2
  unfold cacheWithTrace cacheWithTraceAndWork
  dsimp only
  simp only [List.append_assoc]
  change usage (front.1.2.2 ++
    ([.frames (count+parsed.1.1+8),.arrayAllocation (2*(count+1)^2+16)] ++
      (under 2 totals.2 ++ (under 2 routes.2 ++ under 2 extra.2)))) ≤ _
  dsimp only [request] at *
  omega

theorem rawCachePolynomialBudget (L n W prior : ℕ)
    (hDimension : n ≤ L) (hWidth : W ≤ 6*(L+3))
    (hPrefix : prior ≤ 2^60*(L+1)^5)
    (hRoute : rawRouteEnvelope L W ≤ 20000000000*(L+3)^8) :
    prior+rawRouteEnvelope L W+2000000*(W+2)^4+3*n+200 ≤
      2^61*(L+3)^8 := by
  let t := L+3
  have ht : 1 ≤ t := by dsimp only [t]; omega
  have hFifth : (L+1)^5 ≤ t^8 :=
    (Nat.pow_le_pow_left (by dsimp only [t]; omega) 5).trans
      (Nat.pow_le_pow_right (by omega : 0<t) (by decide : 5 ≤ 8))
  have hPrefixTop : prior ≤ 2^60*t^8 :=
    hPrefix.trans (Nat.mul_le_mul_left _ hFifth)
  have hPivotBase : W+2 ≤ 7*t := by
    change W ≤ 6*t at hWidth
    omega
  have hFourth : t^4 ≤ t^8 :=
    Nat.pow_le_pow_right (by omega : 0<t) (by decide : 4 ≤ 8)
  have hPivotTop : 2000000*(W+2)^4 ≤ 4802000000*t^8 := by
    calc
      _ ≤ 2000000*(7*t)^4 := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left hPivotBase 4)
      _ = 4802000000*t^4 := by ring
      _ ≤ 4802000000*t^8 := Nat.mul_le_mul_left _ hFourth
  have hFirst : 1 ≤ t^8 := Nat.one_le_pow 8 t ht
  have hLinear : t ≤ t^8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<t)
      (by decide : 1 ≤ 8)
  have hDimensionTop : 3*n+200 ≤ 203*t^8 := by
    have hLt : n ≤ t := hDimension.trans (by dsimp only [t]; omega)
    omega
  have hSum : prior+rawRouteEnvelope L W+2000000*(W+2)^4+
      3*n+200 ≤ (2^60+20000000000+4802000000+203)*t^8 := by
    change rawRouteEnvelope L W ≤ 20000000000*t^8 at hRoute
    calc
      _ ≤ 2^60*t^8+20000000000*t^8+4802000000*t^8+203*t^8 := by omega
      _ = (2^60+20000000000+4802000000+203)*t^8 := by ring
  have hCoeff : (2^60+20000000000+4802000000+203)*t^8 ≤ 2^61*t^8 :=
    Nat.mul_le_mul_right _ (by norm_num)
  exact hSum.trans hCoeff

theorem accepted_cache_envelope_polynomial (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    let request := parsed.1.2.logical.request
    BinaryTerminalPrefixLifetime.prefixBound request+
      rawRouteEnvelope frame.length
        (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)+
        2000000*(3+2*binaryWordWidth
          request.source.normalizedInput.latticeDenominator)^4+
      3*parsed.1.1+200 ≤ 2^61*(frame.length+3)^8 := by
  have hWidth := accepted_lattice_width frame parsed hParsed
  have hRoute := (rawRouteEnvelope_mono frame.length hWidth).trans
    (rawRouteEnvelope_polynomial frame.length)
  have hBudget := rawCachePolynomialBudget frame.length parsed.1.1
    (1+2*binaryWordWidth
      parsed.1.2.logical.request.source.normalizedInput.latticeDenominator)
    (BinaryTerminalPrefixLifetime.prefixBound parsed.1.2.logical.request)
    (accepted_dimension frame parsed hParsed) hWidth
    (accepted_prefixBound_raw frame parsed hParsed) hRoute
  have hArithmetic : 1+2*binaryWordWidth
      parsed.1.2.logical.request.source.normalizedInput.latticeDenominator+2 =
      3+2*binaryWordWidth
        parsed.1.2.logical.request.source.normalizedInput.latticeDenominator := by omega
  simpa only [hArithmetic] using hBudget

theorem accepted_reached_cache_polynomial_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 = some state) :
    let request := parsed.1.2.logical.request
    let input := BinaryPRGTerminalWork.terminalInput request rich state
    usage (cacheWithTrace input parsed.1.2.physical.lengthStore).2 ≤
      2^61*(frame.length+3)^8 := by
  exact (accepted_reached_cache_raw_usage frame parsed hParsed rich seed state hState).trans
    (accepted_cache_envelope_polynomial frame parsed hParsed)

theorem accepted_reached_cache_polynomial_prefix (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 = some state)
    (borrowed steps : ℕ) :
    let request := parsed.1.2.logical.request
    let input := BinaryPRGTerminalWork.terminalInput request rich state
    retainedHeap borrowed (cacheWithTrace input parsed.1.2.physical.lengthStore).2 steps ≤
        borrowed+2^61*(frame.length+3)^8 ∧
      framePeak ((cacheWithTrace input parsed.1.2.physical.lengthStore).2.take steps) ≤
        2^61*(frame.length+3)^8 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_reached_cache_polynomial_usage frame parsed hParsed rich seed state hState)
    borrowed steps

theorem cache_erases {n : ℕ} (input : BinaryTerminalGrouping.Input n)
    (store : BinaryWordObjectArray.Store n)
    (hRead : ∀ j, (readLength store j).1 = some (input.length.read j)) :
    (cacheWithTrace input store).1 =
      (BinaryTerminalCacheLifetime.cacheWithTrace input).1 := by
  have hRoute := routes_erases store input.length
    (BinaryTerminalCacheLifetime.packingOfEntries
      (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1) hRead
  simp only [routesWithTrace] at hRoute
  rw [BinaryTerminalCacheLifetime.cacheWithTrace,
    BinaryTerminalCacheLifetime.cacheWithTraceAndListWork_erases,
    BinaryTerminalCacheLifetime.cacheWithTraceAndPatchWork_erases,
    BinaryTerminalCacheLifetime.cacheWithTraceAndRouteWork_erases]
  unfold cacheWithTrace cacheWithTraceAndWork BinaryTerminalCacheLifetime.cacheWithTraceAndPivotWork
  simpa only [totalsWithTrace_erases,BinaryTerminalCacheLifetime.pivotWithTrace,
    BinaryTerminalCacheLifetime.packingOfEntries] using congrArg
      (fun r : FixedArrayTable n (BinaryGroupRoutes.Route
        (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1.length) =>
        BinaryTerminalCacheLifetime.CacheData.mk
          (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1.length
          (BinaryTerminalCacheLifetime.packingOfEntries
            (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1)
          (FixedArrayTable.ofFn (fun g =>
            ((BinaryTerminalCacheLifetime.packingOfEntries
              (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.2.1).read g).2))
          r
          (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.1.pivot
          (BinaryTerminalCacheLifetime.pivotWithTraceAndWork input
            (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.1.pivot).1.1.1
          (BinaryTerminalCacheLifetime.pivotWithTraceAndWork input
            (BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork input).1.1.pivot).1.1.2) hRoute

theorem accepted_cache_erases (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length) :
    (cacheWithTrace
      (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state)
      parsed.1.2.physical.lengthStore).1 =
      (BinaryTerminalCacheLifetime.cacheWithTrace
        (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state)).1 := by
  exact cache_erases _ _ (accepted_length_read frame parsed hParsed rich state)

def runCachedPrefixWithTraceReference
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × Trace :=
  let request := parsed.2.logical.request
  let resource := BinaryPhysicalHeapRequestLifetime.runWithTrace seed parsed.2 rich
  match resource.1.1 with
  | none => ((none,resource.1.2),wrap 16 2 [resource.2])
  | some state =>
      let cached := cacheWithTrace
        (BinaryPRGTerminalWork.terminalInput request rich state)
        parsed.2.physical.lengthStore
      ((some ⟨state,cached.1⟩,resource.1.2),wrap 24 2 [resource.2,cached.2])

def runCachedPrefixWithTraceAndWork
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    ((Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × Trace) × ℕ :=
  let request := parsed.2.logical.request
  let resource := BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
    seed parsed.2 rich
  match resource.1.1.1 with
  | none => (((none,resource.1.1.2),wrap 16 2 [resource.1.2]),resource.2+4)
  | some state =>
      let cached := cacheWithTraceAndWork
        (BinaryPRGTerminalWork.terminalInput request rich state)
        parsed.2.physical.lengthStore
      (((some ⟨state,cached.1.1⟩,resource.1.1.2),
          wrap 24 2 [resource.1.2,cached.1.2]),resource.2+cached.2+8)

def runCachedPrefixWithTrace (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (Option (BinaryPRGHeapCachedPrefixLifetime.CachedResult
      parsed.2.logical.request rich) × FixedBinaryWord seed.width) × Trace :=
  (runCachedPrefixWithTraceAndWork parsed seed rich).1

theorem runCachedPrefixWithTraceAndWork_erases
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runCachedPrefixWithTraceAndWork parsed seed rich).1 =
      runCachedPrefixWithTraceReference parsed seed rich := by
  unfold runCachedPrefixWithTraceAndWork runCachedPrefixWithTraceReference
  dsimp only
  rw [BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork_erases]
  cases h : (BinaryPhysicalHeapRequestLifetime.runWithTrace seed parsed.2 rich).1.1 <;>
    rfl

noncomputable def cachedPrefixEnvelope (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (seed : BinarySeedLookupTree.Store) : ℕ :=
  let request := parsed.2.logical.request
  let W := 1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator
  BinaryPRGHeapRequestLifetime.envelope request seed.width seed.cap.value+
    2*seed.width+BinaryTerminalPrefixLifetime.prefixBound request+
    rawRouteEnvelope frame.length W+2000000*(W+2)^4+3*parsed.1+250+
    2000000200*(frame.length+3)^7+100

theorem accepted_cachedPrefixEnvelope_bound (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) :
    cachedPrefixEnvelope frame parsed.1 seed ≤
      BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
        seed.width seed.cap.value+2*seed.width+
        2^62*(frame.length+3)^8+250 := by
  have hCache := accepted_cache_envelope_polynomial frame parsed hParsed
  have hPower : (frame.length+3)^7 ≤ (frame.length+3)^8 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hArithmetic : 1+2*binaryWordWidth
      parsed.1.2.logical.request.source.normalizedInput.latticeDenominator+2 =
      3+2*binaryWordWidth
        parsed.1.2.logical.request.source.normalizedInput.latticeDenominator := by omega
  unfold cachedPrefixEnvelope
  dsimp only
  simp only [hArithmetic]
  omega

theorem accepted_cached_prefix_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (runCachedPrefixWithTrace parsed.1 seed rich).2 ≤
      cachedPrefixEnvelope frame parsed.1 seed := by
  let request := parsed.1.2.logical.request
  have hResource := BinaryPhysicalHeapRequestLifetime.accepted_run_usage
    frame parsed hParsed seed rich
  rw [runCachedPrefixWithTrace,runCachedPrefixWithTraceAndWork_erases]
  unfold runCachedPrefixWithTraceReference
  dsimp only
  cases hState : (BinaryPhysicalHeapRequestLifetime.runWithTrace seed parsed.1.2 rich).1.1 with
  | none =>
      have hw := wrap_usage 16 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace seed parsed.1.2 rich).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 16 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace seed parsed.1.2 rich).2]) ≤ _
      unfold cachedPrefixEnvelope
      dsimp only [request] at *
      omega
  | some state =>
      have hOldState : (BinaryPRGHeapRequestLifetime.run seed request rich).1.1 =
          some state := by
        rw [← BinaryPhysicalHeapRequestLifetime.run_erasure]
        exact hState
      have hCache := accepted_reached_cache_raw_usage frame parsed hParsed rich
        seed state hOldState
      have hw := wrap_usage 24 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace seed parsed.1.2 rich).2,
          (cacheWithTrace
            (BinaryPRGTerminalWork.terminalInput request rich state)
            parsed.1.2.physical.lengthStore).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace seed parsed.1.2 rich).2,
          (cacheWithTrace
            (BinaryPRGTerminalWork.terminalInput request rich state)
            parsed.1.2.physical.lengthStore).2]) ≤ _
      unfold cachedPrefixEnvelope
      dsimp only [request] at *
      have hWidth : 1+2*binaryWordWidth
          parsed.1.2.logical.request.source.normalizedInput.latticeDenominator+2 =
          3+2*binaryWordWidth
            parsed.1.2.logical.request.source.normalizedInput.latticeDenominator := by omega
      simp only [hWidth] at *
      omega

theorem accepted_cached_prefix_frame_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (runCachedPrefixWithTrace parsed.1 seed rich).2 ≤
      BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
        seed.width seed.cap.value+2*seed.width+
        2^62*(frame.length+3)^8+250 :=
  (accepted_cached_prefix_usage frame parsed hParsed seed rich).trans
    (accepted_cachedPrefixEnvelope_bound frame parsed hParsed seed)

theorem accepted_cached_prefix_frame_all_prefix (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (runCachedPrefixWithTrace parsed.1 seed rich).2 steps ≤
        borrowed+(BinaryPRGHeapRequestLifetime.envelope
          parsed.1.2.logical.request seed.width seed.cap.value+2*seed.width+
          2^62*(frame.length+3)^8+250) ∧
      framePeak ((runCachedPrefixWithTrace parsed.1 seed rich).2.take steps) ≤
        BinaryPRGHeapRequestLifetime.envelope parsed.1.2.logical.request
          seed.width seed.cap.value+2*seed.width+
          2^62*(frame.length+3)^8+250 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_cached_prefix_frame_usage frame parsed hParsed seed rich)
    borrowed steps

theorem request_envelope_le_existing_cached {n : ℕ}
    (request : BinaryPRGRequest.Request n) (indexWidth seedCap : ℕ) :
    BinaryPRGHeapRequestLifetime.envelope request indexWidth seedCap+
      2*indexWidth ≤
      BinaryPRGHeapCachedPrefixLifetime.envelope request indexWidth seedCap := by
  unfold BinaryPRGHeapCachedPrefixLifetime.envelope
  omega

theorem accepted_cached_prefix_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool)
      (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
      (_hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      usage (runCachedPrefixWithTrace parsed.1 seed rich).2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hOld⟩ :=
    BinaryPRGHeapCallerLifetimePolynomial.uniform_cached_envelope
  refine ⟨C*4^d+2^62+250,max d 8,?_⟩
  intro frame parsed hParsed seed rich
  let request := parsed.1.2.logical.request
  let Q := frame.length+seed.width+seed.cap.value+3
  let D := max d 8
  have hQ : 1 ≤ Q := by dsimp only [Q]; omega
  have hn := accepted_dimension frame parsed hParsed
  have hS := accepted_source_width frame parsed hParsed
  have hSize : parsed.1.1+request.source.originalInputWordWidth+
      seed.width+seed.cap.value+2 ≤ 4*Q := by
    dsimp only [request,Q]
    omega
  have hOldBound := hOld request seed.width seed.cap.value
  have hOldTop : BinaryPRGHeapCachedPrefixLifetime.envelope request
      seed.width seed.cap.value ≤ C*4^d*Q^d := by
    have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
    rw [Nat.mul_pow] at hp
    exact hOldBound.trans (hp.trans_eq (by ring))
  have hResource := request_envelope_le_existing_cached request
    seed.width seed.cap.value
  have hFrame := accepted_cached_prefix_frame_usage frame parsed hParsed seed rich
  have hFrameTop : usage (runCachedPrefixWithTrace parsed.1 seed rich).2 ≤
      BinaryPRGHeapCachedPrefixLifetime.envelope request seed.width seed.cap.value+
        2^62*(frame.length+3)^8+250 := by
    dsimp only [request] at *
    omega
  have h8Base : frame.length+3 ≤ Q := by dsimp only [Q]; omega
  have h8 : (frame.length+3)^8 ≤ Q^D :=
    (Nat.pow_le_pow_left h8Base 8).trans
      (Nat.pow_le_pow_right (by omega : 0<Q) (Nat.le_max_right d 8))
  have hd : Q^d ≤ Q^D :=
    Nat.pow_le_pow_right (by omega : 0<Q) (Nat.le_max_left d 8)
  have hOne : 1 ≤ Q^D := Nat.one_le_pow D Q hQ
  have hFirst := Nat.mul_le_mul_left (C*4^d) hd
  have hSecond := Nat.mul_le_mul_left (2^62) h8
  have hThird : 250 ≤ 250*Q^D := by nlinarith only [hOne]
  change usage (runCachedPrefixWithTrace parsed.1 seed rich).2 ≤
    (C*4^d+2^62+250)*Q^D
  calc
    _ ≤ BinaryPRGHeapCachedPrefixLifetime.envelope request seed.width seed.cap.value+
        2^62*(frame.length+3)^8+250 := hFrameTop
    _ ≤ C*4^d*Q^d+2^62*(frame.length+3)^8+250 := by omega
    _ ≤ C*4^d*Q^D+2^62*Q^D+250*Q^D := by omega
    _ = (C*4^d+2^62+250)*Q^D := by ring

theorem accepted_cached_prefix_uniform_work :
    ∃ C d : ℕ, ∀ (frame : List Bool)
      (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
      (_hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool),
      (runCachedPrefixWithTraceAndWork parsed.1 seed rich).2 ≤
        C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hResourceBound⟩ :=
    BinaryPhysicalHeapRequestLifetime.uniform_runWithTraceAndWork_bound
  obtain ⟨P,e,hPrepBound⟩ :=
    BinaryPhysicalHeapRequestLifetime.accepted_preparationAllowance_polynomial
  refine ⟨C*4^d+13000000000+P+8,max (max d 8) e,?_⟩
  intro frame parsed hParsed seed rich
  let Q := frame.length+seed.width+seed.cap.value+3
  let D := max (max d 8) e
  let resource := BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork
    seed parsed.1.2 rich
  have hQ : 1 ≤ Q := by dsimp only [Q]; omega
  have hDimension := accepted_dimension frame parsed hParsed
  have hSource := accepted_source_width frame parsed hParsed
  have hSize : parsed.1.1+
      parsed.1.2.logical.request.source.originalInputWordWidth+
      seed.width+seed.cap.value+1 ≤ 4*Q := by
    dsimp only [Q]
    omega
  have hBase : (BinaryPhysicalHeapRequestLifetime.runWithTraceAndWork
      seed parsed.1.2 rich).2 ≤ C*4^d*Q^d := by
    have h := hResourceBound seed parsed.1.2 rich
    have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
    rw [Nat.mul_pow] at hp
    exact h.trans (hp.trans_eq (by ring))
  have hLookup :=
    BinaryPhysicalNumericalReadbackLifetime.accepted_pair_lookup_allowance_polynomial
      frame parsed hParsed
  have hPrep := hPrepBound frame parsed hParsed
  have hResource : resource.2 ≤
      C*4^d*Q^d+2000000000*(frame.length+3)^7+
        P*(frame.length+3)^e := by
    dsimp only [resource]
    have hNew := BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork_le_preparationWork
      seed parsed.1.2 rich
    rw [BinaryPhysicalHeapRequestLifetime.runWithTraceAndPreparationWork_charge,
      BinaryPhysicalHeapRequestLifetime.runWithTraceAndLookupWork_charge] at hNew
    omega
  have hd : Q^d ≤ Q^D :=
    Nat.pow_le_pow_right (by omega : 0<Q) (by omega : d ≤ D)
  have h8Base : frame.length+3 ≤ Q := by dsimp only [Q]; omega
  have h8 : (frame.length+3)^8 ≤ Q^D :=
    (Nat.pow_le_pow_left h8Base 8).trans
      (Nat.pow_le_pow_right (by omega : 0<Q) (by omega : 8 ≤ D))
  have h7 : (frame.length+3)^7 ≤ Q^D :=
    (Nat.pow_le_pow_left h8Base 7).trans
      (Nat.pow_le_pow_right (by omega : 0<Q) (by omega : 7 ≤ D))
  have he : (frame.length+3)^e ≤ Q^D :=
    (Nat.pow_le_pow_left h8Base e).trans
      (Nat.pow_le_pow_right (by omega : 0<Q) (by omega : e ≤ D))
  have hOne : 1 ≤ Q^D := Nat.one_le_pow D Q hQ
  have hResourceTop : resource.2 ≤
      C*4^d*Q^D+2000000000*Q^D+P*Q^D := by
    have hFirst := Nat.mul_le_mul_left (C*4^d) hd
    have hSecond := Nat.mul_le_mul_left 2000000000 h7
    have hThird := Nat.mul_le_mul_left P he
    omega
  have hCacheTop : 11000000000*(frame.length+3)^8 ≤
      11000000000*Q^D := Nat.mul_le_mul_left _ h8
  change (runCachedPrefixWithTraceAndWork parsed.1 seed rich).2 ≤
    (C*4^d+13000000000+P+8)*Q^D
  unfold runCachedPrefixWithTraceAndWork
  dsimp only
  cases hState : resource.1.1.1 with
  | none =>
      change resource.2+4 ≤ _
      nlinarith only [hResourceTop,hOne]
  | some state =>
      have hPhysical : (BinaryPhysicalHeapRequestLifetime.runWithTrace
          seed parsed.1.2 rich).1.1 = some state := by
        rw [← BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork_erases]
        exact hState
      have hOldState : (BinaryPRGHeapRequestLifetime.run seed
          parsed.1.2.logical.request rich).1.1 = some state := by
        rw [← BinaryPhysicalHeapRequestLifetime.run_erasure]
        exact hPhysical
      have hCache := accepted_reached_cache_polynomial_work frame parsed
        hParsed rich seed state hOldState
      change (cacheWithTraceAndWork
        (BinaryPRGTerminalWork.terminalInput
          parsed.1.2.logical.request rich state)
        parsed.1.2.physical.lengthStore).2 ≤
          11000000000*(frame.length+3)^8 at hCache
      change resource.2+(cacheWithTraceAndWork
        (BinaryPRGTerminalWork.terminalInput
          parsed.1.2.logical.request rich state)
        parsed.1.2.physical.lengthStore).2+8 ≤ _
      nlinarith only [hResourceTop,hCache,hCacheTop,hOne]

theorem accepted_cached_prefix_uniform_all_prefix :
    ∃ C d : ℕ, ∀ (frame : List Bool)
      (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
      (_hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ),
      retainedHeap borrowed (runCachedPrefixWithTrace parsed.1 seed rich).2 steps ≤
          borrowed+C*(frame.length+seed.width+seed.cap.value+3)^d ∧
        framePeak ((runCachedPrefixWithTrace parsed.1 seed rich).2.take steps) ≤
          C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_cached_prefix_uniform_polynomial
  exact ⟨C,d,fun frame parsed hParsed seed rich borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _
      (hUsage frame parsed hParsed seed rich) borrowed steps⟩

theorem accepted_cached_prefix_all_prefix (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (runCachedPrefixWithTrace parsed.1 seed rich).2 steps ≤
        borrowed+cachedPrefixEnvelope frame parsed.1 seed ∧
      framePeak ((runCachedPrefixWithTrace parsed.1 seed rich).2.take steps) ≤
        cachedPrefixEnvelope frame parsed.1 seed :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_cached_prefix_usage frame parsed hParsed seed rich) borrowed steps

theorem accepted_cached_prefix_erases (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runCachedPrefixWithTrace parsed.1 seed rich).1 =
      (BinaryPRGHeapCachedPrefixLifetime.runWithTrace seed
        parsed.1.2.logical.request rich).1 := by
  rw [runCachedPrefixWithTrace,runCachedPrefixWithTraceAndWork_erases]
  unfold runCachedPrefixWithTraceReference BinaryPRGHeapCachedPrefixLifetime.runWithTrace
  dsimp only
  rw [BinaryPhysicalHeapRequestLifetime.run_erasure]
  cases hState : (BinaryPRGHeapRequestLifetime.run seed
      parsed.1.2.logical.request rich).1.1 with
  | none => rfl
  | some state =>
      simp only
      rw [accepted_cache_erases frame parsed hParsed rich state]

theorem accepted_cached_prefix_reference (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    (runCachedPrefixWithTrace parsed.1 seed rich).1 =
      BinaryPRGHeapCachedPrefixLifetime.reference seed
        parsed.1.2.logical.request rich := by
  rw [accepted_cached_prefix_erases frame parsed hParsed]
  exact BinaryPRGHeapCachedPrefixLifetime.runWithTrace_erasure _ _ _

def runSeededPrefixWithTrace
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (rich : Bool) (seed : List Bool) :
    BinaryPRGHeapSeededPrefixLifetime.Retained
      parsed.2.logical.request rich seed × Trace :=
  let prepared := BinaryWordStoreLifetime.prepareWithTrace seed
  let cached := runCachedPrefixWithTrace parsed prepared.1 rich
  (⟨prepared.1,BinaryWordStoreLifetime.prepareWithTrace_erases seed,cached.1⟩,
    wrap 32 2 [prepared.2,cached.2])

theorem accepted_seeded_output_transport (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (first second : BinarySeedLookupTree.Store)
    (h : first = second) :
    (h ▸ (runCachedPrefixWithTrace parsed.1 first rich).1) =
      BinaryPRGHeapCachedPrefixLifetime.reference second
        parsed.1.2.logical.request rich := by
  cases h
  exact accepted_cached_prefix_reference frame parsed hParsed first rich

theorem accepted_seeded_prefix_erasure (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    BinaryPRGHeapSeededPrefixLifetime.erase
      (runSeededPrefixWithTrace parsed.1 rich seed).1 =
      BinaryPRGHeapCachedPrefixLifetime.reference
        (BinarySeedLookupTree.prepare seed) parsed.1.2.logical.request rich := by
  exact accepted_seeded_output_transport frame parsed hParsed rich _ _
    (BinaryWordStoreLifetime.prepareWithTrace_erases seed)

theorem accepted_seeded_prefix_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool)
      (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
      (_hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool),
      usage (runSeededPrefixWithTrace parsed.1 rich seed).2 ≤
        C*(frame.length+seed.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_cached_prefix_uniform_polynomial
  refine ⟨C*2^d+120,d+1,?_⟩
  intro frame parsed hParsed rich seed
  let prepared := BinaryWordStoreLifetime.prepareWithTrace seed
  let X := frame.length+seed.length+3
  have hE : prepared.1 = BinarySeedLookupTree.prepare seed :=
    BinaryWordStoreLifetime.prepareWithTrace_erases seed
  have hW : prepared.1.width ≤ seed.length+1 := by
    rw [hE]
    have h := BinarySeedLookupTree.prepare_width_bound seed
    have hLog := Nat.log2_le_self seed.length
    unfold binaryWordWidth at h
    omega
  have hCap : prepared.1.cap.value = seed.length := by
    rw [hE,BinarySeedLookupTree.prepare_cap]
  have hPrep := BinaryWordStoreLifetime.prepareWithTrace_bounds seed
  have hLog : binaryWordWidth seed.length ≤ seed.length+1 := by
    have h := Nat.log2_le_self seed.length
    unfold binaryWordWidth
    omega
  have hPrepUsage : usage prepared.2 ≤ 49*seed.length+33 := by
    change listCells prepared.2+arraySlots prepared.2 ≤ _ ∧
      framePeak prepared.2 ≤ _ at hPrep
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hCached := hBound frame parsed hParsed prepared.1 rich
  have hSize : frame.length+prepared.1.width+prepared.1.cap.value+3 ≤
      2*X := by dsimp only [X]; omega
  have hScaled : usage (runCachedPrefixWithTrace parsed.1 prepared.1 rich).2 ≤
      C*2^d*X^d := by
    have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
    rw [Nat.mul_pow] at hp
    exact hCached.trans (hp.trans_eq (by ring))
  have hSmall : X^d ≤ X^(d+1) :=
    Nat.pow_le_pow_right (by dsimp only [X]; omega) (by omega)
  have hLarge : X ≤ X^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (by dsimp only [X]; omega : 0<X) (show 1 ≤ d+1 by omega)
  have hLength : seed.length ≤ X := by dsimp only [X]; omega
  have hOne : 1 ≤ X^(d+1) := Nat.one_le_pow _ X (by dsimp only [X]; omega)
  have hw := wrap_usage 32 2
    [prepared.2,(runCachedPrefixWithTrace parsed.1 prepared.1 rich).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  have hUsage : usage (runSeededPrefixWithTrace parsed.1 rich seed).2 ≤
      usage prepared.2+
        usage (runCachedPrefixWithTrace parsed.1 prepared.1 rich).2+38 := by
    unfold runSeededPrefixWithTrace
    dsimp only
    change usage (wrap 32 2
      [prepared.2,(runCachedPrefixWithTrace parsed.1 prepared.1 rich).2]) ≤ _
    omega
  have hScale := Nat.mul_le_mul_left (C*2^d) hSmall
  have hLinear := Nat.mul_le_mul_left 49 (hLength.trans hLarge)
  change usage (runSeededPrefixWithTrace parsed.1 rich seed).2 ≤
    (C*2^d+120)*X^(d+1)
  nlinarith only [hUsage,hPrepUsage,hScaled,hScale,hLinear,hOne]

theorem accepted_seeded_prefix_uniform_all_prefix :
    ∃ C d : ℕ, ∀ (frame : List Bool)
      (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
      (_hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool) (borrowed steps : ℕ),
      retainedHeap borrowed (runSeededPrefixWithTrace parsed.1 rich seed).2 steps ≤
          borrowed+C*(frame.length+seed.length+3)^d ∧
        framePeak ((runSeededPrefixWithTrace parsed.1 rich seed).2.take steps) ≤
          C*(frame.length+seed.length+3)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_seeded_prefix_uniform_polynomial
  exact ⟨C,d,fun frame parsed hParsed rich seed borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _
      (hUsage frame parsed hParsed rich seed) borrowed steps⟩

end Blotto.BinaryTerminalPhysicalRouteLifetime

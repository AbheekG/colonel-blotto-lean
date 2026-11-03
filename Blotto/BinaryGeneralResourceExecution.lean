import Blotto.BinaryGeneralResourceLattice
import Blotto.BinaryCoinWordWork

/-! Actual native resource preparation and selected updates are instrumented
with verified Boolean arithmetic work. Logical table reads/writes, list/control
operations, and a conservative full-array copy allowance remain distinct.
Fixed-D bounds are derived from the closed lattice/box invariant. No physical
allocator, reference-count uniqueness, compiler/GC, or fast backend is asserted.
The full shared-cap loop composition is a further join. -/

namespace Blotto.BinaryGeneralResourceExecution
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair BinaryGeneralResourceChoice
open BinaryGeneralResourceLattice
open scoped BigOperators

variable {n : ℕ}

structure Charge where
  booleanWork : ℕ
  reads : ℕ
  writes : ℕ
  listControl : ℕ
  copyAllowance : ℕ
  deriving Repr,DecidableEq

def Charge.add (first second : Charge) : Charge:=
  ⟨first.booleanWork+second.booleanWork,first.reads+second.reads,first.writes+second.writes,
    first.listControl+second.listControl,first.copyAllowance+second.copyAllowance⟩

-- Both comparisons execute exactly as in the retained fractional predicate.
def fractionalWithCharge (capacity resource : FixedArrayTable n SignedWord) (j : Fin n) : Bool×Charge:=
  let bid:=resource.read j
  let limit:=capacity.read j
  let first:=BinaryRationalArithmetic.lessEqual bid BinaryRationalOpcode.zero
  let second:=BinaryRationalArithmetic.lessEqual limit bid
  ((!first)&&(!second),⟨BinaryRationalArithmetic.lessEqualWork bid BinaryRationalOpcode.zero+
    BinaryRationalArithmetic.lessEqualWork limit bid,2,0,3,0⟩)

theorem fractionalWithCharge_state (capacity resource : FixedArrayTable n SignedWord) (j : Fin n) :
    (fractionalWithCharge capacity resource j).1=BinaryResourceState.fractional capacity resource j:=rfl

def scanWithCharge (capacity resource : FixedArrayTable n SignedWord) : List (Fin n)→List (Fin n)×Charge
  | []=>([],⟨0,0,0,1,0⟩)
  | j::rest=>
      let current:=fractionalWithCharge capacity resource j
      let later:=scanWithCharge capacity resource rest
      (if current.1 then j::later.1 else later.1,
        current.2.add (later.2.add ⟨0,0,0,2,0⟩))

theorem scanWithCharge_state (capacity resource : FixedArrayTable n SignedWord) (items : List (Fin n)) :
    (scanWithCharge capacity resource items).1=items.filter (BinaryResourceState.fractional capacity resource):=by
  induction items with
  | nil=>rfl
  | cons j rest ih=>
      simp only [scanWithCharge,fractionalWithCharge_state,ih,List.filter_cons]

def initialWithCharge (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) : Certified capacity×Charge:=
  let scan:=scanWithCharge capacity resource (List.finRange n)
  (⟨⟨resource,scan.1⟩,hR,
    (by rw [scanWithCharge_state]; exact (List.nodup_finRange n).filter _),
    (by intro j; rw [scanWithCharge_state]; simp [List.mem_finRange,BinaryResourceState.fractional_iff capacity resource hC hR j])⟩,
    scan.2.add ⟨0,0,0,n+1,0⟩)

theorem initialWithCharge_state (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initialWithCharge capacity resource hC hR).1=initial capacity resource hC hR:=by
  unfold initialWithCharge initial BinaryResourceState.initial
  simp only [scanWithCharge_state]

-- This counts payload copy for a conservative write that may copy every slot.
-- It is additional to logical reads/writes; no in-place uniqueness is assumed.
def tablePayload (table : FixedArrayTable n SignedWord) : ℕ:=∑ j,BinaryRationalRegisterProgram.payloadWords (table.read j)

def writeCopyAllowance (table : FixedArrayTable n SignedWord) (word : SignedWord) : ℕ:=
  2*(tablePayload table+BinaryRationalRegisterProgram.payloadWords word)

def selectWithCharge {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : Certified capacity×Charge:=
  let chosen:=choice.endpoint branch
  let first:=choice.state.state.resource.read choice.first
  let second:=choice.state.state.resource.read choice.second
  let total:=BinaryRationalOpcode.applyWithWork .add first second
  let other:=BinaryRationalOpcode.applyWithWork .sub total.1 chosen
  let next:=(choice.state.state.resource.write choice.first chosen).write choice.second other.1
  let scan:=scanWithCharge capacity next [choice.first,choice.second]
  let nextState : BinaryResourceState.State n:=⟨next,scan.1++choice.tail⟩
  have hState : nextState=(choice.select branch).state:=by
    unfold nextState BinaryGeneralResourceChoice.Choice.select BinaryResourceState.update
    dsimp only [next,scan,other,total,first,second,chosen]
    simp only [BinaryRationalOpcode.applyWithWork_state,scanWithCharge_state]
  (⟨nextState,
      (by rw [hState]; exact (choice.select branch).canonical),
      (by rw [hState]; exact (choice.select branch).nodup),
      (by rw [hState]; exact (choice.select branch).membership)⟩,
    ⟨total.2+other.2+scan.2.booleanWork,3+scan.2.reads,2,scan.2.listControl+5,
      writeCopyAllowance choice.state.state.resource chosen+
        writeCopyAllowance (choice.state.state.resource.write choice.first chosen) other.1⟩)

theorem selectWithCharge_state {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : (selectWithCharge choice branch).1=choice.select branch:=by
  unfold selectWithCharge
  dsimp only
  unfold BinaryGeneralResourceChoice.Choice.select BinaryResourceState.update
  simp only [BinaryRationalOpcode.applyWithWork_state,scanWithCharge_state]

-- The actual seven-opcode source executes once and its returned array supplies
-- the subsequent endpoint and probability reads.
def prepareWithCharge {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail) : Choice capacity hC×Charge:=
  let source:=pairSource hC state a b tail he
  let registers:=source.runWithWork
  (⟨state,a,b,tail,he,registers.1,(by
      change (BinaryRationalRegisterProgram.runWithWork RealPairProgram.code source.inputs).1=source.run
      rw [BinaryRationalRegisterProgram.runWithWork_refines]
      rfl)⟩,
    ⟨registers.2,4,0,3,source.sourcePayloadWork⟩)

theorem prepareWithCharge_state {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail) :
    (prepareWithCharge hC state a b tail he).1=Choice.prepare hC state a b tail he:=by
  unfold prepareWithCharge Choice.prepare
  simp only [BinaryRationalPairProgram.Source.runWithWork,BinaryRationalRegisterProgram.runWithWork_refines,
    BinaryRationalPairProgram.Source.run]


theorem fractionalWithCharge_bound (capacity resource : FixedArrayTable n SignedWord) (j : Fin n) (W : ℕ)
    (hW : 1≤W) (hC : width (capacity.read j)≤W) (hR : width (resource.read j)≤W) :
    (fractionalWithCharge capacity resource j).2.booleanWork≤1000*(W+1)^2:=by
  have hFirst:=BinaryRationalArithmetic.lessEqualWork_bound (resource.read j) BinaryRationalOpcode.zero
  have hSecond:=BinaryRationalArithmetic.lessEqualWork_bound (capacity.read j) (resource.read j)
  have hZero : width BinaryRationalOpcode.zero=1:=rfl
  have hp1 : BinaryRationalArithmetic.pairWidth (resource.read j) BinaryRationalOpcode.zero≤W:=max_le hR (by rw [hZero]; exact hW)
  have hp2 : BinaryRationalArithmetic.pairWidth (capacity.read j) (resource.read j)≤W:=max_le hC hR
  have hb1:=hFirst.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hp1 1) 2))
  have hb2:=hSecond.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right hp2 1) 2))
  unfold fractionalWithCharge
  dsimp only
  omega

theorem scanWithCharge_bound (capacity resource : FixedArrayTable n SignedWord) (items : List (Fin n)) (W : ℕ)
    (hW : 1≤W) (hC : ∀ j,width (capacity.read j)≤W) (hR : ∀ j,width (resource.read j)≤W) :
    (scanWithCharge capacity resource items).2.booleanWork≤ items.length*(1000*(W+1)^2) ∧
      (scanWithCharge capacity resource items).2.reads=2*items.length ∧
      (scanWithCharge capacity resource items).2.writes=0 ∧
      (scanWithCharge capacity resource items).2.listControl=5*items.length+1 ∧
      (scanWithCharge capacity resource items).2.copyAllowance=0:=by
  induction items with
  | nil=>simp [scanWithCharge]
  | cons j rest ih=>
      have hf:=fractionalWithCharge_bound capacity resource j W hW (hC j) (hR j)
      obtain ⟨hb,hr,hw,hl,hcp⟩:=ih
      unfold scanWithCharge
      dsimp only
      simp only [Charge.add,List.length_cons]
      change (fractionalWithCharge capacity resource j).2.booleanWork+(scanWithCharge capacity resource rest).2.booleanWork≤_ ∧ _
      dsimp only [fractionalWithCharge]
      constructor
      · have hSum:=Nat.add_le_add hf hb
        exact hSum.trans_eq (by ring)
      · exact ⟨by omega,by omega,by omega,by omega⟩

theorem tablePayload_bound (table : FixedArrayTable n SignedWord) (W : ℕ) (h : ∀ j,width (table.read j)≤W) :
    tablePayload table≤n*(1+2*W):=by
  unfold tablePayload
  calc
    _≤∑ _j : Fin n,(1+2*W):=Finset.sum_le_sum (fun j _=>BinaryRationalRegisterProgram.payloadWords_bound _ W (h j))
    _=_:=by simp

theorem writeCopyAllowance_bound (table : FixedArrayTable n SignedWord) (word : SignedWord) (W : ℕ)
    (h : ∀ j,width (table.read j)≤W) (hw : width word≤W) :
    writeCopyAllowance table word≤2*(n+1)*(1+2*W):=by
  have ht:=tablePayload_bound table W h
  have hp:=BinaryRationalRegisterProgram.payloadWords_bound word W hw
  unfold writeCopyAllowance
  nlinarith

theorem prepareWithCharge_lattice_bound {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state) :
    (prepareWithCharge hC state a b tail he).2.booleanWork≤
      7*(12000*(4+2*binaryWordWidth D)^3+28*(7+4*binaryWordWidth D)+4):=
  pair_work_bound hC state a b tail he D hD hLattice hUnit hs


theorem selected_endpoint_width {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D choice.state) (branch : Bool) :
    width (choice.endpoint branch)≤1+2*binaryWordWidth D:=by
  have hNext:=choice_select_invariant choice D hLattice hs branch
  have hw:=state_wordWidth (choice.select branch) D hD hUnit hNext choice.first
  have hDistinct : choice.first≠choice.second:=by
    exact choice.state.reference.realView.selected_distinct choice.head_pair
  unfold Choice.select BinaryResourceState.update at hw
  dsimp only at hw
  rw [FixedArrayTable.read_write,FixedArrayTable.read_write] at hw
  simp only [hDistinct,ite_false,ite_true] at hw
  exact hw

theorem selected_total_width {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D choice.state) :
    width (BinaryRationalOpcode.apply .add (choice.state.state.resource.read choice.first)
      (choice.state.state.resource.read choice.second))≤3+2*binaryWordWidth D:=by
  let source:=pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair
  have hc:=BinaryReflectedFourSetup.opcode_canonical .add _ _ (choice.state.canonical choice.first) (choice.state.canonical choice.second)
  have hw:=source.pair.total_wordWidth hD (pair_lattice hC choice.state _ _ _ _ D hLattice hs) (hUnit choice.first) (hUnit choice.second)
  have hv : value (BinaryRationalOpcode.apply .add (choice.state.state.resource.read choice.first)
      (choice.state.state.resource.read choice.second))=source.pair.total:=by
    rw [BinaryRationalOpcode.apply_value .add _ _ (choice.state.canonical _).1 (choice.state.canonical _).1]
    rfl
  have hb:=hc.2
  rw [hv] at hb
  exact hb.trans hw

theorem selected_other_width {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D choice.state) (branch : Bool) :
    width (BinaryRationalOpcode.apply .sub (BinaryRationalOpcode.apply .add
      (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second)) (choice.endpoint branch))≤1+2*binaryWordWidth D:=by
  have hw:=state_wordWidth (choice.select branch) D hD hUnit (choice_select_invariant choice D hLattice hs branch) choice.second
  unfold Choice.select BinaryResourceState.update at hw
  dsimp only at hw
  rw [FixedArrayTable.read_write] at hw
  simpa only [ite_true] using hw


theorem selectWithCharge_lattice_bound {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D choice.state) (branch : Bool) :
    (selectWithCharge choice branch).2.booleanWork≤24000*(4+2*binaryWordWidth D)^3+
      2000*(2+2*binaryWordWidth D)^2 ∧
      (selectWithCharge choice branch).2.reads=7 ∧
      (selectWithCharge choice branch).2.writes=2 ∧
      (selectWithCharge choice branch).2.listControl=16 ∧
      (selectWithCharge choice branch).2.copyAllowance≤4*(n+1)*(3+4*binaryWordWidth D):=by
  let W:=1+2*binaryWordWidth D
  have hW : 1≤W:=by dsimp [W]; omega
  have hu : ∀ j,value (capacity.read j)≤1:=fun j=>(hCapacityBox j).2
  have hResource : ∀ j,width (choice.state.state.resource.read j)≤W:=fun j=>state_wordWidth choice.state D hD hu hs j
  have hCapacity : ∀ j,width (capacity.read j)≤W:=fun j=>capacity_wordWidth capacity hC D hD hLattice hCapacityBox j
  have hChosen : width (choice.endpoint branch)≤W:=selected_endpoint_width choice D hD hLattice hu hs branch
  have hOther:=selected_other_width choice D hD hLattice hu hs branch
  have hTotal:=selected_total_width choice D hD hLattice hu hs
  have hA:=BinaryRationalOpcode.applyWithWork_bound .add (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second)
  have hAddPair : BinaryRationalArithmetic.pairWidth (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second)≤3+2*binaryWordWidth D:=by
    exact (max_le (hResource _) (hResource _)).trans (by dsimp [W]; omega)
  have hAB:=hA.trans (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left (Nat.add_le_add_right hAddPair 1) 3))
  have hS:=BinaryRationalOpcode.applyWithWork_bound .sub
    (BinaryRationalOpcode.applyWithWork .add (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second)).1 (choice.endpoint branch)
  have hSubPair : BinaryRationalArithmetic.pairWidth
      (BinaryRationalOpcode.applyWithWork .add (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second)).1
      (choice.endpoint branch)≤3+2*binaryWordWidth D:=by
    rw [BinaryRationalOpcode.applyWithWork_state]
    exact max_le hTotal (hChosen.trans (by dsimp [W]; omega))
  have hSB:=hS.trans (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left (Nat.add_le_add_right hSubPair 1) 3))
  have hNext : ∀ j,width (((choice.state.state.resource.write choice.first (choice.endpoint branch)).write choice.second
      (BinaryRationalOpcode.apply .sub (BinaryRationalOpcode.apply .add (choice.state.state.resource.read choice.first)
        (choice.state.state.resource.read choice.second)) (choice.endpoint branch))).read j)≤W:=by
    intro j
    rw [FixedArrayTable.read_write,FixedArrayTable.read_write]
    split
    · exact hOther
    · split
      · exact hChosen
      · exact hResource j
  have hScan:=scanWithCharge_bound capacity _ [choice.first,choice.second] W hW hCapacity hNext
  have hIntermediate : ∀ j,width ((choice.state.state.resource.write choice.first (choice.endpoint branch)).read j)≤W:=by
    intro j; rw [FixedArrayTable.read_write]; split
    · exact hChosen
    · exact hResource j
  have hCopyFirst:=writeCopyAllowance_bound choice.state.state.resource (choice.endpoint branch) W hResource hChosen
  have hCopySecond:=writeCopyAllowance_bound (choice.state.state.resource.write choice.first (choice.endpoint branch))
    (BinaryRationalOpcode.apply .sub (BinaryRationalOpcode.apply .add (choice.state.state.resource.read choice.first)
      (choice.state.state.resource.read choice.second)) (choice.endpoint branch)) W hIntermediate hOther
  unfold selectWithCharge
  dsimp only
  simp only [BinaryRationalOpcode.applyWithWork_state] at hS hSB ⊢
  obtain ⟨hScanB,hScanR,hScanW,hScanL,hScanC⟩:=hScan
  simp only [List.length_cons,List.length_nil] at hScanB hScanR hScanW hScanL hScanC
  dsimp [W] at hResource hChosen hCopyFirst hCopySecond hScanB
  constructor
  · have hAdd := Nat.add_le_add (Nat.add_le_add hAB hSB) hScanB
    exact hAdd.trans_eq (by ring)
  · exact ⟨by omega,by trivial,by omega,by nlinarith⟩


theorem initialWithCharge_lattice_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hResourceBox : ∀ j,0≤value (resource.read j) ∧ value (resource.read j)≤value (capacity.read j)) :
    (initialWithCharge capacity resource hC hR).2.booleanWork≤n*(1000*(2+2*binaryWordWidth D)^2) ∧
      (initialWithCharge capacity resource hC hR).2.reads=2*n ∧
      (initialWithCharge capacity resource hC hR).2.writes=0 ∧
      (initialWithCharge capacity resource hC hR).2.listControl=6*n+2 ∧
      (initialWithCharge capacity resource hC hR).2.copyAllowance=0:=by
  have hCapacity:=fun j=>capacity_wordWidth capacity hC D hD hLattice hCapacityBox j
  have hInitial:=initial_invariant capacity resource hC hR D hResourceLattice hResourceBox
  have hResource:=fun j=>state_wordWidth (initial capacity resource hC hR) D hD (fun j=>(hCapacityBox j).2) hInitial j
  have hb:=scanWithCharge_bound capacity resource (List.finRange n) (1+2*binaryWordWidth D) (by omega) hCapacity hResource
  simp only [List.length_finRange] at hb
  unfold initialWithCharge
  dsimp only
  simp only [Charge.add]
  obtain ⟨hw,hr,hwr,hl,hc⟩:=hb
  have hWidth : 1+2*binaryWordWidth D+1=2+2*binaryWordWidth D:=by omega
  rw [hWidth] at hw
  exact ⟨hw,by omega,by omega,by omega,by omega⟩

theorem prepareWithCharge_copy_bound {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D state) :
    (prepareWithCharge hC state a b tail he).2.copyAllowance≤8*(3+4*binaryWordWidth D)+4:=by
  let W:=1+2*binaryWordWidth D
  have hL:=fun j=>capacity_wordWidth capacity hC D hD hLattice hCapacityBox j
  have hR:=fun j=>state_wordWidth state D hD (fun j=>(hCapacityBox j).2) hs j
  have p1:=BinaryRationalRegisterProgram.payloadWords_bound (capacity.read a) W (hL a)
  have p2:=BinaryRationalRegisterProgram.payloadWords_bound (capacity.read b) W (hL b)
  have p3:=BinaryRationalRegisterProgram.payloadWords_bound (state.state.resource.read a) W (hR a)
  have p4:=BinaryRationalRegisterProgram.payloadWords_bound (state.state.resource.read b) W (hR b)
  unfold prepareWithCharge BinaryRationalPairProgram.Source.sourcePayloadWork pairSource
  dsimp only
  dsimp [W] at p1 p2 p3 p4
  nlinarith

end Blotto.BinaryGeneralResourceExecution

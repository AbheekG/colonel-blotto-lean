import Blotto.BinaryGeneralResourceExecution

/-! The instrumented shared-cap resource loop executes actual cached pair
preparation and selected writes. Every coin body retains fixed Boolean words;
result, exhaustion and absolute reader position refine the native runner.
Boolean callback work and conservative table-copy work remain separate. -/

namespace Blotto.BinaryGeneralResourceRunWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair BinaryGeneralResourceChoice
open BinaryGeneralResourceRun BinaryGeneralResourceExecution BinaryGeneralResourceLattice
variable {n : ℕ}

-- Padding traverses each input spine and creates only the missing suffixes.
def paddingCharge {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : Charge:=
  ⟨12*(max choice.probability.numerator.length choice.probability.denominator.length+1),2,0,2,0⟩

def prepareStep {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : Preparation capacity hC×Charge:=
  match he : state.state.active with
  | a::b::tail=>
      let result:=prepareWithCharge hC state a b tail he
      (.ask result.1,result.2.add ⟨0,0,0,1,0⟩)
  | _=>(.done state,⟨0,0,0,1,0⟩)

theorem prepareStep_state {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : (prepareStep hC state).1=BinaryGeneralResourceChoice.prepare capacity hC state:=by
  cases state with
  | mk data canonical nodup membership=>
      cases data with
      | mk resource active=>
          cases active with
          | nil=>rfl
          | cons a rest=>
              cases rest with
              | nil=>rfl
              | cons b tail=>
                  dsimp only [prepareStep,BinaryGeneralResourceChoice.prepare]
                  rw [prepareWithCharge_state]

def runIndexed {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos≤N) :
    (Option (Certified capacity)×ℕ)×Charge:=
  match cursor with
  | .ready state=>
      let prepared:=prepareStep hC state
      match hs : prepared.1 with
      | .done result=>((some result,pos),prepared.2)
      | .ask choice=>
          let later:=runIndexed N bits (pending choice) pos hp
          (later.1,prepared.2.add ((paddingCharge choice).add later.2))
  | .coin choice a b hb hab=>
      let body : Charge:=⟨FixedWordCoin.bodyWork a b,0,0,2,0⟩
      if hz : a.isZero=true then
        let selected:=selectWithCharge choice false
        let later:=runIndexed N bits (.ready selected.1 : Cursor capacity hC) pos hp
        (later.1,body.add (selected.2.add later.2))
      else if he : a.same b=true then
        let selected:=selectWithCharge choice true
        let later:=runIndexed N bits (.ready selected.1 : Cursor capacity hC) pos hp
        (later.1,body.add (selected.2.add later.2))
      else if hRead : pos<N then
        let bit:=bits ⟨pos,hRead⟩
        let next:=a.coinStep b
        have hlt : a.value<b.value:=lt_of_le_of_ne hab (fun h=>he ((a.same_value b).mpr h))
        if bit=next.1 then
          let later:=runIndexed N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
          (later.1,body.add ((⟨0,1,0,2,0⟩ : Charge).add later.2))
        else
          let selected:=selectWithCharge choice (!bit)
          let later:=runIndexed N bits (.ready selected.1 : Cursor capacity hC) (pos+1) (by omega)
          (later.1,body.add ((⟨0,1,0,2,0⟩ : Charge).add (selected.2.add later.2)))
      else ((none,pos),body)
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state:=by
      have hh:=prepareStep_state hC state
      change (prepareStep hC state).1=.ask choice at hs
      rw [hs] at hh
      unfold BinaryGeneralResourceChoice.prepare at hh
      split at hh
      · cases Preparation.ask.inj hh; rfl
      · cases hh
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  · apply Prod.Lex.right
    rw [selectWithCharge_state]
    exact selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    rw [selectWithCharge_state]
    exact selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega


theorem runIndexed_state {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos≤N) :
    (runIndexed N bits cursor pos hp).1=BinaryGeneralResourceRun.runIndexed N bits cursor pos hp:=by
  cases cursor with
  | ready state=>
      conv_lhs=>unfold runIndexed
      conv_rhs=>unfold BinaryGeneralResourceRun.runIndexed
      rw [←prepareStep_state hC state]
      dsimp only
      cases hs : (prepareStep hC state).1 with
      | done result=>rfl
      | ask choice=>
          exact runIndexed_state N bits (pending choice) pos hp
  | coin choice a b hb hab=>
      conv_lhs=>unfold runIndexed
      conv_rhs=>unfold BinaryGeneralResourceRun.runIndexed
      dsimp only
      split
      · rw [selectWithCharge_state]
        exact runIndexed_state N bits (.ready (choice.select false) : Cursor capacity hC) pos hp
      · split
        · rw [selectWithCharge_state]
          exact runIndexed_state N bits (.ready (choice.select true) : Cursor capacity hC) pos hp
        · split
          · split
            · exact runIndexed_state N bits _ (pos+1) _
            · rw [selectWithCharge_state]
              exact runIndexed_state N bits _ (pos+1) _
          · rfl
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state:=by
      have hh:=prepareStep_state hC state
      rw [hs] at hh
      unfold BinaryGeneralResourceChoice.prepare at hh
      split at hh
      · cases Preparation.ask.inj hh; rfl
      · cases hh
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  all_goals try (apply Prod.Lex.right; exact selected_rank_lt choice a b hb hab _)
  all_goals apply Prod.Lex.left
  all_goals omega



-- Componentwise bounds keep arithmetic, table accesses, control and copy
-- allowances distinct throughout the actual execution proof.
def ChargeLE (first second : Charge) : Prop:=
  first.booleanWork≤second.booleanWork ∧ first.reads≤second.reads ∧
    first.writes≤second.writes ∧ first.listControl≤second.listControl ∧ first.copyAllowance≤second.copyAllowance

def scale (k : ℕ) (charge : Charge) : Charge:=
  ⟨k*charge.booleanWork,k*charge.reads,k*charge.writes,k*charge.listControl,k*charge.copyAllowance⟩

def terminalAllowance : Charge:=⟨0,0,0,1,0⟩

def pairAllowance (D : ℕ) : Charge:=
  ⟨7*(12000*(4+2*binaryWordWidth D)^3+28*(7+4*binaryWordWidth D)+4),4,0,4,
    8*(3+4*binaryWordWidth D)+4⟩

def padAllowance (D : ℕ) : Charge:=⟨12*(2+2*binaryWordWidth D),2,0,2,0⟩

def selectAllowance (n D : ℕ) : Charge:=
  ⟨24000*(4+2*binaryWordWidth D)^3+2000*(2+2*binaryWordWidth D)^2,7,2,16,
    4*(n+1)*(3+4*binaryWordWidth D)⟩

-- Charge one potential body read even when a zero/one/exhaustion body uses
-- none; selected successors and remaining bits pay these conservative labels.
def bodyAllowance (D : ℕ) : Charge:=⟨24*(1+2*binaryWordWidth D)+28,1,0,4,0⟩

def pairTotalAllowance (n D : ℕ) : Charge:=
  (pairAllowance D).add ((padAllowance D).add ((selectAllowance n D).add (bodyAllowance D)))

def cursorAllowance {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D remaining : ℕ) : Cursor capacity hC→Charge
  | .ready state=>(scale (state.state.active.length-1) (pairTotalAllowance n D)).add
      ((scale remaining (bodyAllowance D)).add terminalAllowance)
  | .coin choice _ _ _ _=>(scale (choice.state.state.active.length-2) (pairTotalAllowance n D)).add
      ((selectAllowance n D).add ((scale (remaining+1) (bodyAllowance D)).add terminalAllowance))

def BoundedCursor {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D : ℕ) : Cursor capacity hC→Prop
  | .ready state=>StateInvariant capacity D state
  | .coin (w:=w) choice _ _ _ _=>StateInvariant capacity D choice.state ∧ w≤1+2*binaryWordWidth D

theorem chargeLE_refl (charge : Charge) : ChargeLE charge charge:=⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩
theorem chargeLE_trans {first second third : Charge} (h : ChargeLE first second) (g : ChargeLE second third) : ChargeLE first third:=
  ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.1.trans g.2.2.1,h.2.2.2.1.trans g.2.2.2.1,h.2.2.2.2.trans g.2.2.2.2⟩
theorem chargeLE_add {first second upper lower : Charge} (h : ChargeLE first upper) (g : ChargeLE second lower) :
    ChargeLE (first.add second) (upper.add lower):=by
  exact ⟨Nat.add_le_add h.1 g.1,Nat.add_le_add h.2.1 g.2.1,Nat.add_le_add h.2.2.1 g.2.2.1,
    Nat.add_le_add h.2.2.2.1 g.2.2.2.1,Nat.add_le_add h.2.2.2.2 g.2.2.2.2⟩

theorem prepareWithCharge_allowance {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D state) :
    ChargeLE ((prepareWithCharge hC state a b tail he).2.add ⟨0,0,0,1,0⟩) (pairAllowance D):=by
  have hp:=prepareWithCharge_lattice_bound hC state a b tail he D hD hLattice (fun j=>(hCapacityBox j).2) hs
  have hc:=prepareWithCharge_copy_bound hC state a b tail he D hD hLattice hCapacityBox hs
  unfold ChargeLE
  refine ⟨?_,?_,?_,?_,?_⟩
  · change (prepareWithCharge hC state a b tail he).2.booleanWork+0≤_
    rw [Nat.add_zero]
    exact hp
  · change 4≤4
    exact le_rfl
  · change 0≤0
    exact le_rfl
  · change 4≤4
    exact le_rfl
  · change (prepareWithCharge hC state a b tail he).2.copyAllowance+0≤_
    rw [Nat.add_zero]
    exact hc

theorem prepareStep_charge {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (D : ℕ) (hD : 0<D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D state) :
    match (prepareStep hC state).1 with
    | .done _=>ChargeLE (prepareStep hC state).2 terminalAllowance
    | .ask choice=>choice.state=state ∧ 2≤state.state.active.length ∧ ChargeLE (prepareStep hC state).2 (pairAllowance D):=by
  cases state with
  | mk data canonical nodup membership=>
      cases data with
      | mk resource active=>
          cases active with
          | nil=>exact chargeLE_refl terminalAllowance
          | cons a rest=>
              cases rest with
              | nil=>exact chargeLE_refl terminalAllowance
              | cons b tail=>
                  let state : Certified capacity:=⟨⟨resource,a::b::tail⟩,canonical,nodup,membership⟩
                  have hc:=prepareWithCharge_allowance hC state a b tail rfl D hD hLattice hCapacityBox hs
                  change (prepareWithCharge hC state a b tail rfl).1.state=state ∧
                    2≤state.state.active.length ∧ ChargeLE ((prepareWithCharge hC state a b tail rfl).2.add ⟨0,0,0,1,0⟩) (pairAllowance D)
                  exact ⟨rfl,by simp [state],hc⟩

theorem padding_charge {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D choice.state) : ChargeLE (paddingCharge choice) (padAllowance D):=by
  have hw:=prepared_coin_buffer_width choice D hD hLattice (fun j=>(hCapacityBox j).2) hs
  unfold ChargeLE paddingCharge padAllowance
  dsimp only
  exact ⟨by omega,le_rfl,le_rfl,le_rfl,le_rfl⟩

theorem selected_charge {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D choice.state) (branch : Bool) :
    ChargeLE (selectWithCharge choice branch).2 (selectAllowance n D):=by
  obtain ⟨hb,hr,hw,hl,hc⟩:=selectWithCharge_lattice_bound choice D hD hLattice hCapacityBox hs branch
  exact ⟨hb,hr.le,hw.le,hl.le,hc⟩

theorem pending_bounded {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hs : StateInvariant capacity D choice.state) : BoundedCursor D (pending choice):=by
  change StateInvariant capacity D choice.state ∧ _
  exact ⟨hs,prepared_coin_buffer_width choice D hD hLattice (fun j=>(hCapacityBox j).2) hs⟩

theorem body_charge {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    {w : ℕ} (_choice : Choice capacity hC) (a b : FixedBinaryWord w) (D : ℕ)
    (hw : w≤1+2*binaryWordWidth D) :
    ChargeLE (⟨FixedWordCoin.bodyWork a b,0,0,2,0⟩ : Charge) (bodyAllowance D):=by
  have hb:=FixedWordCoin.bodyWork_bound a b
  rw [FixedWordCoin.bodyAllowance_eq] at hb
  unfold ChargeLE bodyAllowance
  dsimp only
  exact ⟨hb.trans (by omega),by omega,le_rfl,by omega,le_rfl⟩


theorem scale_mono (charge : Charge) {first second : ℕ} (h : first≤second) :
    ChargeLE (scale first charge) (scale second charge):=
  ⟨Nat.mul_le_mul_right _ h,Nat.mul_le_mul_right _ h,Nat.mul_le_mul_right _ h,Nat.mul_le_mul_right _ h,Nat.mul_le_mul_right _ h⟩

theorem terminal_credit {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D remaining : ℕ) (state : Certified capacity) : ChargeLE terminalAllowance (cursorAllowance D remaining (.ready state : Cursor capacity hC)):=by
  unfold ChargeLE cursorAllowance Charge.add scale terminalAllowance
  dsimp only
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

theorem prepared_credit {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D remaining : ℕ) (state : Certified capacity) (choice : Choice capacity hC)
    (hState : choice.state=state) (hLength : 2≤state.state.active.length) :
    ChargeLE ((pairAllowance D).add ((padAllowance D).add (cursorAllowance D remaining (pending choice))))
      (cursorAllowance D remaining (.ready state : Cursor capacity hC)):=by
  have he : state.state.active.length-1=(state.state.active.length-2)+1:=by omega
  unfold ChargeLE cursorAllowance pending
  dsimp only [Charge.add,scale]
  rw [hState,he]
  unfold pairTotalAllowance
  dsimp only [Charge.add,scale]
  exact ⟨by ring_nf; rfl,by ring_nf; rfl,by ring_nf; rfl,by ring_nf; rfl,by ring_nf; rfl⟩

theorem selected_credit {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    {w : ℕ} (D remaining : ℕ) (choice : Choice capacity hC) (a b : FixedBinaryWord w) (hb : 0<b.value) (hab : a.value≤b.value)
    (branch : Bool) :
    ChargeLE ((bodyAllowance D).add ((selectAllowance n D).add
      (cursorAllowance D remaining (.ready (selectWithCharge choice branch).1 : Cursor capacity hC))))
      (cursorAllowance D remaining (.coin choice a b hb hab)):=by
  rw [selectWithCharge_state]
  have hProgress:=choice.select_progress branch
  have hLength : 2≤choice.state.state.active.length:=by rw [choice.head_pair]; simp
  have hCount : (choice.select branch).state.active.length-1≤choice.state.state.active.length-2:=by omega
  have hScale:=scale_mono (pairTotalAllowance n D) hCount
  unfold ChargeLE cursorAllowance at *
  dsimp only [Charge.add,scale] at *
  obtain ⟨hBool,hRead,hWrite,hList,hCopy⟩:=hScale
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem body_read_charge {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    {w : ℕ} (_choice : Choice capacity hC) (a b : FixedBinaryWord w) (D : ℕ) (hw : w≤1+2*binaryWordWidth D) :
    ChargeLE ((⟨FixedWordCoin.bodyWork a b,0,0,2,0⟩ : Charge).add ⟨0,1,0,2,0⟩) (bodyAllowance D):=by
  have hb:=FixedWordCoin.bodyWork_bound a b
  rw [FixedWordCoin.bodyAllowance_eq] at hb
  unfold ChargeLE bodyAllowance
  dsimp only [Charge.add]
  exact ⟨hb.trans (by omega),le_rfl,le_rfl,le_rfl,le_rfl⟩

theorem residual_credit {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    {w : ℕ} (D remaining : ℕ) (hRemaining : 0<remaining) (choice : Choice capacity hC)
    (a b a' : FixedBinaryWord w) (hb : 0<b.value) (hab : a.value≤b.value) (hab' : a'.value≤b.value) :
    ChargeLE ((bodyAllowance D).add (cursorAllowance D (remaining-1) (.coin choice a' b hb hab')))
      (cursorAllowance D remaining (.coin choice a b hb hab)):=by
  have he : remaining-1+1=remaining:=by omega
  unfold ChargeLE cursorAllowance
  dsimp only [Charge.add,scale]
  rw [he]
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem selected_read_credit {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    {w : ℕ} (D remaining : ℕ) (_hRemaining : 0<remaining) (choice : Choice capacity hC)
    (a b : FixedBinaryWord w) (hb : 0<b.value) (hab : a.value≤b.value) (branch : Bool) :
    ChargeLE ((bodyAllowance D).add ((selectAllowance n D).add
      (cursorAllowance D (remaining-1) (.ready (selectWithCharge choice branch).1 : Cursor capacity hC))))
      (cursorAllowance D remaining (.coin choice a b hb hab)):=by
  have h:=selected_credit D (remaining-1) choice a b hb hab branch
  have hm : ChargeLE (cursorAllowance D (remaining-1) (.coin choice a b hb hab))
      (cursorAllowance D remaining (.coin choice a b hb hab)):=by
    unfold ChargeLE cursorAllowance
    dsimp only [Charge.add,scale]
    have hp:=Nat.sub_le remaining 1
    refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith
  exact chargeLE_trans h hm

theorem exhausted_credit {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    {w : ℕ} (D remaining : ℕ) (choice : Choice capacity hC) (a b : FixedBinaryWord w) (hb : 0<b.value) (hab : a.value≤b.value) :
    ChargeLE (bodyAllowance D) (cursorAllowance D remaining (.coin choice a b hb hab)):=by
  unfold ChargeLE cursorAllowance
  dsimp only [Charge.add,scale]
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩


theorem runIndexed_charge_bound {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos≤N)
    (hs : BoundedCursor D cursor) :
    ChargeLE (runIndexed N bits cursor pos hp).2 (cursorAllowance D (N-pos) cursor):=by
  cases cursor with
  | ready state=>
      unfold runIndexed
      dsimp only
      have hPrepare:=prepareStep_charge hC state D hD hLattice hCapacityBox hs
      cases hPrep : (prepareStep hC state).1 with
      | done result=>
          rw [hPrep] at hPrepare
          exact chargeLE_trans hPrepare (terminal_credit D (N-pos) state)
      | ask choice=>
          rw [hPrep] at hPrepare
          obtain ⟨hState,hLength,hCharge⟩:=hPrepare
          have hChoice : StateInvariant capacity D choice.state:=by rw [hState]; exact hs
          have hPending:=pending_bounded choice D hD hLattice hCapacityBox hChoice
          have ih:=runIndexed_charge_bound D hD hLattice hCapacityBox N bits (pending choice) pos hp hPending
          have hPadding:=padding_charge choice D hD hLattice hCapacityBox hChoice
          exact chargeLE_trans (chargeLE_add hCharge (chargeLE_add hPadding ih)) (prepared_credit D (N-pos) state choice hState hLength)
  | coin choice a b hb hab=>
      unfold runIndexed
      dsimp only
      have hBody:=body_charge choice a b D hs.2
      have hReadBody:=body_read_charge choice a b D hs.2
      have hSelected (branch : Bool) : BoundedCursor D (.ready (selectWithCharge choice branch).1 : Cursor capacity hC):=by
        rw [selectWithCharge_state]
        exact choice_select_invariant choice D hLattice hs.1 branch
      split
      · have ih:=runIndexed_charge_bound D hD hLattice hCapacityBox N bits
          (.ready (selectWithCharge choice false).1 : Cursor capacity hC) pos hp (hSelected false)
        have hSelect:=selected_charge choice D hD hLattice hCapacityBox hs.1 false
        exact chargeLE_trans (chargeLE_add hBody (chargeLE_add hSelect ih)) (selected_credit D (N-pos) choice a b hb hab false)
      · split
        · have ih:=runIndexed_charge_bound D hD hLattice hCapacityBox N bits
            (.ready (selectWithCharge choice true).1 : Cursor capacity hC) pos hp (hSelected true)
          have hSelect:=selected_charge choice D hD hLattice hCapacityBox hs.1 true
          exact chargeLE_trans (chargeLE_add hBody (chargeLE_add hSelect ih)) (selected_credit D (N-pos) choice a b hb hab true)
        · split
          · rename_i hRead
            have hlt : a.value<b.value:=lt_of_le_of_ne hab (fun h=>by
              have hSame : a.same b=true:=(a.same_value b).mpr h
              contradiction)
            have hRemaining : 0<N-pos:=by omega
            have hSubtract : N-(pos+1)=(N-pos)-1:=by omega
            split
            · have ih:=runIndexed_charge_bound D hD hLattice hCapacityBox N bits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le : Cursor capacity hC) (pos+1) (by omega) ⟨hs.1,hs.2⟩
              have hCredit:=residual_credit D (N-pos) hRemaining choice a b (a.coinStep b).2 hb hab (a.coinStep_normalized b hlt).le
              rw [←hSubtract] at hCredit
              have h:=chargeLE_trans (chargeLE_add hReadBody ih) hCredit
              simpa only [ChargeLE,Charge.add,Nat.add_assoc] using h
            · have ih:=runIndexed_charge_bound D hD hLattice hCapacityBox N bits
                (.ready (selectWithCharge choice (!bits ⟨pos,hRead⟩)).1 : Cursor capacity hC) (pos+1) (by omega) (hSelected _)
              have hSelect:=selected_charge choice D hD hLattice hCapacityBox hs.1 (!bits ⟨pos,hRead⟩)
              have hCredit:=selected_read_credit D (N-pos) hRemaining choice a b hb hab (!bits ⟨pos,hRead⟩)
              rw [←hSubtract] at hCredit
              have h:=chargeLE_trans (chargeLE_add hReadBody (chargeLE_add hSelect ih)) hCredit
              simpa only [ChargeLE,Charge.add,Nat.add_assoc] using h
          · exact chargeLE_trans hBody (exhausted_credit D (N-pos) choice a b hb hab)
termination_by (N-pos,cursor.rank)
decreasing_by
  all_goals subst cursor
  · apply Prod.Lex.right
    have hh:=prepareStep_state hC state
    rw [hPrep] at hh
    unfold BinaryGeneralResourceChoice.prepare at hh
    have hState : choice.state=state:=by
      split at hh
      · cases Preparation.ask.inj hh; rfl
      · cases hh
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  all_goals try (apply Prod.Lex.right; rw [selectWithCharge_state]; exact selected_rank_lt choice a b hb hab _)
  all_goals apply Prod.Lex.left
  all_goals omega


def run {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) : (Option (Certified capacity)×ℕ)×Charge:=
  runIndexed N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)

theorem run_state {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) :
    (run hC N state bits).1=BinaryGeneralResourceRun.run hC N state bits:=
  runIndexed_state N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)

theorem run_lattice_bound {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) (hs : StateInvariant capacity D state) :
    ChargeLE (run hC N state bits).2 ((scale (n-1) (pairTotalAllowance n D)).add
      ((scale N (bodyAllowance D)).add terminalAllowance)):=by
  have h:=runIndexed_charge_bound D hD hLattice hCapacityBox N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N) hs
  change ChargeLE (run hC N state bits).2 ((scale (state.state.active.length-1) (pairTotalAllowance n D)).add
    ((scale N (bodyAllowance D)).add terminalAllowance)) at h
  have hm:=scale_mono (pairTotalAllowance n D) (Nat.sub_le_sub_right (active_length_le state) 1)
  exact chargeLE_trans h (chargeLE_add hm (chargeLE_refl _))

-- Explicit totals count the actual Boolean bodies and local opcode work.
-- Conservative copies stay in their own field and may be quadratic in n.
theorem run_explicit_bound {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) (hs : StateInvariant capacity D state) :
    (run hC N state bits).2.booleanWork≤(n-1)*((pairAllowance D).booleanWork+(padAllowance D).booleanWork+
      (selectAllowance n D).booleanWork+(bodyAllowance D).booleanWork)+N*(bodyAllowance D).booleanWork ∧
    (run hC N state bits).2.reads≤14*(n-1)+N ∧
    (run hC N state bits).2.writes≤2*(n-1) ∧
    (run hC N state bits).2.listControl≤26*(n-1)+4*N+1 ∧
    (run hC N state bits).2.copyAllowance≤(n-1)*(8*(3+4*binaryWordWidth D)+4+4*(n+1)*(3+4*binaryWordWidth D)):=by
  have h:=run_lattice_bound hC D hD hLattice hCapacityBox N state bits hs
  unfold ChargeLE pairTotalAllowance scale Charge.add pairAllowance padAllowance selectAllowance bodyAllowance terminalAllowance at h
  unfold pairAllowance padAllowance selectAllowance bodyAllowance at ⊢
  dsimp only at h ⊢
  norm_num only at h ⊢
  simpa only [Nat.add_assoc,Nat.mul_comm,Nat.mul_one,Nat.mul_zero,Nat.add_zero,Nat.zero_add] using h

def initialRun (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (N : ℕ) (bits : Fin N→Bool) : (Option (Certified capacity)×ℕ)×Charge:=
  let initial:=initialWithCharge capacity resource hC hR
  let later:=run hC N initial.1 bits
  (later.1,initial.2.add later.2)

theorem initialRun_state (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (N : ℕ) (bits : Fin N→Bool) :
    (initialRun capacity resource hC hR N bits).1=BinaryGeneralResourceRun.initialRun capacity resource hC hR N bits:=by
  unfold initialRun
  dsimp only
  rw [run_state,initialWithCharge_state]
  rfl

theorem initialRun_lattice_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hResourceBox : ∀ j,0≤value (resource.read j) ∧ value (resource.read j)≤value (capacity.read j))
    (N : ℕ) (bits : Fin N→Bool) :
    ChargeLE (initialRun capacity resource hC hR N bits).2
      ((⟨n*(1000*(2+2*binaryWordWidth D)^2),2*n,0,6*n+2,0⟩ : Charge).add
        ((scale (n-1) (pairTotalAllowance n D)).add ((scale N (bodyAllowance D)).add terminalAllowance))):=by
  have hi:=initialWithCharge_lattice_bound capacity resource hC hR D hD hLattice hResourceLattice hCapacityBox hResourceBox
  have hs : StateInvariant capacity D (initialWithCharge capacity resource hC hR).1:=by
    rw [initialWithCharge_state]
    exact initial_invariant capacity resource hC hR D hResourceLattice hResourceBox
  have hr:=run_lattice_bound hC D hD hLattice hCapacityBox N (initialWithCharge capacity resource hC hR).1 bits hs
  have hInit : ChargeLE (initialWithCharge capacity resource hC hR).2
      ⟨n*(1000*(2+2*binaryWordWidth D)^2),2*n,0,6*n+2,0⟩:=
    ⟨hi.1,hi.2.1.le,hi.2.2.1.le,hi.2.2.2.1.le,hi.2.2.2.2.le⟩
  exact chargeLE_add hInit hr

theorem pairTotal_boolean_cubic (n D : ℕ) :
    (pairTotalAllowance n D).booleanWork≤7000000*(binaryWordWidth D+1)^3:=by
  unfold pairTotalAllowance pairAllowance padAllowance selectAllowance bodyAllowance
  dsimp only [Charge.add]
  nlinarith [Nat.zero_le (binaryWordWidth D),Nat.zero_le ((binaryWordWidth D)^2),Nat.zero_le ((binaryWordWidth D)^3)]

theorem body_boolean_linear (D : ℕ) : (bodyAllowance D).booleanWork≤52*(binaryWordWidth D+1):=by
  unfold bodyAllowance
  dsimp only
  omega

theorem initialRun_boolean_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hResourceBox : ∀ j,0≤value (resource.read j) ∧ value (resource.read j)≤value (capacity.read j))
    (N : ℕ) (bits : Fin N→Bool) :
    (initialRun capacity resource hC hR N bits).2.booleanWork≤
      7100000*n*(binaryWordWidth D+1)^3+52*N*(binaryWordWidth D+1):=by
  have h:= (initialRun_lattice_bound capacity resource hC hR D hD hLattice hResourceLattice hCapacityBox hResourceBox N bits).1
  dsimp only [Charge.add,scale,terminalAllowance] at h
  have hp:=Nat.mul_le_mul_left (n-1) (pairTotal_boolean_cubic n D)
  have hb:=Nat.mul_le_mul_left N (body_boolean_linear D)
  have hn : n-1≤n:=Nat.sub_le _ _
  have hP:=hp.trans (Nat.mul_le_mul_right (7000000*(binaryWordWidth D+1)^3) hn)
  have hInit : 1000*(2+2*binaryWordWidth D)^2≤100000*(binaryWordWidth D+1)^3:=by
    nlinarith [Nat.zero_le (binaryWordWidth D),Nat.zero_le ((binaryWordWidth D)^2),Nat.zero_le ((binaryWordWidth D)^3)]
  have hi:=Nat.mul_le_mul_left n hInit
  nlinarith

theorem initialRun_access_copy_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hCapacityBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1)
    (hResourceBox : ∀ j,0≤value (resource.read j) ∧ value (resource.read j)≤value (capacity.read j))
    (N : ℕ) (bits : Fin N→Bool) :
    (initialRun capacity resource hC hR N bits).2.reads≤2*n+14*(n-1)+N ∧
    (initialRun capacity resource hC hR N bits).2.writes≤2*(n-1) ∧
    (initialRun capacity resource hC hR N bits).2.listControl≤6*n+3+26*(n-1)+4*N ∧
    (initialRun capacity resource hC hR N bits).2.copyAllowance≤
      (n-1)*(8*(3+4*binaryWordWidth D)+4+4*(n+1)*(3+4*binaryWordWidth D)):=by
  have h:=initialRun_lattice_bound capacity resource hC hR D hD hLattice hResourceLattice hCapacityBox hResourceBox N bits
  unfold ChargeLE pairTotalAllowance scale Charge.add pairAllowance padAllowance selectAllowance bodyAllowance terminalAllowance at h
  dsimp only at h
  obtain ⟨_,hr,hw,hl,hc⟩:=h
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩


theorem initialRun_refines (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (N : ℕ) (bits : Fin N→Bool) :
    BinaryGeneralResourceRun.mapResult (initialRun capacity resource hC hR N bits).1=
      (rationalResourceMachine (fun j=>value (capacity.read j))).run N
        (.ready (RationalActiveResources.initial (fun j=>value (capacity.read j)) (fun j=>value (resource.read j)))) bits:=by
  rw [initialRun_state]
  exact BinaryGeneralResourceRun.initialRun_refines capacity resource hC hR N bits

-- The prior exact native request observer follows these same preparation and
-- selected-state branches; its n-1 bound is retained rather than an assumption.
theorem requests_le_dimension {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) :
    BinaryGeneralResourceRun.requests N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)≤n-1:=
  BinaryGeneralResourceRun.run_requests_le_dimension hC N state bits

theorem initialRun_bitReads_le (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (N : ℕ) (bits : Fin N→Bool) :
    (initialRun capacity resource hC hR N bits).1.2≤N:=by
  rw [initialRun_state]
  rw [BinaryGeneralResourceRun.initialRun,BinaryGeneralResourceRun.run_position]
  exact WordStateMachine.run_bits_le _ _ _ _

theorem normalized_initialRun_boolean_bound (source : RationalPRGInput n) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,value (capacity.read j)=source.lengths j)
    (hInitial : (∀ j,value (resource.read j)=source.richInitial j) ∨ (∀ j,value (resource.read j)=source.poorInitial j))
    (N : ℕ) (bits : Fin N→Bool) :
    (initialRun capacity resource hC hR N bits).2.booleanWork≤
      7100000*n*(source.inputWordWidth+2)^3+52*N*(source.inputWordWidth+2):=by
  have hL : ∀ j,OnRationalLattice source.latticeDenominator (value (capacity.read j)):=by
    intro j; rw [hCapacity j]; exact source.lengths_on_lattice j
  have hRL : ∀ j,OnRationalLattice source.latticeDenominator (value (resource.read j)):=by
    intro j
    rcases hInitial with hi|hi
    · rw [hi j]; exact source.richInitial_on_lattice j
    · rw [hi j]; exact source.poorInitial_on_lattice j
  have hCB : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1:=by
    intro j; rw [hCapacity j]
    exact ⟨(mul_pos (by norm_num) (source.positive j)).le,(source.small_fields j).trans source.b_le⟩
  have hRB : ∀ j,0≤value (resource.read j) ∧ value (resource.read j)≤value (capacity.read j):=by
    intro j; rw [hCapacity j]
    rcases hInitial with hi|hi
    · rw [hi j]
      exact ⟨(mul_pos (by norm_num) (source.positive j)).le,le_rfl⟩
    · rw [hi j]
      have hl : 0≤source.lengths j:=(mul_pos (by norm_num) (source.positive j)).le
      exact ⟨mul_nonneg source.b_pos.le hl,(mul_le_mul_of_nonneg_right source.b_le hl).trans_eq (one_mul _)⟩
  have h:=initialRun_boolean_bound capacity resource hC hR source.latticeDenominator source.latticeDenominator_pos hL hRL hCB hRB N bits
  have hWidth : binaryWordWidth source.latticeDenominator+1≤source.inputWordWidth+2:=by
    have hd:=source.latticeDenominator_wordWidth
    omega
  have hCube:=Nat.mul_le_mul_left (7100000*n) (Nat.pow_le_pow_left hWidth 3)
  have hBody:=Nat.mul_le_mul_left (52*N) hWidth
  exact h.trans (Nat.add_le_add hCube hBody)

theorem validLotto_initialRun_boolean_bound (input : BinaryLottoResourceInput.Input n)
    (source : RationalLottoResourceSystem n) (hC : input.Canonical) (hr : input.Refines source)
    (D : ℕ) (hD : 0<D) (hBunit : source.B≤1)
    (hLength : ∀ j,OnRationalLattice D (source.length j)) (hInitial : ∀ j,OnRationalLattice D (source.initial j))
    (N : ℕ) (bits : Fin N→Bool) :
    (initialRun input.length input.resource hC.2.1 hC.2.2 N bits).2.booleanWork≤
      7100000*n*(binaryWordWidth D+1)^3+52*N*(binaryWordWidth D+1):=by
  apply initialRun_boolean_bound input.length input.resource hC.2.1 hC.2.2 D hD
  · intro j; rw [hr.2.1 j]; exact hLength j
  · intro j; rw [hr.2.2 j]; exact hInitial j
  · intro j; rw [hr.2.1 j]
    exact ⟨(source.length_pos j).le,(source.length_le j).trans hBunit⟩
  · intro j; rw [hr.2.2 j,hr.2.1 j]; exact source.initial_box j


-- The conservative stored-padding allowance covers both source length scans,
-- repeated lengths/maxima needed by the two pad calls, both append traversals,
-- and both false suffix constructions without compiler common-expression
-- elimination. Metadata traversal is linear in the actual stored width.
def storedPaddingVisits (numerator denominator : List Bool) : ℕ:=
  let width:=max numerator.length denominator.length
  3*(numerator.length+denominator.length)+2*width+8

theorem storedPaddingVisits_bound (numerator denominator : List Bool) :
    storedPaddingVisits numerator denominator≤12*(max numerator.length denominator.length+1):=by
  have hn:=Nat.le_max_left numerator.length denominator.length
  have hd:=Nat.le_max_right numerator.length denominator.length
  unfold storedPaddingVisits
  dsimp only
  omega


theorem padding_visits_covered {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) :
    storedPaddingVisits choice.probability.numerator choice.probability.denominator≤(paddingCharge choice).booleanWork:=
  storedPaddingVisits_bound _ _

end Blotto.BinaryGeneralResourceRunWork

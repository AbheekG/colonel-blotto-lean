import Blotto.BinaryGeneralResourceChoice
import Blotto.SharedResourceContracts
import Blotto.WordMachineRunEmbedding

/-! One-state Boolean resource rounding keeps a single reader and position,
reuses pending fixed-width coin words, and performs only selected pair writes.
The shared cap is never reset at a new pair. Exact numeric refinement is proved
separately; rank is erased proof data and no successor-state pair is stored. -/

namespace Blotto.BinaryGeneralResourceRun
variable {n : ℕ}
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair BinaryGeneralResourceChoice

inductive Cursor (capacity : FixedArrayTable n SignedWord) (hC : ∀ j,CanonicalWord (capacity.read j)) where
  | ready (state : Certified capacity)
  | coin {w : ℕ} (choice : Choice capacity hC) (a b : FixedBinaryWord w)
      (positive : 0<b.value) (normalized : a.value≤b.value)

def Cursor.rank {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)} : Cursor capacity hC→ℕ
  | .ready state => 2*state.state.active.length+1
  | .coin choice _ _ _ _ => 2*choice.state.state.active.length

def pending {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : Cursor capacity hC :=
  let words:=BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator
  have hv:=BinaryStoredRationalCoin.fromStored_values choice.probability.numerator choice.probability.denominator
  have hn:=choice.probability_numbers
  .coin choice words.1 words.2
    (by rw [hv.2,hn.2]; exact (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator_pos)
    (by rw [hv.1,hv.2,hn.1,hn.2]; exact (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.normalized)

theorem selected_rank_lt {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    {w : ℕ} (choice : Choice capacity hC) (a b : FixedBinaryWord w) (hb : 0<b.value) (hab : a.value≤b.value) (branch : Bool) :
    (Cursor.ready (choice.select branch) : Cursor capacity hC).rank < (Cursor.coin choice a b hb hab).rank := by
  have h:=choice.select_progress branch
  simp only [Cursor.rank]
  omega

def runIndexed {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hpos : pos≤N) :
    Option (Certified capacity)×ℕ :=
  match cursor with
  | .ready state =>
      match hp : BinaryGeneralResourceChoice.prepare capacity hC state with
      | .done result => (some result,pos)
      | .ask choice => runIndexed N bits (pending choice) pos hpos
  | .coin choice a b hb hab =>
      if hz : a.isZero=true then runIndexed N bits (.ready (choice.select false) : Cursor capacity hC) pos hpos else
        if he : a.same b=true then runIndexed N bits (.ready (choice.select true) : Cursor capacity hC) pos hpos else
          if hRead : pos<N then
            let next:=a.coinStep b
            have hlt : a.value<b.value := lt_of_le_of_ne hab (fun h=>he ((a.same_value b).mpr h))
            if bits ⟨pos,hRead⟩=next.1 then
              runIndexed N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
            else runIndexed N bits (.ready (choice.select (!bits ⟨pos,hRead⟩)) : Cursor capacity hC) (pos+1) (by omega)
          else (none,pos)
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state := by
      unfold BinaryGeneralResourceChoice.prepare at hp
      split at hp
      · cases Preparation.ask.inj hp; rfl
      · cases hp
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

def run {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) : Option (Certified capacity)×ℕ :=
  runIndexed N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)

noncomputable def Cursor.reference {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)} :
    Cursor capacity hC→WordCursor (RationalResourceCursor (fun j=>value (capacity.read j)))
  | .ready state => .state (.ready state.reference)
  | .coin choice a b hb hab => .coin a.value b.value hb hab
      (choice.reference.successor true) (choice.reference.successor false)

noncomputable def mapResult {capacity : FixedArrayTable n SignedWord} (result : Option (Certified capacity)×ℕ) :
    Option (RationalActiveResources (fun j=>value (capacity.read j)))×ℕ :=
  (result.1.map Certified.reference,result.2)

theorem coin_eq {S : Type*} (a b a' b' : ℕ) (hb : 0<b) (hab : a≤b) (hb' : 0<b') (hab' : a'≤b')
    (upper lower : S) (ha : a=a') (hd : b=b') :
    WordCursor.coin a b hb hab upper lower=WordCursor.coin a' b' hb' hab' upper lower := by
  subst a'
  subst b'
  rfl

theorem pending_reference {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : (pending choice).reference=
      .coin (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.numerator
        (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator
        (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator_pos
        (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.normalized
        (choice.reference.successor true) (choice.reference.successor false) := by
  have hv:=BinaryStoredRationalCoin.fromStored_values choice.probability.numerator choice.probability.denominator
  have hn:=choice.probability_numbers
  unfold pending Cursor.reference
  dsimp only
  apply coin_eq
  · exact hv.1.trans hn.1
  · exact hv.2.trans hn.2

theorem numeric_materialize {n : ℕ} {L : Fin n→ℚ} (N : ℕ) (bits : Fin N→Bool)
    (cursor : RationalResourceCursor L) (pos : ℕ) (hpos : pos≤N) :
    (rationalResourceMachine L).runCursorIndexed N bits (.state cursor) pos hpos=
      (rationalResourceMachine L).runCursorIndexed N bits (.state (.ready cursor.materialize)) pos hpos := by
  conv_lhs => unfold WordStateMachine.runCursorIndexed
  conv_rhs => unfold WordStateMachine.runCursorIndexed
  rfl

theorem runIndexed_refines {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hpos : pos≤N) :
    mapResult (runIndexed N bits cursor pos hpos)=
      (rationalResourceMachine (fun j=>value (capacity.read j))).runCursorIndexed N bits cursor.reference pos hpos := by
  cases cursor with
  | ready state =>
      conv_lhs => unfold runIndexed
      conv_rhs => rw [Cursor.reference]; unfold WordStateMachine.runCursorIndexed
      have hp:=BinaryGeneralResourceChoice.prepare_refines capacity hC state
      cases he : BinaryGeneralResourceChoice.prepare capacity hC state with
      | done result =>
          rw [he] at hp
          change rationalResourceStepReference state.reference=.done result.reference at hp
          change mapResult (some result,pos)=_
          rw [show (rationalResourceMachine (fun j=>value (capacity.read j))).step (.ready state.reference)=.done result.reference from
            (rationalResourceStep_refines state.reference).trans hp]
          rfl
      | ask choice =>
          rw [he] at hp
          have hs : (rationalResourceMachine (fun j=>value (capacity.read j))).step (.ready state.reference)=
            .ask (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.numerator
              (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator
              (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator_pos
              (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.normalized
              (choice.reference.successor true) (choice.reference.successor false) :=
            (rationalResourceStep_refines state.reference).trans hp
          rw [hs]
          have ih:=runIndexed_refines N bits (pending choice) pos hpos
          rw [pending_reference] at ih
          exact ih
  | coin choice a b hb hab =>
      conv_lhs => unfold runIndexed
      conv_rhs => rw [Cursor.reference]; unfold WordStateMachine.runCursorIndexed
      have hZero:=a.isZero_value
      have hSame : a.same b=true ↔ b.value≤a.value := by rw [a.same_value b]; omega
      simp only [hZero,hSame]
      by_cases hz : a.value=0
      · simp only [dite_eq_left hz,ite_eq_left hz]
        have ih:=runIndexed_refines N bits (.ready (choice.select false) : Cursor capacity hC) pos hpos
        have hm:=numeric_materialize N bits (choice.reference.successor false) pos hpos
        rw [←ResourceChoice.select_eq_materialize,←choice.select_reference false] at hm
        exact ih.trans hm.symm
      · simp only [dite_eq_right hz,ite_eq_right hz]
        by_cases he : b.value≤a.value
        · simp only [dite_eq_left he,ite_eq_left he]
          have ih:=runIndexed_refines N bits (.ready (choice.select true) : Cursor capacity hC) pos hpos
          have hm:=numeric_materialize N bits (choice.reference.successor true) pos hpos
          rw [←ResourceChoice.select_eq_materialize,←choice.select_reference true] at hm
          exact ih.trans hm.symm
        · simp only [dite_eq_right he,ite_eq_right he]
          by_cases hRead : pos<N
          · simp only [dite_eq_left hRead,FixedBinaryWord.coinStep_digit]
            have hlt : a.value<b.value := by omega
            by_cases hd : bits ⟨pos,hRead⟩=denominatorDigit a.value b.value
            · simp only [ite_eq_left hd]
              have ih:=runIndexed_refines N bits (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le)
                (pos+1) (by omega)
              simpa only [Cursor.reference,FixedBinaryWord.coinStep_residual a b hlt] using ih
            · simp only [ite_eq_right hd]
              have ih:=runIndexed_refines N bits (.ready (choice.select (!bits ⟨pos,hRead⟩)) : Cursor capacity hC) (pos+1) (by omega)
              cases hBit : bits ⟨pos,hRead⟩
              · simp only [hBit,Bool.not_false,Bool.false_eq_true,ite_false] at ih ⊢
                have hm:=numeric_materialize N bits (choice.reference.successor true) (pos+1) (by omega)
                rw [←ResourceChoice.select_eq_materialize,←choice.select_reference true] at hm
                exact ih.trans hm.symm
              · simp only [hBit,Bool.not_true,ite_true] at ih ⊢
                have hm:=numeric_materialize N bits (choice.reference.successor false) (pos+1) (by omega)
                rw [←ResourceChoice.select_eq_materialize,←choice.select_reference false] at hm
                exact ih.trans hm.symm
          · simp only [dite_eq_right hRead]
            rfl
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state := by
      unfold BinaryGeneralResourceChoice.prepare at he
      split at he
      · cases Preparation.ask.inj he; rfl
      · cases he
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

theorem run_refines {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) : mapResult (run hC N state bits)=
      (rationalResourceMachine (fun j=>value (capacity.read j))).run N (.ready state.reference) bits := by
  rw [WordStateMachine.run_eq_numeric]
  exact runIndexed_refines N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)

theorem run_position {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) : (run hC N state bits).2=
      ((rationalResourceMachine (fun j=>value (capacity.read j))).run N (.ready state.reference) bits).2 :=
  congrArg Prod.snd (run_refines hC N state bits)

theorem run_failure_iff {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) : (run hC N state bits).1=none ↔
      ((rationalResourceMachine (fun j=>value (capacity.read j))).run N (.ready state.reference) bits).1=none := by
  have he:=congrArg Prod.fst (run_refines hC N state bits)
  change (run hC N state bits).1.map Certified.reference=_ at he
  rw [←he]
  cases hr : (run hC N state bits).1 <;> simp

theorem run_success_reference {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state result : Certified capacity) (bits : Fin N→Bool) (h : (run hC N state bits).1=some result) :
    ((rationalResourceMachine (fun j=>value (capacity.read j))).run N (.ready state.reference) bits).1=some result.reference := by
  have he:=congrArg Prod.fst (run_refines hC N state bits)
  change (run hC N state bits).1.map Certified.reference=_ at he
  rw [h,Option.map_some] at he
  exact he.symm

theorem run_terminal {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state result : Certified capacity) (bits : Fin N→Bool) (h : (run hC N state bits).1=some result) :
    result.state.active.length≤1 :=
  rationalResourceMachine_terminal _ (.ready state.reference) N bits (run_success_reference hC N state result bits h)

theorem run_invariant {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (total : ℝ) (N : ℕ) (state result : Certified capacity) (bits : Fin N→Bool)
    (hs : RationalResourceInvariant (fun j=>value (capacity.read j)) total state.reference)
    (h : (run hC N state bits).1=some result) :
    RationalResourceInvariant (fun j=>value (capacity.read j)) total result.reference :=
  rationalResourceMachine_invariant _ total (.ready state.reference) N bits hs (run_success_reference hC N state result bits h)

theorem active_length_le {capacity : FixedArrayTable n SignedWord} (state : Certified capacity) :
    state.state.active.length≤n := by
  have he:=List.Nodup.length_le_card state.nodup
  simpa using he

def requests {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hpos : pos≤N) : ℕ :=
  match cursor with
  | .ready state =>
      match hp : BinaryGeneralResourceChoice.prepare capacity hC state with
      | .done _ => 0
      | .ask choice => 1+requests N bits (pending choice) pos hpos
  | .coin choice a b hb hab =>
      if hz : a.isZero=true then requests N bits (.ready (choice.select false) : Cursor capacity hC) pos hpos else
        if he : a.same b=true then requests N bits (.ready (choice.select true) : Cursor capacity hC) pos hpos else
          if hRead : pos<N then
            let next:=a.coinStep b
            have hlt : a.value<b.value := lt_of_le_of_ne hab (fun h=>he ((a.same_value b).mpr h))
            if bits ⟨pos,hRead⟩=next.1 then
              requests N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
            else requests N bits (.ready (choice.select (!bits ⟨pos,hRead⟩)) : Cursor capacity hC) (pos+1) (by omega)
          else 0
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state := by
      unfold BinaryGeneralResourceChoice.prepare at hp
      split at hp
      · cases Preparation.ask.inj hp; rfl
      · cases hp
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

def Cursor.requestBound {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)} : Cursor capacity hC→ℕ
  | .ready state => state.state.active.length-1
  | .coin choice _ _ _ _ => choice.state.state.active.length-2

theorem requests_bound {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hpos : pos≤N) :
    requests N bits cursor pos hpos≤cursor.requestBound := by
  cases cursor with
  | ready state =>
      unfold requests
      cases hp : BinaryGeneralResourceChoice.prepare capacity hC state with
      | done result => simp [Cursor.requestBound]
      | ask choice =>
          have hState : choice.state=state ∧ 2≤state.state.active.length := by
            unfold BinaryGeneralResourceChoice.prepare at hp
            split at hp
            · rename_i a b tail hHead
              cases Preparation.ask.inj hp
              refine ⟨rfl,?_⟩
              rw [hHead]
              simp only [List.length_cons]
              omega
            · cases hp
          have ih:=requests_bound N bits (pending choice) pos hpos
          change requests N bits (pending choice) pos hpos≤choice.state.state.active.length-2 at ih
          simp only [Cursor.requestBound]
          rw [hState.1] at ih
          omega
  | coin choice a b hb hab =>
      unfold requests
      have hLen : 2≤choice.state.state.active.length := by rw [choice.head_pair]; simp
      have hSelected (branch : Bool) : (Cursor.ready (choice.select branch) : Cursor capacity hC).requestBound≤
          (Cursor.coin choice a b hb hab).requestBound := by
        have h:=choice.select_progress branch
        simp only [Cursor.requestBound]
        omega
      split
      · exact (requests_bound N bits (.ready (choice.select false) : Cursor capacity hC) pos hpos).trans (hSelected false)
      · split
        · exact (requests_bound N bits (.ready (choice.select true) : Cursor capacity hC) pos hpos).trans (hSelected true)
        · split
          · dsimp only
            split
            · exact requests_bound N bits _ (pos+1) _
            · exact (requests_bound N bits (.ready (choice.select (!bits ⟨pos,by assumption⟩)) : Cursor capacity hC) (pos+1) _).trans (hSelected _)
          · exact Nat.zero_le _
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state := by
      unfold BinaryGeneralResourceChoice.prepare at hp
      split at hp
      · cases Preparation.ask.inj hp; rfl
      · cases hp
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  all_goals try (apply Prod.Lex.right; exact selected_rank_lt choice a b hb hab _)
  all_goals apply Prod.Lex.left
  all_goals omega

theorem run_requests_le_dimension {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (N : ℕ) (state : Certified capacity) (bits : Fin N→Bool) :
    requests N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)≤n-1 := by
  have h:=requests_bound N bits (.ready state : Cursor capacity hC) 0 (Nat.zero_le N)
  have hl:=active_length_le state
  change _≤state.state.active.length-1 at h
  omega


theorem runIndexed_position_bounds {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hpos : pos≤N) :
    pos≤(runIndexed N bits cursor pos hpos).2 ∧ (runIndexed N bits cursor pos hpos).2≤N:=by
  have hp:=(rationalResourceMachine (fun j=>value (capacity.read j))).runCursorIndexed_position_bounds N bits cursor.reference pos hpos
  rw [←runIndexed_refines] at hp
  exact hp

def initialRun (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (N : ℕ) (bits : Fin N→Bool) : Option (Certified capacity)×ℕ:=
  run hC N (initial capacity resource hC hR) bits

theorem initialRun_refines (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (N : ℕ) (bits : Fin N→Bool) : mapResult (initialRun capacity resource hC hR N bits)=
      (rationalResourceMachine (fun j=>value (capacity.read j))).run N
        (.ready (RationalActiveResources.initial (fun j=>value (capacity.read j)) (fun j=>value (resource.read j)))) bits:=by
  rw [initialRun,run_refines,initial_reference]

theorem initialRun_terminal_contract (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (total : ℝ) (hBox : InBox (fun j=>(value (capacity.read j) : ℝ)) (fun j=>(value (resource.read j) : ℝ)))
    (hTotal : (∑ j : Fin n,(value (resource.read j) : ℝ))=total)
    (N : ℕ) (bits : Fin N→Bool) (result : Certified capacity)
    (h : (initialRun capacity resource hC hR N bits).1=some result) :
    result.state.active.length≤1 ∧
      InBox (fun j=>(value (capacity.read j) : ℝ)) (fun j=>(value (result.state.resource.read j) : ℝ)) ∧
      (∑ j : Fin n,(value (result.state.resource.read j) : ℝ))=total:=by
  have hs : RationalResourceInvariant (fun j=>value (capacity.read j)) total (initial capacity resource hC hR).reference:=by
    rw [initial_reference]
    unfold RationalResourceInvariant
    rw [RationalActiveResources.initial,RationalResourceArray.realAllocation_ofAllocation]
    exact ⟨hBox,hTotal⟩
  have hi:=run_invariant hC total N (initial capacity resource hC hR) result bits hs h
  have ht:=run_terminal hC N (initial capacity resource hC hR) result bits h
  have he : result.reference.resource.realAllocation=(fun j=>(value (result.state.resource.read j) : ℝ)):=by
    funext j
    simp only [Certified.reference,RationalResourceArray.realAllocation,RationalResourceArray.allocation_ofAllocation,
      BinaryResourceState.allocation]
  unfold RationalResourceInvariant at hi
  rw [he] at hi
  exact ⟨ht,hi.1,hi.2⟩

end Blotto.BinaryGeneralResourceRun

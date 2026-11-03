import Blotto.BinaryPRGResourceLifetime
import Blotto.BinaryStoredSegmentChoiceWork

/-! Operational stored categorical preparation and shared-cap selection
lifetimes. Mass additions, positive-mass comparison, probability division,
padding and reached restoring-division coin buffers are concretely reserved.
The actual source producer supplies the selected label and absolute position.
Every reservation stays live, without an ownership/release premise. The
arithmetic backend is the retained Boolean Euclidean implementation. -/
set_option autoImplicit false
namespace Blotto.BinaryCategoricalLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryRationalOpcode BinaryCategoricalPreparation BinaryCategoricalRun
open BinaryCategoricalUnitLattice

def sumWithTrace {α : Type*} : List (α×SignedWord) → SignedWord×Trace
  | [] => (zero,[.frames 1,.arrayAllocation 8])
  | item::rest =>
      let later := sumWithTrace rest
      let added := BinaryRationalOpcodeAllocation.applyWithAllocation .add item.2 later.1
      (added.1,[.frames 1,.arrayAllocation 8,
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .add item.2 later.1)] ++ under 1 later.2)

@[simp] theorem sumWithTrace_erases {α : Type*} (items : List (α×SignedWord)) :
    (sumWithTrace items).1=WeightList.sumWords items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [sumWithTrace,BinaryRationalOpcodeAllocation.applyWithAllocation_state,ih,WeightList.sumWords]

def sumStepBound (D : ℕ) : ℕ := 2000000*(3+2*binaryWordWidth D)^4+8

theorem sumWithTrace_bounds {α : Type*} (D : ℕ) (hD : 0<D) (weights : WeightList α)
    (h : UnitLattice D weights) :
    listCells (sumWithTrace weights.items).2+arraySlots (sumWithTrace weights.items).2 ≤
      weights.items.length*sumStepBound D+8 ∧
    framePeak (sumWithTrace weights.items).2 ≤ weights.items.length+1 := by
  cases weights with
  | mk items hc hn =>
      induction items with
      | nil => simp [sumWithTrace,listCells,arraySlots,framePeak]
      | cons item rest ih =>
          let weights : WeightList α := ⟨item::rest,hc,hn⟩
          let tail := weights.tail item rest rfl
          have ht := tail_unit D weights h item rest rfl
          have hRest := ih tail.canonical tail.nonnegative ht
          have hItem := item_width D hD weights h item (by simp [weights])
          have hMass := mass_width D hD tail ht
          have hOp := (BinaryRationalOpcodeAllocation.opcodeStorage_bound .add item.2 tail.mass).trans
            (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hItem hMass) 2) 4))
          have hTail : (sumWithTrace rest).1=tail.mass := sumWithTrace_erases rest
          have hFrames := framePeak_under 1 (sumWithTrace rest).2
          dsimp only at hRest
          unfold sumStepBound at hRest
          rw [show 1+2*binaryWordWidth D+2=3+2*binaryWordWidth D by omega] at hOp
          simp only [sumWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
            listCells_under,arraySlots_under,List.length_cons]
          rw [hTail]
          unfold sumStepBound
          change _ ≤ _ ∧ _
          exact ⟨by nlinarith only [hOp,hRest.1],by omega⟩

def prepareWithTrace {α : Type*} (fallback : α) (weights : WeightList α) : Preparation α×Trace :=
  match he : weights.items with
  | [] => (.done fallback,[.frames 1,.arrayAllocation 8])
  | [head] => (.done head.1,[.frames 1,.arrayAllocation 8])
  | head::next::tail =>
      let computed := sumWithTrace weights.items
      have hMass : computed.1=weights.mass := sumWithTrace_erases weights.items
      let guard := BinaryRationalOpcodeAllocation.lessEqualWithAllocation computed.1 zero
      let common := [.frames 2,.arrayAllocation 16,
        .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage computed.1 zero)] ++ under 2 computed.2
      if hp : (!guard.1)=true then
        let probability := BinaryRationalOpcodeAllocation.applyWithAllocation .div head.2 computed.1
        (.ask ⟨weights,head,next,tail,he,
          (by
            rw [← weights.mass_value,← hMass]
            apply (positive_iff computed.1 (hMass.symm ▸ weights.mass_canonical)).mp
            simpa only [guard,positive,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state] using hp),
          probability.1,(by rw [BinaryRationalOpcodeAllocation.applyWithAllocation_state,hMass]; rfl)⟩,
          common ++ [.listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .div head.2 computed.1)])
      else (.done head.1,common)

@[simp] theorem prepareWithTrace_erases {α : Type*} (fallback : α) (weights : WeightList α) :
    (prepareWithTrace fallback weights).1=BinaryCategoricalRun.prepare fallback weights := by
  cases weights with
  | mk items hc hn =>
      cases items with
      | nil => rfl
      | cons head rest =>
          cases rest with
          | nil => rfl
          | cons next tail =>
              unfold prepareWithTrace BinaryCategoricalRun.prepare
              dsimp only
              simp only [sumWithTrace_erases,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state,
                BinaryRationalOpcodeAllocation.applyWithAllocation_state,positive,WeightList.mass,WeightList.probability]
              split <;> simp_all

def preparationBound (D M : ℕ) : ℕ :=
  (M+1)*sumStepBound D+2500*(2+2*binaryWordWidth D)^3+24

theorem prepareWithTrace_bounds {α : Type*} (D : ℕ) (hD : 0<D) (M : ℕ)
    (fallback : α) (weights : WeightList α) (h : UnitLattice D weights) (hM : weights.items.length ≤ M) :
    listCells (prepareWithTrace fallback weights).2+arraySlots (prepareWithTrace fallback weights).2 ≤ preparationBound D M ∧
    framePeak (prepareWithTrace fallback weights).2 ≤ M+3 := by
  have hSum := sumWithTrace_bounds D hD weights h
  have hMass := mass_width D hD weights h
  have hCompare := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound weights.mass zero).trans
    (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right
      (max_le hMass (show width zero≤1+2*binaryWordWidth D from by change 1≤_; omega)) 1) 3))
  have hFrames := framePeak_under 2 (sumWithTrace weights.items).2
  have hTop := Nat.mul_le_mul_right (sumStepBound D) hM
  rw [show 1+2*binaryWordWidth D+1=2+2*binaryWordWidth D by omega] at hCompare
  unfold prepareWithTrace
  split
  · simp only [listCells,arraySlots,framePeak]; unfold preparationBound; exact ⟨by omega,by omega⟩
  · simp only [listCells,arraySlots,framePeak]; unfold preparationBound; exact ⟨by omega,by omega⟩
  · rename_i head next tail he
    dsimp only
    have hHead := item_width D hD weights h head (by rw [he]; simp)
    have hDiv := (BinaryRationalOpcodeAllocation.opcodeStorage_bound .div head.2 weights.mass).trans
      (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hHead hMass) 2) 4))
    rw [show 1+2*binaryWordWidth D+2=3+2*binaryWordWidth D by omega] at hDiv
    simp only [sumWithTrace_erases]
    change BinaryRationalOpcodeAllocation.lessEqualStorage (WeightList.sumWords weights.items) zero ≤ _ at hCompare
    change BinaryRationalOpcodeAllocation.opcodeStorage .div head.2 (WeightList.sumWords weights.items) ≤ _ at hDiv
    split <;> simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
      listCells_under,arraySlots_under] <;> unfold preparationBound sumStepBound at * <;>
      exact ⟨by nlinarith only [hSum.1,hCompare,hTop,hDiv],by omega⟩

theorem prepared_choice_weights {α : Type*} (fallback : α) (weights : WeightList α) (choice : Choice α)
    (h : (prepareWithTrace fallback weights).1=.ask choice) : choice.weights=weights := by
  have hs := prepareWithTrace_erases fallback weights
  rw [h] at hs
  unfold BinaryCategoricalRun.prepare at hs
  split at hs
  · cases hs
  · cases hs
  · dsimp only at hs
    split at hs
    · cases Preparation.ask.inj hs; rfl
    · cases hs

def paddingTrace {α : Type*} (choice : Choice α) : Trace :=
  let w := width choice.probability
  [.frames (w+8),.listAllocation (2*w+8)]

def runWithTrace {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N→Bool)
    (cursor : Cursor α) (pos : ℕ) (hp : pos≤N) : (Option α×ℕ)×Trace :=
  match cursor with
  | .selected result => ((some result,pos),[.frames 1,.arrayAllocation 8])
  | .remaining weights =>
      let prepared := prepareWithTrace fallback weights
      match hs : prepared.1 with
      | .done result => ((some result,pos),[.frames 1,.arrayAllocation 8] ++ under 1 prepared.2)
      | .ask choice =>
          let later := runWithTrace fallback N bits (pending choice) pos hp
          (later.1,[.frames 1,.arrayAllocation 8] ++ under 1 prepared.2 ++ paddingTrace choice ++ under 1 later.2)
  | .coin (w:=w) choice a b hb hab =>
      let body : Trace := [.frames (w+8),.arrayAllocation 16]
      if hz : a.isZero=true then
        let later := runWithTrace fallback N bits (.remaining choice.rest) pos hp
        (later.1,body ++ under 1 later.2)
      else if he : a.same b=true then
        let later := runWithTrace fallback N bits (.selected choice.head.1) pos hp
        (later.1,body ++ under 1 later.2)
      else if hRead : pos<N then
        let bit := bits ⟨pos,hRead⟩
        let next := a.coinStep b
        have hlt : a.value<b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
        if bit=next.1 then
          let later := runWithTrace fallback N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
          (later.1,body ++ BinaryPRGResourceLifetime.coinTrace a b ++ under 1 later.2)
        else
          let later := runWithTrace fallback N bits (if bit then .remaining choice.rest else .selected choice.head.1) (pos+1) (by omega)
          (later.1,body ++ BinaryPRGResourceLifetime.coinTrace a b ++ under 1 later.2)
      else ((none,pos),body)
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hW := prepared_choice_weights fallback weights choice hs
    simp only [pending,Cursor.rank]; rw [hW]; omega
  · apply Prod.Lex.right
    have hl := rest_length choice
    simp only [Cursor.rank]; omega
  · apply Prod.Lex.right
    simp only [Cursor.rank]; rw [choice.head_pair]; simp only [List.length_cons]; omega
  all_goals apply Prod.Lex.left
  all_goals omega

theorem runWithTrace_erases {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N→Bool)
    (cursor : Cursor α) (pos : ℕ) (hp : pos≤N) :
    (runWithTrace fallback N bits cursor pos hp).1=BinaryCategoricalRun.runIndexed fallback N bits cursor pos hp := by
  cases cursor with
  | selected result => unfold runWithTrace BinaryCategoricalRun.runIndexed; rfl
  | remaining weights =>
      conv_lhs => unfold runWithTrace
      conv_rhs => unfold BinaryCategoricalRun.runIndexed
      rw [← prepareWithTrace_erases fallback weights]
      dsimp only
      cases hs : (prepareWithTrace fallback weights).1 with
      | done result => rfl
      | ask choice => exact runWithTrace_erases fallback N bits (pending choice) pos hp
  | coin choice a b hb hab =>
      conv_lhs => unfold runWithTrace
      conv_rhs => unfold BinaryCategoricalRun.runIndexed
      dsimp only
      split
      · exact runWithTrace_erases fallback N bits _ pos hp
      · split
        · exact runWithTrace_erases fallback N bits _ pos hp
        · split
          · split
            · exact runWithTrace_erases fallback N bits _ (pos+1) _
            · exact runWithTrace_erases fallback N bits _ (pos+1) _
          · rfl
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hW := prepared_choice_weights fallback weights choice hs
    simp only [pending,Cursor.rank]; rw [hW]; omega
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       have hl := rest_length choice
       simp only [Cursor.rank]
       rw [choice.head_pair] at hl ⊢
       simp only [List.length_cons] at hl ⊢
       omega)

def potential {α : Type*} (N pos : ℕ) (cursor : Cursor α) : ℕ := N-pos+cursor.rank
def stepBound (D M : ℕ) : ℕ := preparationBound D M+2*(5+8*binaryWordWidth D)+8+50*(7+8*binaryWordWidth D)^2+32
def localFrames (D M : ℕ) : ℕ := M+8*binaryWordWidth D+20

theorem paddingTrace_bounds {α : Type*} (D : ℕ) (hD : 0<D) (choice : Choice α)
    (h : UnitLattice D choice.weights) :
    listCells (paddingTrace choice)+arraySlots (paddingTrace choice) ≤ 2*(5+8*binaryWordWidth D)+8 ∧
    framePeak (paddingTrace choice) ≤ 13+8*binaryWordWidth D := by
  have hw := choice_probability_width D hD choice h
  simp only [paddingTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

theorem space_join {a b T B P : ℕ} (hA : a ≤ T) (hB : b ≤ (P+1)*T)
    (hP : P+1 ≤ B) : a+b ≤ (B+1)*T := by
  have hm := Nat.mul_le_mul_right T hP
  nlinarith only [hA,hB,hm]

set_option maxHeartbeats 2000000 in
theorem runWithTrace_bounds {α : Type*} (D : ℕ) (hD : 0<D) (M : ℕ)
    (fallback : α) (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor α) (pos : ℕ) (hp : pos≤N)
    (h : BinaryCategoricalRunWork.BoundedCursor D M cursor) :
    listCells (runWithTrace fallback N bits cursor pos hp).2+arraySlots (runWithTrace fallback N bits cursor pos hp).2 ≤
      (potential N pos cursor+1)*stepBound D M ∧
    framePeak (runWithTrace fallback N bits cursor pos hp).2 ≤ potential N pos cursor+localFrames D M := by
  cases cursor with
  | selected result =>
      have ht : 8 ≤ stepBound D M := by unfold stepBound; omega
      have hm := Nat.mul_le_mul_right (stepBound D M) (show 1 ≤ potential N pos (.selected result : Cursor α)+1 from by omega)
      simp only [runWithTrace,listCells,arraySlots,framePeak]
      unfold potential localFrames
      exact ⟨by nlinarith only [ht,hm],by omega⟩
  | remaining weights =>
      have hPrep := prepareWithTrace_bounds D hD M fallback weights h.1 h.2
      have hPrepFrames := framePeak_under 1 (prepareWithTrace fallback weights).2
      unfold runWithTrace
      dsimp only
      cases hs : (prepareWithTrace fallback weights).1 with
      | done result =>
          have ht : preparationBound D M+8 ≤ stepBound D M := by unfold stepBound; omega
          have hm := Nat.mul_le_mul_right (stepBound D M) (show 1 ≤ potential N pos (.remaining weights : Cursor α)+1 from by omega)
          simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
          unfold potential localFrames
          exact ⟨by nlinarith only [hPrep.1,ht,hm],by omega⟩
      | ask choice =>
          have hW := prepared_choice_weights fallback weights choice hs
          have hUnit : UnitLattice D choice.weights := hW.symm ▸ h.1
          have hLength : choice.weights.items.length ≤ M := hW.symm ▸ h.2
          have hNext := BinaryCategoricalRunWork.pending_bounded D hD M choice hUnit hLength
          have hLater := runWithTrace_bounds D hD M fallback N bits (pending choice) pos hp hNext
          have hLaterFrames := framePeak_under 1 (runWithTrace fallback N bits (pending choice) pos hp).2
          have hPad := paddingTrace_bounds D hD choice hUnit
          have hDrop : potential N pos (pending choice)+1 ≤ potential N pos (.remaining weights) := by
            simp only [potential,pending,Cursor.rank]; rw [hW]; omega
          have hLocal : preparationBound D M+2*(5+8*binaryWordWidth D)+8+8 ≤ stepBound D M := by unfold stepBound; omega
          have hJoin := space_join (by omega : 8+
            (listCells (prepareWithTrace fallback weights).2+arraySlots (prepareWithTrace fallback weights).2)+
            (listCells (paddingTrace choice)+arraySlots (paddingTrace choice)) ≤ stepBound D M) hLater.1 hDrop
          simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
          unfold localFrames at *
          exact ⟨by omega,by omega⟩
  | @coin w choice a b hb hab =>
      obtain ⟨hUnit,hLength,hWidth⟩ := h
      have hCoin := BinaryPRGResourceLifetime.coinTrace_bound a b (5+8*binaryWordWidth D) hWidth
      rw [show 5+8*binaryWordWidth D+2=7+8*binaryWordWidth D by omega] at hCoin
      have hBody : 16 ≤ stepBound D M := by unfold stepBound; omega
      have hBodyCoin : 16+50*(7+8*binaryWordWidth D)^2 ≤ stepBound D M := by unfold stepBound; omega
      have hRest := BinaryCategoricalRunWork.rest_bounded D M choice hUnit hLength
      have hRestDrop : potential N pos (.remaining choice.rest)+1 ≤ potential N pos (.coin choice a b hb hab) := by
        have hl := rest_length choice
        simp only [potential,Cursor.rank]; omega
      have hSelectedDrop : potential N pos (.selected choice.head.1)+1 ≤ potential N pos (.coin choice a b hb hab) := by
        simp only [potential,Cursor.rank]
        rw [choice.head_pair]
        simp only [List.length_cons]
        omega
      unfold runWithTrace
      dsimp only
      split
      · have hLater := runWithTrace_bounds D hD M fallback N bits (.remaining choice.rest) pos hp hRest
        have hLaterFrames := framePeak_under 1 (runWithTrace fallback N bits (.remaining choice.rest) pos hp).2
        have hJoin := space_join hBody hLater.1 hRestDrop
        simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
        unfold localFrames at *
        exact ⟨by omega,by omega⟩
      · rename_i hz
        split
        · have hLater := runWithTrace_bounds D hD M fallback N bits (.selected choice.head.1) pos hp trivial
          have hLaterFrames := framePeak_under 1 (runWithTrace fallback N bits (.selected choice.head.1) pos hp).2
          have hJoin := space_join hBody hLater.1 hSelectedDrop
          simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
          unfold localFrames at *
          exact ⟨by omega,by omega⟩
        · rename_i he
          split
          · rename_i hRead
            have hlt : a.value<b.value := lt_of_le_of_ne hab (fun hv => he ((a.same_value b).mpr hv))
            have hLocal : 16+listCells (BinaryPRGResourceLifetime.coinTrace a b)+
                arraySlots (BinaryPRGResourceLifetime.coinTrace a b) ≤ stepBound D M := by omega
            split
            · have hLater := runWithTrace_bounds D hD M fallback N bits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
                ⟨hUnit,hLength,hWidth⟩
              have hLaterFrames := framePeak_under 1 (runWithTrace fallback N bits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)).2
              have hDrop : potential N (pos+1) (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le)+1 ≤
                  potential N pos (.coin choice a b hb hab) := by simp only [potential,Cursor.rank]; omega
              have hJoin := space_join hLocal hLater.1 hDrop
              simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
              unfold localFrames at *
              exact ⟨by omega,by omega⟩
            · split
              · have hLater := runWithTrace_bounds D hD M fallback N bits (.remaining choice.rest) (pos+1) (by omega) hRest
                have hLaterFrames := framePeak_under 1 (runWithTrace fallback N bits (.remaining choice.rest) (pos+1) (by omega)).2
                have hDrop : potential N (pos+1) (.remaining choice.rest)+1 ≤ potential N pos (.coin choice a b hb hab) := by
                  have hl := rest_length choice
                  simp only [potential,Cursor.rank]; omega
                have hJoin := space_join hLocal hLater.1 hDrop
                simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
                unfold localFrames at *
                exact ⟨by omega,by omega⟩
              · have hLater := runWithTrace_bounds D hD M fallback N bits (.selected choice.head.1) (pos+1) (by omega) trivial
                have hLaterFrames := framePeak_under 1 (runWithTrace fallback N bits (.selected choice.head.1) (pos+1) (by omega)).2
                have hDrop : potential N (pos+1) (.selected choice.head.1)+1 ≤ potential N pos (.coin choice a b hb hab) := by
                  simp only [potential,Cursor.rank]
                  rw [choice.head_pair]
                  simp only [List.length_cons]
                  omega
                have hJoin := space_join hLocal hLater.1 hDrop
                simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
                unfold localFrames at *
                exact ⟨by omega,by omega⟩
          · have hm := Nat.mul_le_mul_right (stepBound D M) (show 1 ≤ potential N pos (.coin choice a b hb hab)+1 from by omega)
            simp only [listCells,arraySlots,framePeak]
            unfold potential localFrames
            exact ⟨by nlinarith only [hBody,hm],by omega⟩
termination_by (N-pos,cursor.rank)
decreasing_by
  all_goals simp_all only [Cursor.rank]
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       try simp only [pending]
       first
       | (have hW := prepared_choice_weights fallback weights choice hs; rw [hW]; omega)
       | (have hl := rest_length choice; rw [choice.head_pair] at hl ⊢; simp only [List.length_cons] at hl ⊢; omega))

theorem run_all_prefix {α : Type*} (D : ℕ) (hD : 0<D) (M : ℕ)
    (fallback : α) (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor α) (pos : ℕ) (hp : pos≤N)
    (h : BinaryCategoricalRunWork.BoundedCursor D M cursor) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (runWithTrace fallback N bits cursor pos hp).2 steps ≤
      borrowedCells+(potential N pos cursor+1)*stepBound D M := by
  have hb := (runWithTrace_bounds D hD M fallback N bits cursor pos hp h).1
  have hl := listCells_take_le (runWithTrace fallback N bits cursor pos hp).2 steps
  have ha := arraySlots_take_le (runWithTrace fallback N bits cursor pos hp).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryCategoricalLifetime

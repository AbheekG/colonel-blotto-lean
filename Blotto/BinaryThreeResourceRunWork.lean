import Blotto.BinaryThreeResourceExecution
import Blotto.BinaryCoinWordWork

/-! The actual reflected three-coordinate resource loop retains a single reader,
fixed residual coin words and actual prepared/selected arithmetic charges. Exact
native result, none and absolute position refine the old shared-cap runner.
Logical accesses/control and conservative copies remain separate from Boolean
work and from physical compiler/ownership contracts. -/

namespace Blotto.BinaryThreeResourceRunWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourcePair BinaryResourceChoice
open BinarySharedResourceRun BinaryThreeResourceExecution BinaryGeneralResourceExecution

def paddingCharge {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : Charge :=
  ⟨12 * (max choice.probability.numerator.length choice.probability.denominator.length + 1),2,0,2,0⟩

def runIndexed {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
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
      let body : Charge:=⟨FixedWordCoin.bodyWork a b + 2,0,0,2,0⟩
      if hz : a.isZero=true then
        let selected:=BinaryThreeResourceExecution.selectWithCharge choice false
        let later:=runIndexed N bits (.ready selected.1 : Cursor capacity hC) pos hp
        (later.1,body.add (selected.2.add later.2))
      else if he : a.same b=true then
        let selected:=BinaryThreeResourceExecution.selectWithCharge choice true
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
          let selected:=BinaryThreeResourceExecution.selectWithCharge choice (!bit)
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
      unfold BinaryResourceChoice.prepare at hh
      split at hh
      · cases Preparation.ask.inj hh; rfl
      · cases hh
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  · apply Prod.Lex.right
    rw [BinaryThreeResourceExecution.selectWithCharge_state]
    exact BinarySharedResourceRun.selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    rw [BinaryThreeResourceExecution.selectWithCharge_state]
    exact BinarySharedResourceRun.selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega


theorem runIndexed_state {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos≤N) :
    (runIndexed N bits cursor pos hp).1=BinarySharedResourceRun.runIndexed N bits cursor pos hp:=by
  cases cursor with
  | ready state=>
      conv_lhs=>unfold runIndexed
      conv_rhs=>unfold BinarySharedResourceRun.runIndexed
      rw [←prepareStep_state hC state]
      dsimp only
      cases hs : (prepareStep hC state).1 with
      | done result=>rfl
      | ask choice=>
          exact runIndexed_state N bits (pending choice) pos hp
  | coin choice a b hb hab=>
      conv_lhs=>unfold runIndexed
      conv_rhs=>unfold BinarySharedResourceRun.runIndexed
      dsimp only
      split
      · rw [BinaryThreeResourceExecution.selectWithCharge_state]
        exact runIndexed_state N bits (.ready (choice.select false) : Cursor capacity hC) pos hp
      · split
        · rw [BinaryThreeResourceExecution.selectWithCharge_state]
          exact runIndexed_state N bits (.ready (choice.select true) : Cursor capacity hC) pos hp
        · split
          · split
            · exact runIndexed_state N bits _ (pos+1) _
            · rw [BinaryThreeResourceExecution.selectWithCharge_state]
              exact runIndexed_state N bits _ (pos+1) _
          · rfl
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state:=by
      have hh:=prepareStep_state hC state
      rw [hs] at hh
      unfold BinaryResourceChoice.prepare at hh
      split at hh
      · cases Preparation.ask.inj hh; rfl
      · cases hh
    simp only [pending,Cursor.rank]
    rw [hState]
    omega
  all_goals try (apply Prod.Lex.right; exact BinarySharedResourceRun.selected_rank_lt choice a b hb hab _)
  all_goals apply Prod.Lex.left
  all_goals omega



open BinaryThreeResourceHeight

def bodyBound (C s : ℕ) : ℕ := 24 * coinWidth C s + 30
def padBound (C s : ℕ) : ℕ := 12 * (coinWidth C s + 1)
def pairTotalBound (C s : ℕ) : ℕ := pairBound C s + padBound C s + selectBound C s + bodyBound C s

def allowance {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s remaining : ℕ) : Cursor capacity hC → ℕ
  | .ready state => (state.state.active.length - 1) * pairTotalBound C s + remaining * bodyBound C s
  | .coin choice _ _ _ _ => (choice.state.state.active.length - 2) * pairTotalBound C s +
      selectBound C s + (remaining + 1) * bodyBound C s

def BoundedCursor {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) : Cursor capacity hC → Prop
  | .ready state => StateHeight capacity C s state
  | .coin (w := w) choice _ _ _ _ => StateHeight capacity C s choice.state ∧ w ≤ coinWidth C s

theorem pending_bounded {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (choice : Choice capacity hC) (h : StateHeight capacity C s choice.state) : BoundedCursor C s (pending choice) :=
  ⟨h, probability_width C s hs hCap choice h⟩

theorem pad_bound {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (choice : Choice capacity hC) (h : StateHeight capacity C s choice.state) :
    (paddingCharge choice).booleanWork ≤ padBound C s := by
  have hw := probability_width C s hs hCap choice h
  unfold paddingCharge padBound
  exact Nat.mul_le_mul_left 12 (Nat.add_le_add_right hw 1)

theorem body_bound (C s : ℕ) {w : ℕ} (a b : FixedBinaryWord w) (hw : w ≤ coinWidth C s) :
    FixedWordCoin.bodyWork a b + 2 ≤ bodyBound C s := by
  have hb := FixedWordCoin.bodyWork_bound a b
  rw [FixedWordCoin.bodyAllowance_eq] at hb
  unfold bodyBound
  omega

theorem allowance_mono {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (cursor : Cursor capacity hC) {a b : ℕ} (h : a ≤ b) : allowance C s a cursor ≤ allowance C s b cursor := by
  cases cursor <;> simp only [allowance] <;> gcongr

theorem prepared_credit {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s) (remaining : ℕ)
    (state : Certified capacity) (h : StateHeight capacity C s state) (choice : Choice capacity hC)
    (he : (prepareStep hC state).1 = .ask choice) :
    (prepareStep hC state).2.booleanWork + (paddingCharge choice).booleanWork + allowance C s remaining (pending choice) ≤
      allowance C s remaining (.ready state : Cursor capacity hC) := by
  have hState := prepareStep_choice_state hC state choice he
  have hChoice : StateHeight capacity C s choice.state := hState.symm ▸ h
  have hPrep := prepareStep_bound hC C s hs hCap state h
  have hPad := pad_bound C s hs hCap choice hChoice
  have hLen : 2 ≤ state.state.active.length := by rw [← hState, choice.head_pair]; simp only [List.length_cons]; omega
  have hRank : state.state.active.length - 1 = state.state.active.length - 2 + 1 := by omega
  unfold allowance pending
  dsimp only
  rw [hState,hRank]
  unfold pairTotalBound
  nlinarith

theorem selected_credit {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s) (remaining : ℕ)
    (choice : Choice capacity hC) (h : StateHeight capacity C s choice.state)
    {w : ℕ} (a b : FixedBinaryWord w) (hb : 0 < b.value) (hab : a.value ≤ b.value)
    (hw : w ≤ coinWidth C s) (branch : Bool) :
    FixedWordCoin.bodyWork a b + 2 + (BinaryThreeResourceExecution.selectWithCharge choice branch).2.booleanWork +
      allowance C s remaining (.ready (choice.select branch) : Cursor capacity hC) ≤ allowance C s remaining (.coin choice a b hb hab) := by
  have hBody := body_bound C s a b hw
  have hSelect := selectWithCharge_bound C s hs hCap choice h branch
  have hProgress := choice.select_progress branch
  have hLen : 2 ≤ choice.state.state.active.length := by rw [choice.head_pair]; simp only [List.length_cons]; omega
  have hRanks : (choice.select branch).state.active.length - 1 ≤ choice.state.state.active.length - 2 := by omega
  have hScale := Nat.mul_le_mul_right (pairTotalBound C s) hRanks
  unfold allowance
  nlinarith

theorem residual_credit {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s N pos : ℕ) (hRead : pos < N) (choice : Choice capacity hC) {w : ℕ} (a b next : FixedBinaryWord w)
    (hb : 0 < b.value) (hab : a.value ≤ b.value) (hNext : next.value ≤ b.value) (hw : w ≤ coinWidth C s) :
    FixedWordCoin.bodyWork a b + 2 + allowance C s (N - (pos + 1)) (.coin choice next b hb hNext) ≤
      allowance C s (N - pos) (.coin choice a b hb hab) := by
  have hBody := body_bound C s a b hw
  have hRemaining : N - pos = N - (pos + 1) + 1 := by omega
  simp only [allowance]
  rw [hRemaining]
  nlinarith

theorem runIndexed_bound {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (N : ℕ) (bits : Fin N → Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hp : pos ≤ N)
    (h : BoundedCursor C s cursor) :
    (runIndexed N bits cursor pos hp).2.booleanWork ≤ allowance C s (N - pos) cursor := by
  cases cursor with
  | ready state =>
    unfold runIndexed
    dsimp only
    cases he : (prepareStep hC state).1 with
    | done result =>
      dsimp only
      rw [prepareStep_done_work hC state result he]
      exact Nat.zero_le _
    | ask choice =>
      dsimp only [Charge.add]
      have hState := prepareStep_choice_state hC state choice he
      have hChoice : StateHeight capacity C s choice.state := hState.symm ▸ h
      have ih := runIndexed_bound (hC := hC) C s hs hCap N bits (pending choice) pos hp (pending_bounded C s hs hCap choice hChoice)
      have hc := prepared_credit hC C s hs hCap (N - pos) state h choice he
      omega
  | @coin w choice a b hb hab =>
    obtain ⟨hState,hWidth⟩ := h
    unfold runIndexed
    dsimp only
    split
    · rw [BinaryThreeResourceExecution.selectWithCharge_state]
      dsimp only [Charge.add]
      have ih := runIndexed_bound (hC := hC) C s hs hCap N bits (.ready (choice.select false)) pos hp
        (selected_height C s hs hCap choice hState false)
      have hc := selected_credit C s hs hCap (N - pos) choice hState a b hb hab hWidth false
      omega
    · split
      · rw [BinaryThreeResourceExecution.selectWithCharge_state]
        dsimp only [Charge.add]
        have ih := runIndexed_bound (hC := hC) C s hs hCap N bits (.ready (choice.select true)) pos hp
          (selected_height C s hs hCap choice hState true)
        have hc := selected_credit C s hs hCap (N - pos) choice hState a b hb hab hWidth true
        omega
      · rename_i hz he
        split
        · rename_i hRead
          split
          · have hlt : a.value < b.value := lt_of_le_of_ne hab (fun hv => he ((a.same_value b).mpr hv))
            dsimp only [Charge.add]
            have ih := runIndexed_bound (hC := hC) C s hs hCap N bits
              (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) (pos + 1) (by omega) ⟨hState,hWidth⟩
            have hc := residual_credit C s N pos hRead choice a b (a.coinStep b).2 hb hab (a.coinStep_normalized b hlt).le hWidth
            omega
          · rw [BinaryThreeResourceExecution.selectWithCharge_state]
            dsimp only [Charge.add]
            have hNext := selected_height C s hs hCap choice hState (!bits ⟨pos,hRead⟩)
            have ih := runIndexed_bound (hC := hC) C s hs hCap N bits (.ready (choice.select (!bits ⟨pos,hRead⟩)))
              (pos + 1) (by omega) hNext
            have hc := selected_credit C s hs hCap (N - pos) choice hState a b hb hab hWidth (!bits ⟨pos,hRead⟩)
            have hm := allowance_mono C s (.ready (choice.select (!bits ⟨pos,hRead⟩)) : Cursor capacity hC)
              (show N - (pos + 1) ≤ N - pos by omega)
            omega
        · have hc := body_bound C s a b hWidth
          simp only [allowance]
          nlinarith
termination_by (N - pos, cursor.rank)
decreasing_by
  all_goals simp_all only [Cursor.rank]
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       first
       | (simp only [pending]; rw [prepareStep_choice_state hC state choice he]; omega)
       | (have hp := choice.select_progress false; omega)
       | (have hp := choice.select_progress true; omega))

end Blotto.BinaryThreeResourceRunWork

import Blotto.BinaryCategoricalPreparation
import Blotto.BinarySharedResourceRun

/-! Native categorical selection retains the remaining stored weight list and
one fixed-width Boolean coin. The one reader/position cap is shared across all
selected suffixes; there is no per-coin reset or Rat-to-word encoding. -/

namespace Blotto.BinaryCategoricalRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryCategoricalPreparation

structure Choice (α : Type*) where
  weights : WeightList α
  head : α×SignedWord
  next : α×SignedWord
  tail : List (α×SignedWord)
  head_pair : weights.items=head::next::tail
  positive : 0<weights.reference.mass
  probability : SignedWord
  probability_correct : probability=weights.probability head

namespace Choice
def rest {α : Type*} (choice : Choice α) : WeightList α:=choice.weights.tail choice.head (choice.next::choice.tail) choice.head_pair
noncomputable def words {α : Type*} (choice : Choice α) : ProbabilityWords:=
  ProbabilityWords.ofRat (value choice.head.2/choice.weights.reference.mass)
    ⟨div_nonneg (choice.weights.nonnegative choice.head (by rw [choice.head_pair]; simp)) choice.positive.le,
      (div_le_one choice.positive).mpr (choice.weights.head_le_mass choice.head _ choice.head_pair)⟩
theorem probability_numbers {α : Type*} (choice : Choice α) :
    BinaryBigEndian.littleValue choice.probability.numerator=choice.words.numerator ∧
      BinaryBigEndian.littleValue choice.probability.denominator=choice.words.denominator:=by
  rw [choice.probability_correct]
  exact choice.weights.probability_numbers choice.head _ choice.head_pair choice.positive
end Choice

inductive Preparation (α : Type*) where
  | done (value : α)
  | ask (choice : Choice α)

def prepare {α : Type*} (fallback : α) (weights : WeightList α) : Preparation α:=
  match h : weights.items with
  | []=>.done fallback
  | [head]=>.done head.1
  | head::next::tail=>
      let mass:=weights.mass
      if hp : positive mass=true then
        .ask ⟨weights,head,next,tail,h,(by rw [←weights.mass_value]; exact (positive_iff mass weights.mass_canonical).mp hp),
          weights.probability head,rfl⟩
      else .done head.1

inductive Cursor (α : Type*) where
  | remaining (weights : WeightList α)
  | selected (value : α)
  | coin {w : ℕ} (choice : Choice α) (a b : FixedBinaryWord w) (positive : 0<b.value) (normalized : a.value≤b.value)

def Cursor.rank {α : Type*} : Cursor α→ℕ
  | .selected _=>0
  | .remaining weights=>2*weights.items.length+1
  | .coin choice _ _ _ _=>2*choice.weights.items.length

def pending {α : Type*} (choice : Choice α) : Cursor α:=
  let words:=BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator
  have hv:=BinaryStoredRationalCoin.fromStored_values choice.probability.numerator choice.probability.denominator
  have hn:=choice.probability_numbers
  .coin choice words.1 words.2 (by rw [hv.2,hn.2]; exact choice.words.denominator_pos)
    (by rw [hv.1,hv.2,hn.1,hn.2]; exact choice.words.normalized)

theorem rest_length {α : Type*} (choice : Choice α) : choice.rest.items.length+1=choice.weights.items.length:=by
  rw [choice.head_pair]
  rfl

def runIndexed {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N→Bool)
    (cursor : Cursor α) (pos : ℕ) (hpos : pos≤N) : Option α×ℕ:=
  match cursor with
  | .selected value=>(some value,pos)
  | .remaining weights=>match hp : prepare fallback weights with
    | .done value=>(some value,pos)
    | .ask choice=>runIndexed fallback N bits (pending choice) pos hpos
  | .coin choice a b hb hab=>
      if hz : a.isZero=true then runIndexed fallback N bits (.remaining choice.rest) pos hpos else
        if he : a.same b=true then runIndexed fallback N bits (.selected choice.head.1) pos hpos else
          if hRead : pos<N then
            let next:=a.coinStep b
            have hlt : a.value<b.value:=lt_of_le_of_ne hab (fun h=>he ((a.same_value b).mpr h))
            if bits ⟨pos,hRead⟩=next.1 then
              runIndexed fallback N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
            else runIndexed fallback N bits
              (if bits ⟨pos,hRead⟩ then .remaining choice.rest else .selected choice.head.1) (pos+1) (by omega)
          else (none,pos)
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hW : choice.weights=weights:=by
      unfold prepare at hp
      split at hp
      · cases hp
      · cases hp
      · dsimp only at hp
        split at hp
        · cases Preparation.ask.inj hp; rfl
        · cases hp
    simp only [pending,Cursor.rank]
    rw [hW]
    omega
  · apply Prod.Lex.right
    have hL:=rest_length choice
    simp only [Cursor.rank]
    omega
  · apply Prod.Lex.right
    simp only [Cursor.rank]
    rw [choice.head_pair]
    simp only [List.length_cons]
    omega
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.left
    omega

noncomputable def Cursor.reference {α : Type*} : Cursor α→WordCursor (CategoricalState α)
  | .remaining weights=>.state (.remaining weights.reference)
  | .selected value=>.state (.selected value)
  | .coin choice a b hb hab=>.coin a.value b.value hb hab (.selected choice.head.1) (.remaining choice.rest.reference)

theorem categorical_many {α : Type*} (fallback : α) (head next : α×ℚ) (tail : List (α×ℚ))
    (hn : ∀ (item : α × ℚ), item ∈ (head :: next :: tail) → 0 ≤ item.2) :
    categoricalTransition fallback (.remaining ⟨head::next::tail,hn⟩)=
      if hm : 0<(RationalWeightList.mk (head::next::tail) hn).mass then
        let weights : RationalWeightList α:=⟨head::next::tail,hn⟩
        let rest : RationalWeightList α:=⟨next::tail,fun item hi=>hn item (by simp [hi])⟩
        let p:=ProbabilityWords.ofRat (head.2/weights.mass)
          ⟨div_nonneg (hn head (by simp)) hm.le,(div_le_one hm).mpr (by
            change head.2≤head.2+rest.mass
            linarith [rest.mass_nonnegative])⟩
        .ask p.numerator p.denominator p.denominator_pos p.normalized (.selected head.1) (.remaining rest)
      else .done head.1:=by rfl

theorem prepare_refines {α : Type*} (fallback : α) (weights : WeightList α) :
    match prepare fallback weights with
    | .done value=>categoricalTransition fallback (.remaining weights.reference)=.done value
    | .ask choice=>categoricalTransition fallback (.remaining weights.reference)=
        .ask choice.words.numerator choice.words.denominator choice.words.denominator_pos choice.words.normalized
          (.selected choice.head.1) (.remaining choice.rest.reference):=by
  cases weights with
  | mk items hc hn=>
      cases items with
      | nil=>rfl
      | cons head rest=>
          cases rest with
          | nil=>rfl
          | cons next tail=>
              let weights : WeightList α:=⟨head::next::tail,hc,hn⟩
              let numeric : RationalWeightList α:=
                ⟨(head.1,value head.2)::(next.1,value next.2)::tail.map (fun (item : α×SignedWord)=>(item.1,value item.2)),
                  by
                    intro item hi
                    exact weights.reference.nonnegative item hi⟩
              have hTransition : categoricalTransition fallback (.remaining weights.reference)=
                categoricalTransition fallback (.remaining numeric):=rfl
              by_cases hp : positive weights.mass=true
              · have hPrep : prepare fallback weights=.ask
                  ⟨weights,head,next,tail,rfl,(by rw [←weights.mass_value]; exact (positive_iff _ weights.mass_canonical).mp hp),weights.probability head,rfl⟩:=by
                  unfold prepare
                  dsimp only [weights]
                  rw [dite_eq_left hp]
                change (match prepare fallback weights with | .done value=>_ | .ask choice=>_) 
                rw [hPrep]
                dsimp only
                have hMass : 0<(WeightList.reference (⟨head::next::tail,hc,hn⟩ : WeightList α)).mass:=by
                  rw [←WeightList.mass_value]
                  exact (positive_iff _ (WeightList.mass_canonical _)).mp hp
                change 0<numeric.mass at hMass
                rw [hTransition]
                change categoricalTransition fallback (.remaining numeric)=_
                dsimp only [numeric]
                rw [categorical_many,dite_eq_left hMass]
                rfl
              · have hPrep : prepare fallback weights=.done head.1:=by
                  unfold prepare
                  dsimp only [weights]
                  rw [dite_eq_right hp]
                change (match prepare fallback weights with | .done value=>_ | .ask choice=>_)
                rw [hPrep]
                dsimp only
                have hMass : ¬0<(WeightList.reference (⟨head::next::tail,hc,hn⟩ : WeightList α)).mass:=by
                  intro h
                  apply hp
                  rw [←WeightList.mass_value] at h
                  exact (positive_iff _ (WeightList.mass_canonical _)).mpr h
                change ¬0<numeric.mass at hMass
                rw [hTransition]
                change categoricalTransition fallback (.remaining numeric)=_
                dsimp only [numeric]
                rw [categorical_many,dite_eq_right hMass]

theorem pending_reference {α : Type*} (choice : Choice α) : (pending choice).reference=
    .coin choice.words.numerator choice.words.denominator choice.words.denominator_pos choice.words.normalized
      (.selected choice.head.1) (.remaining choice.rest.reference):=by
  have hv:=BinaryStoredRationalCoin.fromStored_values choice.probability.numerator choice.probability.denominator
  have hn:=choice.probability_numbers
  unfold pending Cursor.reference
  dsimp only
  apply BinarySharedResourceRun.coin_eq
  · exact hv.1.trans hn.1
  · exact hv.2.trans hn.2

theorem runIndexed_refines {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N→Bool)
    (cursor : Cursor α) (pos : ℕ) (hpos : pos≤N) : runIndexed fallback N bits cursor pos hpos=
      (categoricalMachine fallback).runCursorIndexed N bits cursor.reference pos hpos:=by
  cases cursor with
  | selected value=>
      conv_lhs=>unfold runIndexed
      conv_rhs=>rw [Cursor.reference]; unfold WordStateMachine.runCursorIndexed
      rfl
  | remaining weights=>
      conv_lhs=>unfold runIndexed
      conv_rhs=>rw [Cursor.reference]; unfold WordStateMachine.runCursorIndexed
      simp only [categoricalMachine]
      have hp:=prepare_refines fallback weights
      cases he : prepare fallback weights with
      | done value=>rw [he] at hp; dsimp only at hp; rw [hp]
      | ask choice=>
          rw [he] at hp
          dsimp only at hp
          rw [hp]
          have ih:=runIndexed_refines fallback N bits (pending choice) pos hpos
          rw [pending_reference] at ih
          exact ih
  | coin choice a b hb hab=>
      conv_lhs=>unfold runIndexed
      conv_rhs=>rw [Cursor.reference]; unfold WordStateMachine.runCursorIndexed
      have hSame : a.same b=true ↔ b.value≤a.value:=by rw [a.same_value b]; omega
      simp only [a.isZero_value,hSame]
      by_cases hz : a.value=0
      · simp only [dite_eq_left hz,ite_eq_left hz]
        exact runIndexed_refines fallback N bits (.remaining choice.rest) pos hpos
      · simp only [dite_eq_right hz,ite_eq_right hz]
        by_cases he : b.value≤a.value
        · simp only [dite_eq_left he,ite_eq_left he]
          exact runIndexed_refines fallback N bits (.selected choice.head.1) pos hpos
        · simp only [dite_eq_right he,ite_eq_right he]
          by_cases hRead : pos<N
          · simp only [dite_eq_left hRead,FixedBinaryWord.coinStep_digit]
            have hlt : a.value<b.value:=by omega
            by_cases hd : bits ⟨pos,hRead⟩=denominatorDigit a.value b.value
            · simp only [ite_eq_left hd]
              have ih:=runIndexed_refines fallback N bits (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
              simpa only [Cursor.reference,FixedBinaryWord.coinStep_residual a b hlt] using ih
            · simp only [ite_eq_right hd]
              have ih:=runIndexed_refines fallback N bits (if bits ⟨pos,hRead⟩ then .remaining choice.rest else .selected choice.head.1) (pos+1) (by omega)
              cases hBit : bits ⟨pos,hRead⟩ <;> simpa only [hBit,Bool.false_eq_true,ite_false,ite_true,Cursor.reference] using ih
          · simp only [dite_eq_right hRead]
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hW : choice.weights=weights:=by
      unfold prepare at he
      split at he
      · cases he
      · cases he
      · dsimp only at he
        split at he
        · cases Preparation.ask.inj he; rfl
        · cases he
    simp only [pending,Cursor.rank]
    rw [hW]
    omega
  · apply Prod.Lex.right
    have hL:=rest_length choice
    simp only [Cursor.rank]
    omega
  · apply Prod.Lex.right
    simp only [Cursor.rank]
    rw [choice.head_pair]
    simp only [List.length_cons]
    omega
  all_goals apply Prod.Lex.left
  all_goals omega


def run {α : Type*} (fallback : α) (N : ℕ) (weights : WeightList α) (bits : Fin N→Bool) : Option α×ℕ:=
  runIndexed fallback N bits (.remaining weights) 0 (Nat.zero_le N)

def output {α : Type*} (fallback : α) (N : ℕ) (weights : WeightList α) (bits : Fin N→Bool) : α:=
  (run fallback N weights bits).1.getD fallback

theorem run_refines {α : Type*} (fallback : α) (N : ℕ) (weights : WeightList α) (bits : Fin N→Bool) :
    run fallback N weights bits=(categoricalMachine fallback).run N (.remaining weights.reference) bits:=by
  rw [WordStateMachine.run_eq_numeric]
  exact runIndexed_refines fallback N bits (.remaining weights) 0 (Nat.zero_le N)

theorem runIndexed_position {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N→Bool)
    (cursor : Cursor α) (pos : ℕ) (hpos : pos≤N) :
    pos≤(runIndexed fallback N bits cursor pos hpos).2 ∧ (runIndexed fallback N bits cursor pos hpos).2≤N:=by
  rw [runIndexed_refines]
  rw [(categoricalMachine fallback).runCursorIndexed_window N bits cursor.reference pos (N-pos) (by omega)]
  have hb:=(categoricalMachine fallback).runCursor_refines (N-pos) cursor.reference
    (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  have ht:=(categoricalMachine fallback).cursorSpecification cursor.reference |>.sample_bits_le (N-pos)
    (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  change _≤(N-pos) at ht
  rw [←hb] at ht
  simp only [WordStateMachine.offsetConsumed]
  constructor <;> omega

theorem run_failure_iff {α : Type*} (fallback : α) (N : ℕ) (weights : WeightList α) (bits : Fin N→Bool) :
    (run fallback N weights bits).1=none ↔
      ((categoricalMachine fallback).run N (.remaining weights.reference) bits).1=none:=by
  rw [run_refines]

theorem output_refines {α : Type*} (fallback : α) (N : ℕ) (weights : WeightList α) (bits : Fin N→Bool) :
    output fallback N weights bits=(categoricalMachine fallback).output N (.remaining weights.reference) fallback bits:=by
  unfold output WordStateMachine.output
  rw [run_refines]

end Blotto.BinaryCategoricalRun

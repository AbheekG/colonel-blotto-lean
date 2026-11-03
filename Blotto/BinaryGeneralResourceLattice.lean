import Blotto.BinaryGeneralResourceRun
import Blotto.RationalResourceWordHeight
import Blotto.RationalPRGResourceBitWidth
import Blotto.RationalPRGLatticeInput
import Blotto.BinaryLottoResourceInput

/-! Actual native resource states preserve the input rational lattice and
coordinate box through each selected pair. Canonical stored state and all
seven-opcode pair registers therefore have widths derived from the fixed D,
independent of update count. Lattice/unit promises are explicit input premises;
no caller provides a reached-state word bound or pair final-height oracle. -/

namespace Blotto.BinaryGeneralResourceLattice
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair BinaryGeneralResourceChoice
open BinaryGeneralResourceRun

variable {n : ℕ}

def StateInvariant (capacity : FixedArrayTable n SignedWord) (D : ℕ) (state : Certified capacity) : Prop:=
  state.reference.resource.OnLattice D ∧
    InBox (fun j=>(value (capacity.read j) : ℝ)) state.reference.resource.realAllocation

theorem initial_invariant (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (D : ℕ) (hLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0≤value (resource.read j) ∧ value (resource.read j)≤value (capacity.read j)) :
    StateInvariant capacity D (initial capacity resource hC hR):=by
  rw [StateInvariant,initial_reference]
  constructor
  · intro j
    rw [RationalActiveResources.initial,RationalResourceArray.allocation_ofAllocation]
    exact hLattice j
  · intro j
    change (0 : ℝ)≤((RationalResourceArray.ofAllocation (fun j=>value (resource.read j))).allocation j : ℝ) ∧
      ((RationalResourceArray.ofAllocation (fun j=>value (resource.read j))).allocation j : ℝ)≤(value (capacity.read j) : ℝ)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact_mod_cast hBox j

theorem selected_invariant {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (D : ℕ) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j))) (state : Certified capacity)
    (hs : StateInvariant capacity D state) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail) (upper : Bool) :
    StateInvariant capacity D (selected hC state a b tail he upper):=by
  rw [StateInvariant,selected_reference]
  have hz : (if upper then (state.reference.pair a b tail he).upper else (state.reference.pair a b tail he).lower)=
      (state.reference.pair a b tail he).lower ∨
      (if upper then (state.reference.pair a b tail he).upper else (state.reference.pair a b tail he).lower)=
      (state.reference.pair a b tail he).upper:=by cases upper; exact Or.inl rfl; exact Or.inr rfl
  exact ⟨state.reference.update_on_lattice hLattice hs.1 a b tail he hz,
    state.reference.update_inBox a b tail he hs.2 hz⟩

theorem choice_select_invariant {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hs : StateInvariant capacity D choice.state) (branch : Bool) : StateInvariant capacity D (choice.select branch):=by
  rw [choice.select_eq]
  exact selected_invariant hC D hLattice choice.state hs _ _ _ _ branch

theorem state_wordWidth {capacity : FixedArrayTable n SignedWord} (state : Certified capacity)
    (D : ℕ) (hD : 0<D) (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state) (j : Fin n) :
    width (state.state.resource.read j)≤1+2*binaryWordWidth D:=by
  have hBox : 0≤value (state.state.resource.read j) ∧ value (state.state.resource.read j)≤1:=by
    have hb:=hs.2 j
    simp only [Certified.reference,RationalResourceArray.realAllocation,RationalResourceArray.allocation_ofAllocation,
      BinaryResourceState.allocation] at hb
    change (0 : ℝ)≤(value (state.state.resource.read j) : ℝ) ∧
      (value (state.state.resource.read j) : ℝ)≤(value (capacity.read j) : ℝ) at hb
    have hq : 0≤value (state.state.resource.read j) ∧ value (state.state.resource.read j)≤value (capacity.read j):=by exact_mod_cast hb
    exact ⟨hq.1,hq.2.trans (hUnit j)⟩
  have hl:=hs.1 j
  simp only [Certified.reference,RationalResourceArray.allocation_ofAllocation,BinaryResourceState.allocation] at hl
  change OnRationalLattice D (value (state.state.resource.read j)) at hl
  exact (state.canonical j).2.trans (rationalWordWidth_lattice_bound hD hl hBox)

theorem capacity_wordWidth (capacity : FixedArrayTable n SignedWord) (hC : ∀ j,CanonicalWord (capacity.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0≤value (capacity.read j) ∧ value (capacity.read j)≤1) (j : Fin n) :
    width (capacity.read j)≤1+2*binaryWordWidth D:=
  (hC j).2.trans (rationalWordWidth_lattice_bound hD (hLattice j) (hBox j))

theorem pair_lattice {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j))) (hs : StateInvariant capacity D state) :
    (pairSource hC state a b tail he).pair.Lattice D:=by
  rw [pairSource_pair]
  exact ⟨hLattice a,hLattice b,hs.1 a,hs.1 b⟩

theorem pair_trace_wordBounds {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state) :
    BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code (pairSource hC state a b tail he).inputs
      (3+2*binaryWordWidth D):=by
  let source:=pairSource hC state a b tail he
  apply BinaryRegisterHeightBridge.final_semantic_trace _ _ source.inputs_canonical
  rw [source.inputs_interpreted]
  exact RationalPairProgram.final_wordBounds_lattice source.pair hD (pair_lattice hC state a b tail he D hLattice hs)
    (hUnit a) (hUnit b)

theorem pair_run_wordBounds {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state) :
    BinaryRationalRegisterProgram.WordBounds (pairSource hC state a b tail he).run (3+2*binaryWordWidth D):=
  BinaryRationalRegisterProgram.trace_bounds_final _ _ _ (pair_trace_wordBounds hC state a b tail he D hD hLattice hUnit hs)

theorem choice_register_wordBounds {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D choice.state) :
    BinaryRationalRegisterProgram.WordBounds choice.registers (3+2*binaryWordWidth D):=by
  rw [choice.registers_correct]
  exact pair_run_wordBounds hC _ _ _ _ _ D hD hLattice hUnit hs


def CursorInvariant {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D : ℕ) : Cursor capacity hC→Prop
  | .ready state=>StateInvariant capacity D state
  | .coin choice _ _ _ _=>StateInvariant capacity D choice.state

theorem prepared_invariant {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D : ℕ) (state : Certified capacity) (hs : StateInvariant capacity D state)
    (choice : Choice capacity hC) (hp : BinaryGeneralResourceChoice.prepare capacity hC state=.ask choice) :
    CursorInvariant D (pending choice):=by
  have hState : choice.state=state:=by
    unfold BinaryGeneralResourceChoice.prepare at hp
    split at hp
    · cases Preparation.ask.inj hp; rfl
    · cases hp
  change StateInvariant capacity D choice.state
  rw [hState]
  exact hs

-- This path predicate follows the actual native loop, including every pending
-- residual and exhaustion. Its state premise gives fixed-D widths at every
-- visited resource and actual pair preparation.
def PathInvariant {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hpos : pos≤N) : Prop:=
  CursorInvariant D cursor ∧
  match cursor with
  | .ready state=>match hp : BinaryGeneralResourceChoice.prepare capacity hC state with
    | .done _=>True
    | .ask choice=>PathInvariant D N bits (pending choice) pos hpos
  | .coin choice a b hb hab=>
      if hz : a.isZero=true then PathInvariant D N bits (.ready (choice.select false) : Cursor capacity hC) pos hpos else
        if he : a.same b=true then PathInvariant D N bits (.ready (choice.select true) : Cursor capacity hC) pos hpos else
          if hRead : pos<N then
            let next:=a.coinStep b
            have hlt : a.value<b.value:=lt_of_le_of_ne hab (fun h=>he ((a.same_value b).mpr h))
            if bits ⟨pos,hRead⟩=next.1 then
              PathInvariant D N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos+1) (by omega)
            else PathInvariant D N bits (.ready (choice.select (!bits ⟨pos,hRead⟩)) : Cursor capacity hC) (pos+1) (by omega)
          else True
termination_by (N-pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hState : choice.state=state:=by
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

theorem path_invariant {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (D : ℕ) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (N : ℕ) (bits : Fin N→Bool) (cursor : Cursor capacity hC) (pos : ℕ) (hpos : pos≤N)
    (hs : CursorInvariant D cursor) : PathInvariant D N bits cursor pos hpos:=by
  cases cursor with
  | ready state=>
      unfold PathInvariant
      dsimp only
      refine ⟨hs,?_⟩
      cases hp : BinaryGeneralResourceChoice.prepare capacity hC state with
      | done _=>trivial
      | ask choice=>exact path_invariant D hLattice N bits (pending choice) pos hpos (prepared_invariant D state hs choice hp)
  | coin choice a b hb hab=>
      unfold PathInvariant
      dsimp only
      refine ⟨hs,?_⟩
      split
      · exact path_invariant D hLattice N bits (.ready (choice.select false) : Cursor capacity hC) pos hpos
          (choice_select_invariant choice D hLattice hs false)
      · split
        · exact path_invariant D hLattice N bits (.ready (choice.select true) : Cursor capacity hC) pos hpos
            (choice_select_invariant choice D hLattice hs true)
        · split
          · split
            · exact path_invariant D hLattice N bits _ (pos+1) _ hs
            · exact path_invariant D hLattice N bits _ (pos+1) _ (choice_select_invariant choice D hLattice hs _)
          · trivial
termination_by (N-pos,cursor.rank)
decreasing_by
  all_goals subst cursor
  · apply Prod.Lex.right
    have hState : choice.state=state:=by
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

theorem run_completed_invariant {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (D : ℕ) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j))) (state : Certified capacity)
    (hs : StateInvariant capacity D state) (N : ℕ) (bits : Fin N→Bool) (result : Certified capacity)
    (hSuccess : (run hC N state bits).1=some result) : StateInvariant capacity D result:=by
  have hr:=run_success_reference hC N state result bits hSuccess
  have hl:=rationalResourceMachine_lattice_completed (fun j=>value (capacity.read j)) D hLattice (.ready state.reference)
    N bits hs.1 hr
  have hi : RationalResourceInvariant (fun j=>value (capacity.read j))
      (∑ j : Fin n,state.reference.resource.realAllocation j) state.reference:=⟨hs.2,rfl⟩
  have hb:=run_invariant hC _ N state result bits hi hSuccess
  exact ⟨hl,hb.1⟩


theorem pair_work_bound {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state) :
    (pairSource hC state a b tail he).runWithWork.2≤
      7*(12000*(4+2*binaryWordWidth D)^3+28*(7+4*binaryWordWidth D)+4):=by
  have ht:=pair_trace_wordBounds hC state a b tail he D hD hLattice hUnit hs
  have hw:=BinaryRationalRegisterProgram.work_bound_of_trace RealPairProgram.code
    (pairSource hC state a b tail he).inputs (3+2*binaryWordWidth D) ht
  rw [BinaryRationalPairProgram.Source.runWithWork,BinaryRationalRegisterProgram.runWithWork_refines]
  have hLength : RealPairProgram.code.length=7:=rfl
  have hSize : (pairSource hC state a b tail he).inputs.size=5:=rfl
  rw [hLength,hSize] at hw
  have he : 3+2*binaryWordWidth D+1=4+2*binaryWordWidth D:=by omega
  rw [he] at hw
  convert hw using 1; ring

theorem completed_state_wordWidth {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (state : Certified capacity) (hs : StateInvariant capacity D state)
    (N : ℕ) (bits : Fin N→Bool) (result : Certified capacity) (hSuccess : (run hC N state bits).1=some result) (j : Fin n) :
    width (result.state.resource.read j)≤1+2*binaryWordWidth D:=
  state_wordWidth result D hD hUnit (run_completed_invariant hC D hLattice state hs N bits result hSuccess) j

theorem normalized_initial_lattice (source : RationalPRGInput n) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,value (capacity.read j)=source.lengths j)
    (hInitial : (∀ j,value (resource.read j)=source.richInitial j) ∨ (∀ j,value (resource.read j)=source.poorInitial j)) :
    StateInvariant capacity source.latticeDenominator (initial capacity resource hC hR):=by
  apply initial_invariant
  · intro j
    rcases hInitial with hi|hi
    · rw [hi j]; exact source.richInitial_on_lattice j
    · rw [hi j]; exact source.poorInitial_on_lattice j
  · intro j
    rw [hCapacity j]
    rcases hInitial with hi|hi
    · rw [hi j]
      change 0≤source.lengths j ∧ source.lengths j≤source.lengths j
      exact ⟨(mul_pos (by norm_num) (source.positive j)).le,le_rfl⟩
    · rw [hi j]
      have hl : 0≤source.lengths j:=(mul_pos (by norm_num) (source.positive j)).le
      exact ⟨mul_nonneg source.b_pos.le hl,(mul_le_mul_of_nonneg_right source.b_le hl).trans_eq (one_mul _)⟩

theorem normalized_completed_wordWidth (source : RationalPRGInput n) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,value (capacity.read j)=source.lengths j)
    (hInitial : (∀ j,value (resource.read j)=source.richInitial j) ∨ (∀ j,value (resource.read j)=source.poorInitial j))
    (N : ℕ) (bits : Fin N→Bool) (result : Certified capacity)
    (hSuccess : (initialRun capacity resource hC hR N bits).1=some result) (j : Fin n) :
    width (result.state.resource.read j)≤3+2*source.inputWordWidth:=by
  have hl : ∀ j,OnRationalLattice source.latticeDenominator (value (capacity.read j)):=by
    intro j; rw [hCapacity j]; exact source.lengths_on_lattice j
  have hu : ∀ j,value (capacity.read j)≤1:=by
    intro j; rw [hCapacity j]; exact (source.small_fields j).trans source.b_le
  have hw:=completed_state_wordWidth hC source.latticeDenominator source.latticeDenominator_pos hl hu
    (initial capacity resource hC hR) (normalized_initial_lattice source capacity resource hC hR hCapacity hInitial) N bits result hSuccess j
  have hd:=source.latticeDenominator_wordWidth
  omega


theorem choice_probability_wordWidth {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D choice.state) :
    width choice.probability≤1+2*binaryWordWidth D:=by
  let source:=pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair
  have hc : CanonicalWord choice.probability:=by
    unfold Choice.probability
    rw [choice.registers_correct]
    exact source.run_canonical 11
  have hv : value choice.probability=source.pair.probability:=by
    unfold Choice.probability
    rw [choice.registers_correct]
    exact source.run_probability
  have hw:=hc.2
  rw [hv] at hw
  exact hw.trans (RationalPairProgram.probability_wordWidth_lattice source.pair hD
    (pair_lattice hC choice.state _ _ _ _ D hLattice hs) (hUnit choice.first))

theorem choice_probability_numbers_le {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D choice.state) :
    BinaryBigEndian.littleValue choice.probability.numerator≤D ∧
      BinaryBigEndian.littleValue choice.probability.denominator≤D:=by
  rw [choice.probability_numbers.1,choice.probability_numbers.2]
  have hPair : (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).Lattice D:=
    ⟨hLattice _,hLattice _,hs.1 _,hs.1 _⟩
  exact ⟨RationalRoundingPair.words_num_le _ hD hPair (hUnit choice.first),
    RationalRoundingPair.words_den_le _ hD hPair (hUnit choice.first)⟩

theorem prepared_coin_buffer_width {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D choice.state) :
    max choice.probability.numerator.length choice.probability.denominator.length≤1+2*binaryWordWidth D:=
  choice_probability_wordWidth choice D hD hLattice hUnit hs

theorem normalized_initial_path (source : RationalPRGInput n) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,value (capacity.read j)=source.lengths j)
    (hInitial : (∀ j,value (resource.read j)=source.richInitial j) ∨ (∀ j,value (resource.read j)=source.poorInitial j))
    (N : ℕ) (bits : Fin N→Bool) :
    PathInvariant source.latticeDenominator N bits (.ready (initial capacity resource hC hR) : Cursor capacity hC) 0 (Nat.zero_le N):=by
  apply path_invariant
  · intro j; rw [hCapacity j]; exact source.lengths_on_lattice j
  · exact normalized_initial_lattice source capacity resource hC hR hCapacity hInitial

end Blotto.BinaryGeneralResourceLattice

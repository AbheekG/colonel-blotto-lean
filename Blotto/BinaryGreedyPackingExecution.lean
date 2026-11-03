import Blotto.BinaryGreedyPacking
import Blotto.BinaryTerminalGrouping

/-! The actual retained packing path conses current members, reverses each
closed group once, and conses its output groups. There is no growing-list append.
This executable annotation returns that exact output plus structurally counted
scan/control/list visits and actual add/comparison callbacks. No primitive price
oracle, binary backend time, compiler stack, physical allocator or GC is claimed. -/

namespace Blotto.BinaryGreedyPackingExecution
open BinaryRationalNormalization BinaryRationalEncoding

structure Counts where
  scans : ℕ
  additions : ℕ
  comparisons : ℕ
  reverseVisits : ℕ
  memberCons : ℕ
  groupCons : ℕ
  controls : ℕ
  deriving Repr,DecidableEq

def Counts.add (first second : Counts) : Counts:=
  ⟨first.scans+second.scans,first.additions+second.additions,first.comparisons+second.comparisons,
    first.reverseVisits+second.reverseVisits,first.memberCons+second.memberCons,
    first.groupCons+second.groupCons,first.controls+second.controls⟩

-- This actual reverse-cons loop returns its state and one visit per input cell.
def reverseWithVisits {α : Type*} : List α→List α→List α×ℕ
  | [],accumulator=>(accumulator,0)
  | item::rest,accumulator=>
      let later:=reverseWithVisits rest (item::accumulator)
      (later.1,later.2+1)

theorem reverseWithVisits_state {α : Type*} (items accumulator : List α) :
    (reverseWithVisits items accumulator).1=items.reverse++accumulator:=by
  induction items generalizing accumulator with
  | nil=>rfl
  | cons item rest ih=>
      rw [reverseWithVisits,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem reverseWithVisits_count {α : Type*} (items accumulator : List α) :
    (reverseWithVisits items accumulator).2=items.length:=by
  induction items generalizing accumulator with
  | nil=>rfl
  | cons item rest ih=>simp [reverseWithVisits,ih]

def packAux {α : Type*} (length : α→SignedWord) (budget : SignedWord) :
    List α→SignedWord→List α→List (List α×SignedWord)×Counts
  | current,total,[]=>
      let reversed:=reverseWithVisits current []
      ([(reversed.1,total)],⟨0,0,0,reversed.2,0,1,1⟩)
  | current,total,item::rest=>
      let next:=BinaryRationalOpcode.apply .add total (length item)
      if BinaryRationalArithmetic.lessEqual next budget then
        let later:=packAux length budget (item::current) next rest
        (later.1,(⟨1,1,1,0,1,0,2⟩ : Counts).add later.2)
      else
        let reversed:=reverseWithVisits current []
        let later:=packAux length budget [item] (length item) rest
        ((reversed.1,total)::later.1,(⟨1,1,1,reversed.2,1,1,2⟩ : Counts).add later.2)

def pack {α : Type*} (length : α→SignedWord) (budget : SignedWord) : List α→List (List α×SignedWord)×Counts
  | []=>([],⟨0,0,0,0,0,0,1⟩)
  | item::rest=>
      let later:=packAux length budget [item] (length item) rest
      (later.1,(⟨1,0,0,0,1,0,1⟩ : Counts).add later.2)

theorem packAux_state {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    (packAux length budget current total rest).1=BinaryGreedyPacking.packAux length budget current total rest:=by
  induction rest generalizing current total with
  | nil=>simp [packAux,BinaryGreedyPacking.packAux,reverseWithVisits_state]
  | cons item rest ih=>
      unfold packAux BinaryGreedyPacking.packAux
      dsimp only
      split
      · exact ih _ _
      · rw [ih]
        simp [reverseWithVisits_state]

theorem pack_state {α : Type*} (length : α→SignedWord) (budget : SignedWord) (items : List α) :
    (pack length budget items).1=BinaryGreedyPacking.packedGroups length budget items:=by
  cases items with
  | nil=>rfl
  | cons item rest=>exact packAux_state _ _ _ _ _

theorem packAux_callbacks {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    (packAux length budget current total rest).2.scans=rest.length ∧
      (packAux length budget current total rest).2.additions=rest.length ∧
      (packAux length budget current total rest).2.comparisons=rest.length ∧
      (packAux length budget current total rest).2.memberCons=rest.length ∧
      (packAux length budget current total rest).2.controls=2*rest.length+1:=by
  induction rest generalizing current total with
  | nil=>simp [packAux,reverseWithVisits_count]
  | cons item rest ih=>
      unfold packAux
      dsimp only
      split
      · obtain ⟨hs,ha,hc,hm,ht⟩:=ih (item::current) (BinaryRationalOpcode.apply .add total (length item))
        simp only [Counts.add,List.length_cons]
        exact ⟨by omega,by omega,by omega,by omega,by omega⟩
      · obtain ⟨hs,ha,hc,hm,ht⟩:=ih [item] (length item)
        simp only [Counts.add,List.length_cons]
        exact ⟨by omega,by omega,by omega,by omega,by omega⟩

theorem packAux_reverseVisits {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    (packAux length budget current total rest).2.reverseVisits=current.length+rest.length:=by
  induction rest generalizing current total with
  | nil=>simp [packAux,reverseWithVisits_count]
  | cons item rest ih=>
      unfold packAux
      dsimp only
      split <;> simp only [Counts.add,ih,List.length_cons,List.length_nil,reverseWithVisits_count] <;> omega

theorem packAux_groupCons {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    (packAux length budget current total rest).2.groupCons=(packAux length budget current total rest).1.length:=by
  induction rest generalizing current total with
  | nil=>rfl
  | cons item rest ih=>
      unfold packAux
      dsimp only
      split <;> simp only [Counts.add,ih,List.length_cons] <;> omega

theorem packAux_groups_le {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    (packAux length budget current total rest).1.length≤rest.length+1:=by
  induction rest generalizing current total with
  | nil=>simp [packAux]
  | cons item rest ih=>
      unfold packAux
      dsimp only
      split
      · exact (ih _ _).trans (by simp only [List.length_cons]; omega)
      · have h:=ih [item] (length item)
        simp only [List.length_cons]
        omega

theorem pack_counts {α : Type*} (length : α→SignedWord) (budget : SignedWord) (items : List α) :
    (pack length budget items).2.scans=items.length ∧
      (pack length budget items).2.additions=items.length-1 ∧
      (pack length budget items).2.comparisons=items.length-1 ∧
      (pack length budget items).2.memberCons=items.length ∧
      (pack length budget items).2.reverseVisits=items.length ∧
      (pack length budget items).2.groupCons=(pack length budget items).1.length ∧
      (pack length budget items).1.length≤ items.length ∧
      (pack length budget items).2.controls≤2*items.length+1:=by
  cases items with
  | nil=>simp [pack]
  | cons item rest=>
      obtain ⟨hs,ha,hc,hm,ht⟩:=packAux_callbacks length budget [item] (length item) rest
      have hr:=packAux_reverseVisits length budget [item] (length item) rest
      have hg:=packAux_groupCons length budget [item] (length item) rest
      have hl:=packAux_groups_le length budget [item] (length item) rest
      simp only [pack,Counts.add,List.length_cons,List.length_nil] at *
      exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

-- Structural work charges one cell visit/cons/control or arithmetic callback
-- occurrence. The callback's Boolean bit complexity is not unit-priced here.
def structuralWork {α : Type*} (length : α→SignedWord) (budget : SignedWord) (items : List α) : ℕ:=
  let counts:=(pack length budget items).2
  counts.scans+counts.additions+counts.comparisons+counts.reverseVisits+
    counts.memberCons+counts.groupCons+counts.controls

theorem structuralWork_bound {α : Type*} (length : α→SignedWord) (budget : SignedWord) (items : List α) :
    structuralWork length budget items≤8*items.length+1:=by
  obtain ⟨hs,ha,hc,hm,hr,hg,hl,ht⟩:=pack_counts length budget items
  unfold structuralWork
  dsimp only
  omega

theorem terminal_groupCons_le_three {n : ℕ} (input : BinaryTerminalGrouping.Input n)
    (source : RationalTerminalLotto n) (hC : input.Canonical) (hr : input.Refines source) :
    (pack input.length.read input.budget (BinaryTerminalGrouping.uniformItems input)).2.groupCons≤3:=by
  obtain ⟨_,_,_,_,_,hg,_,_⟩:=pack_counts input.length.read input.budget (BinaryTerminalGrouping.uniformItems input)
  rw [hg,pack_state]
  change (BinaryTerminalGrouping.packed input).length≤3
  have hc:=BinaryTerminalGrouping.groups_count input source hC hr
  simp only [BinaryTerminalGrouping.groups,List.length_map] at hc
  omega

theorem terminal_structuralWork_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    structuralWork input.length.read input.budget (BinaryTerminalGrouping.uniformItems input)≤8*n+1:=by
  have h:=structuralWork_bound input.length.read input.budget (BinaryTerminalGrouping.uniformItems input)
  have hl : (BinaryTerminalGrouping.uniformItems input).length≤n:=by
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  omega


theorem pack_canonical {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (hLength : ∀ item,CanonicalWord (length item)) (items : List α) :
    ∀ entry∈(pack length budget items).1,CanonicalWord entry.2:=by
  rw [pack_state]
  exact BinaryGreedyPacking.packedGroups_canonical length budget hLength items

theorem pack_refines {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (hLength : ∀ item,CanonicalWord (length item)) (hBudget : CanonicalWord budget) (items : List α) :
    BinaryGreedyPacking.interpreted (pack length budget items).1=
      rationalPackedGroups (fun item=>value (length item)) (value budget) items:=by
  rw [pack_state]
  exact BinaryGreedyPacking.packedGroups_refines length budget hLength hBudget items

theorem pack_members {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (hLength : ∀ item,CanonicalWord (length item)) (hBudget : CanonicalWord budget) (items : List α) :
    (pack length budget items).1.map Prod.fst=rationalGreedyGroups (fun item=>value (length item)) (value budget) items:=by
  rw [pack_state]
  exact BinaryGreedyPacking.packedGroups_members length budget hLength hBudget items

theorem pack_totals {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (hLength : ∀ item,CanonicalWord (length item)) (hBudget : CanonicalWord budget) (items : List α) :
    ∀ entry∈(pack length budget items).1,value entry.2=rationalGroupLength (fun item=>value (length item)) entry.1:=by
  rw [pack_state]
  exact BinaryGreedyPacking.packedGroups_totals length budget hLength hBudget items

def terminalPack {n : ℕ} (input : BinaryTerminalGrouping.Input n) : List (List (Fin n)×SignedWord)×Counts:=
  pack input.length.read input.budget (BinaryTerminalGrouping.uniformItems input)

theorem terminalPack_state {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (terminalPack input).1=BinaryTerminalGrouping.packed input:=pack_state _ _ _

end Blotto.BinaryGreedyPackingExecution

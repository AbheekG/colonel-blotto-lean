import Blotto.BinaryReflectedFourSetup
import Blotto.RationalPackedGroups

/-! Boolean next-fit packing scans original item order, caches each tentative
sum once, and stores closed group totals. The exact source group lists and sums
are obtained by refinement, without numerical rational encoding. -/

namespace Blotto.BinaryGreedyPacking
open BinaryRationalNormalization BinaryRationalEncoding

def packAux {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → SignedWord → List α → List (List α × SignedWord)
  | current,total,[] => [(current.reverse,total)]
  | current,total,item::rest =>
    let next := BinaryRationalOpcode.apply .add total (length item)
    if BinaryRationalArithmetic.lessEqual next budget then packAux length budget (item::current) next rest
    else (current.reverse,total) :: packAux length budget [item] (length item) rest

def packedGroups {α : Type*} (length : α → SignedWord) (budget : SignedWord) : List α → List (List α × SignedWord)
  | [] => []
  | item::rest => packAux length budget [item] (length item) rest

noncomputable def interpreted {α : Type*} (groups : List (List α × SignedWord)) : List (List α × ℚ) :=
  groups.map (fun entry => (entry.1,value entry.2))

theorem packAux_refines {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (hc : ∀ item, CanonicalWord (length item)) (hb : CanonicalWord budget)
    (current : List α) (total : SignedWord) (ht : CanonicalWord total) (rest : List α) :
    interpreted (packAux length budget current total rest) =
      rationalPackSumsAux (fun item => value (length item)) (value budget) current (value total) rest := by
  induction rest generalizing current total with
  | nil => rfl
  | cons item rest ih =>
    have hn := BinaryReflectedFourSetup.opcode_canonical .add total (length item) ht (hc item)
    have hv := BinaryRationalOpcode.apply_value .add total (length item) ht.1 (hc item).1
    have he := BinaryRationalArithmetic.lessEqual_iff _ budget hn.1 hb.1
    rw [hv] at he
    change BinaryRationalArithmetic.lessEqual (BinaryRationalOpcode.apply .add total (length item)) budget=true ↔
      value total + value (length item) ≤ value budget at he
    unfold packAux rationalPackSumsAux
    by_cases hFit : value total + value (length item) ≤ value budget
    · rw [ite_eq_left (he.mpr hFit),ite_eq_left hFit]
      have h := ih (item::current) (BinaryRationalOpcode.apply .add total (length item)) hn
      simpa only [hv,RealArithmeticOp.applyRat] using h
    · rw [ite_eq_right (fun h => hFit (he.mp h)),ite_eq_right hFit]
      simp only [interpreted,List.map_cons]
      exact congrArg ((current.reverse,value total)::·) (ih [item] (length item) (hc item))

theorem packedGroups_refines {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (hc : ∀ item, CanonicalWord (length item)) (hb : CanonicalWord budget) (items : List α) :
    interpreted (packedGroups length budget items) = rationalPackedGroups (fun item => value (length item)) (value budget) items := by
  cases items with
  | nil => rfl
  | cons item rest => exact packAux_refines length budget hc hb [item] (length item) (hc item) rest

theorem packAux_canonical {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (hc : ∀ item, CanonicalWord (length item)) (current : List α) (total : SignedWord) (ht : CanonicalWord total) (rest : List α) :
    ∀ entry ∈ packAux length budget current total rest, CanonicalWord entry.2 := by
  induction rest generalizing current total with
  | nil => intro entry he; have h := List.mem_singleton.mp he; subst entry; exact ht
  | cons item rest ih =>
    unfold packAux
    dsimp only
    split
    · exact ih _ _ (BinaryReflectedFourSetup.opcode_canonical .add _ _ ht (hc item))
    · intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact ht
      · exact ih _ _ (hc item) entry he

theorem packedGroups_canonical {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (hc : ∀ item, CanonicalWord (length item)) (items : List α) :
    ∀ entry ∈ packedGroups length budget items, CanonicalWord entry.2 := by
  cases items with
  | nil => simp [packedGroups]
  | cons item rest => exact packAux_canonical length budget hc [item] (length item) (hc item) rest

theorem packedGroups_members {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (hc : ∀ item, CanonicalWord (length item)) (hb : CanonicalWord budget) (items : List α) :
    (packedGroups length budget items).map Prod.fst = rationalGreedyGroups (fun item => value (length item)) (value budget) items := by
  have h := congrArg (List.map Prod.fst) (packedGroups_refines length budget hc hb items)
  rw [rationalPackedGroups_groups] at h
  simpa only [interpreted,List.map_map,Function.comp_def] using h

theorem packedGroups_totals {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (hc : ∀ item, CanonicalWord (length item)) (hb : CanonicalWord budget) (items : List α) :
    ∀ entry ∈ packedGroups length budget items, value entry.2 = rationalGroupLength (fun item => value (length item)) entry.1 := by
  intro entry he
  have hm : (entry.1,value entry.2) ∈ interpreted (packedGroups length budget items) := List.mem_map.mpr ⟨entry,he,rfl⟩
  rw [packedGroups_refines length budget hc hb items] at hm
  exact rationalPackedGroups_totals _ _ _ _ hm

end Blotto.BinaryGreedyPacking

import Blotto.GeneralPaperRaySearchControls

/-! Sort one crossing batch and binary-search its first infeasible point.
The returned adjacent bracket retains feasibility/infeasibility, lies in
the input bracket and contains no batch crossing in its open interior.
-/
namespace Blotto.GeneralPaperRayCrossingRefinement
open GeneralPaperRaySortedCrossings
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Bracket where
  lower : ℚ
  upper : ℚ

def narrow (query : ℚ → Bool × ℕ) (lo hi : ℚ) (points : List ℚ) : Option Bracket :=
  let values := array lo hi points
  let result := GeneralPaperRaySearchControls.selected (fun i => query (values.read i))
  if hr : 0<result.rank ∧ result.rank<(ordered lo hi points).length then
    some ⟨values.read ⟨result.rank-1,by omega⟩,values.read ⟨result.rank,hr.2⟩⟩
  else none

def Sound (query : ℚ → Bool × ℕ) (lo hi : ℚ) (points : List ℚ) (b : Bracket) : Prop :=
  lo≤b.lower ∧ b.lower<b.upper ∧ b.upper≤hi ∧
    (query b.lower).1=true ∧ (query b.upper).1=false ∧
      ∀ t∈points,¬(b.lower<t ∧ t<b.upper)

theorem narrow_sound (query : ℚ → Bool × ℕ) (lo hi : ℚ) (hOrder : lo<hi) (points : List ℚ)
    (hLower : (query lo).1=true) (hUpper : (query hi).1=false)
    (hDown : ∀ s t,lo≤s → s≤t → t≤hi → (query t).1=true → (query s).1=true) :
    ∃ b,narrow query lo hi points=some b ∧ Sound query lo hi points b := by
  let values := array lo hi points
  let qi := fun i => query (values.read i)
  let result := GeneralPaperRaySearchControls.selected qi
  have hMono : StrictMono values.read := read_strict lo hi points
  have hValid : GeneralPaperRayOracleSearch.Valid qi result.rank := by
    apply GeneralPaperRaySearchControls.selected_valid
    intro i j hij ht
    have hIBounds := ordered_bound lo hi hOrder.le points _ (read_mem lo hi points i)
    have hj := ordered_bound lo hi hOrder.le points _ (read_mem lo hi points j)
    exact hDown (values.read i) (values.read j) hIBounds.1 (hMono.monotone hij) hj.2 ht
  have hPos : 0<result.rank := by
    obtain ⟨i,hRead⟩ := mem_read lo hi points lo (lower_mem lo hi points)
    have ht : (qi i).1=true := by dsimp only [qi,values]; rw [hRead]; exact hLower
    have hh := (hValid.2 i).mp ht
    omega
  have hCap : result.rank<(ordered lo hi points).length := by
    obtain ⟨i,hRead⟩ := mem_read lo hi points hi (upper_mem lo hi points)
    have hh : result.rank ≤ i.val := by
      by_contra hn
      have ht := (hValid.2 i).mpr (show i.val<result.rank by omega)
      dsimp only [qi,values] at ht
      rw [hRead,hUpper] at ht
      contradiction
    exact hh.trans_lt i.isLt
  let leftIndex : Fin (ordered lo hi points).length := ⟨result.rank-1,by omega⟩
  let rightIndex : Fin (ordered lo hi points).length := ⟨result.rank,hCap⟩
  have hIndices : leftIndex<rightIndex := by change result.rank-1<result.rank; omega
  have hLeft : (query (values.read leftIndex)).1=true := (hValid.2 leftIndex).mpr hIndices
  have hRight : (query (values.read rightIndex)).1=false := by
    cases he : (query (values.read rightIndex)).1 with
    | false => rfl
    | true => have hh := (hValid.2 rightIndex).mp he; exact (Nat.lt_irrefl result.rank hh).elim
  have hL := ordered_bound lo hi hOrder.le points _ (read_mem lo hi points leftIndex)
  have hU := ordered_bound lo hi hOrder.le points _ (read_mem lo hi points rightIndex)
  refine ⟨⟨values.read leftIndex,values.read rightIndex⟩,?_,hL.1,hMono hIndices,hU.2,hLeft,hRight,?_⟩
  · simp only [narrow]
    change (if hr : 0<result.rank ∧ result.rank<(ordered lo hi points).length then
      some (⟨values.read ⟨result.rank-1,by omega⟩,values.read ⟨result.rank,hr.2⟩⟩ : Bracket) else none)=_
    rw [dite_eq_left ⟨hPos,hCap⟩]
  · intro t ht hInside
    have hMember : t∈ordered lo hi points := (ordered_mem lo hi points t).mpr
      (Or.inr (Or.inr ⟨ht,hL.1.trans hInside.1.le,hInside.2.le.trans hU.2⟩))
    obtain ⟨i,hRead⟩ := mem_read lo hi points t hMember
    by_cases hBefore : i.val<result.rank
    · have hh := hMono.monotone (show i ≤ leftIndex by change i.val≤result.rank-1; omega)
      change (array lo hi points).read i≤_ at hh
      rw [hRead] at hh
      exact (not_lt_of_ge hh) hInside.1
    · have hh := hMono.monotone (show rightIndex ≤ i by change result.rank ≤ i.val; omega)
      change _≤(array lo hi points).read i at hh
      rw [hRead] at hh
      exact (not_lt_of_ge hh) hInside.2

end Blotto.GeneralPaperRayCrossingRefinement

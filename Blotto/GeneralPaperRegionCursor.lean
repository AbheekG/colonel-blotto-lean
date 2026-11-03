import Blotto.GeneralPaperRetainedScalarValue

/-! A priced forward cursor consumes a requested number of actual regions.
Success preserves their order and the untouched suffix. Reads/copies use the
existing region scalar/reference price; no layout or payload is recomputed. -/
namespace Blotto.GeneralPaperRegionCursor
open GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Result (A : ℕ) where
  values : Option (List (Region A))
  remaining : List (Region A)
  work : ℕ

def run (S A : ℕ) : ℕ → List (Region A) → Result A
  | 0,regions => ⟨some [],regions,64 * (S + A + 1)⟩
  | _ + 1,[] => ⟨none,[],64 * (S + A + 1)⟩
  | count + 1,region :: regions =>
    let later := run S A count regions
    ⟨later.values.map (List.cons region),later.remaining,later.work + GeneralPaperLastRegionSelection.price S A region⟩

theorem on_prefix (S A : ℕ) (first rest : List (Region A)) :
    run S A first.length (first ++ rest) =
      ⟨some first,rest,(first.map (GeneralPaperLastRegionSelection.price S A)).sum + 64 * (S + A + 1)⟩ := by
  induction first with
  | nil => simp only [List.length_nil,List.nil_append,run,List.map_nil,List.sum_nil,Nat.zero_add]
  | cons region regions ih =>
    simp only [List.length_cons,List.cons_append,run,ih,Option.map_some,List.map_cons,List.sum_cons]
    congr 1
    omega

theorem take_drop (S A count : ℕ) (regions : List (Region A)) (hCount : count ≤ regions.length) :
    (run S A count regions).values = some (regions.take count) ∧
      (run S A count regions).remaining = regions.drop count := by
  have hLength : (regions.take count).length = count := by rw [List.length_take,Nat.min_eq_left hCount]
  have h := on_prefix S A (regions.take count) (regions.drop count)
  rw [List.take_append_drop,hLength] at h
  rw [h]
  exact ⟨rfl,rfl⟩

theorem consume_append (S A : ℕ) (first rest : List (Region A)) :
    (run S A first.length (first ++ rest)).values = some first ∧
      (run S A first.length (first ++ rest)).remaining = rest := by
  rw [on_prefix]
  exact ⟨rfl,rfl⟩

theorem work_on_prefix (S A : ℕ) (first rest : List (Region A)) :
    (run S A first.length (first ++ rest)).work =
      (first.map (GeneralPaperLastRegionSelection.price S A)).sum + 64 * (S + A + 1) := by rw [on_prefix]

theorem bounded_work (S A count : ℕ) (regions : List (Region A)) (P : ℕ)
    (hCount : count ≤ regions.length)
    (hPrice : ∀ region ∈ regions,GeneralPaperLastRegionSelection.price S A region ≤ P) :
    (run S A count regions).work ≤ count * P + 64 * (S + A + 1) := by
  induction count generalizing regions with
  | zero => simp only [run,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
    cases regions with
    | nil => simp only [List.length_nil] at hCount; omega
    | cons region regions =>
      have hp := hPrice region (List.mem_cons_self ..)
      have ht := ih regions (by simp only [List.length_cons] at hCount; omega)
        (fun region hr => hPrice region (List.mem_cons_of_mem _ hr))
      dsimp only [run]
      nlinarith only [hp,ht]

end Blotto.GeneralPaperRegionCursor

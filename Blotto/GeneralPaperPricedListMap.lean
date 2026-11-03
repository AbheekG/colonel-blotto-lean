import Blotto.GeneralPaperStaticMinimumScanPrice

/-! A priced list map, using the existing one-pass filterMap with always-
present callbacks. Concrete constructor callbacks supply their own price.
-/
namespace Blotto.GeneralPaperPricedListMap
set_option autoImplicit false

def run {α β : Type*} (W : ℕ) (evaluate : α → β × ℕ) (xs : List α) : List β × ℕ :=
  GeneralPaperPricedListStream.filterMap W (fun a => let c := evaluate a; (some c.1,c.2)) xs

theorem data {α β : Type*} (W : ℕ) (evaluate : α → β × ℕ) (xs : List α) :
    (run W evaluate xs).1=xs.map (fun a => (evaluate a).1) := by
  simp only [run,GeneralPaperPricedListStream.filterMap_data,List.filterMap_eq_map']

theorem length {α β : Type*} (W : ℕ) (evaluate : α → β × ℕ) (xs : List α) :
    (run W evaluate xs).1.length=xs.length := by rw [data,List.length_map]

theorem work {α β : Type*} (W C : ℕ) (evaluate : α → β × ℕ) (xs : List α)
    (h : ∀ a∈xs,(evaluate a).2≤C) : (run W evaluate xs).2≤(C+8*W)*xs.length+2*W :=
  GeneralPaperPricedListStream.filterMap_work W C _ xs h

end Blotto.GeneralPaperPricedListMap

import Blotto.GeneralPaperPowerQueryEnvelope

/-! Price the literal natural breakpoint clipping/stable sort/deduplication
used by fixed profit grids and source cells. Both endpoints and every
comparison/write are included. The returned list is the native ordered list.
-/
namespace Blotto.GeneralPaperNaturalOrderPrice
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def leRun (primitive : ℕ → ℕ) (a b : ℕ) : Bool × ℕ :=
  (decide (a≤b),GeneralPaperIntegerWordPrice.compare primitive a b)

def clip (primitive : ℕ → ℕ) (W U x : ℕ) : ℕ × ℕ :=
  (min x U,GeneralPaperIntegerWordPrice.compare primitive x U+primitive (1+binaryWordWidth (min x U))+16*W)

theorem clip_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U x : ℕ) (hx : x≤U) :
    (clip primitive W U x).2≤2*primitive (1+binaryWordWidth U)+16*W := by
  have ht := GeneralPaperIntegerWordPrice.compare_le primitive hMono x U (1+binaryWordWidth U)
    (Nat.add_le_add_left (binaryWordWidth_mono hx) 1) (Nat.le_refl _)
  have hw := hMono (Nat.add_le_add_left (binaryWordWidth_mono (Nat.min_le_right x U)) 1)
  unfold clip
  omega

def after (primitive : ℕ → ℕ) (W last : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([],2*W)
  | x::rest =>
    let test := GeneralPaperIntegerWordPrice.compare primitive x last
    if x=last then
      let later := after primitive W last rest
      (later.1,later.2+test+16*W)
    else
      let later := after primitive W x rest
      (x::later.1,later.2+test+16*W)

theorem after_data (primitive : ℕ → ℕ) (W last : ℕ) (values : List ℕ) :
    (after primitive W last values).1=GeneralPaperSortedBreakpoints.after last values := by
  induction values generalizing last with
  | nil => rfl
  | cons x rest ih =>
    rw [after,GeneralPaperSortedBreakpoints.after]
    dsimp only
    split
    · rw [ih]
    · rw [ih]

theorem after_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U last : ℕ) (hLast : last≤U)
    (values : List ℕ) (hValues : ∀ x∈values,x≤U) :
    (after primitive W last values).2≤(primitive (1+binaryWordWidth U)+16*W)*values.length+2*W := by
  induction values generalizing last with
  | nil => simp only [after,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons x rest ih =>
    have hx := hValues x List.mem_cons_self
    have hRest : ∀ y∈rest,y≤U := fun y hy => hValues y (List.mem_cons_of_mem _ hy)
    have ht := GeneralPaperIntegerWordPrice.compare_le primitive hMono x last (1+binaryWordWidth U)
      (Nat.add_le_add_left (binaryWordWidth_mono hx) 1) (Nat.add_le_add_left (binaryWordWidth_mono hLast) 1)
    rw [after]
    dsimp only
    split
    · have hh := ih last hLast hRest
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    · have hh := ih x hx hRest
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

def unique (primitive : ℕ → ℕ) (W : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([],2*W)
  | x::rest => let later := after primitive W x rest; (x::later.1,later.2+8*W)

theorem unique_data (primitive : ℕ → ℕ) (W : ℕ) (values : List ℕ) :
    (unique primitive W values).1=GeneralPaperSortedBreakpoints.unique values := by
  cases values with
  | nil => rfl
  | cons x rest => simp only [unique,after_data,GeneralPaperSortedBreakpoints.unique]

theorem unique_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (values : List ℕ)
    (hValues : ∀ x∈values,x≤U) :
    (unique primitive W values).2≤(primitive (1+binaryWordWidth U)+16*W)*values.length+2*W := by
  cases values with
  | nil => simp only [unique,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons x rest =>
    have hx := hValues x List.mem_cons_self
    have ht := after_work primitive hMono W U x hx rest (fun y hy => hValues y (List.mem_cons_of_mem _ hy))
    change (after primitive W x rest).2+8*W≤_
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def run (primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) : List ℕ × ℕ :=
  let clipped := GeneralPaperPricedListMap.run W (clip primitive W U) points
  let sorted := GeneralPaperPricedSort.run (leRun primitive) W (0::U::clipped.1)
  let distinct := unique primitive W sorted.1
  (distinct.1,clipped.2+sorted.2+distinct.2+16*W)

theorem data (primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) :
    (run primitive W U points).1=GeneralPaperSortedBreakpoints.ordered U points := by
  simp only [run,unique_data,GeneralPaperPricedSort.data,GeneralPaperPricedListMap.data,clip,leRun,
    GeneralPaperSortedBreakpoints.ordered]

def profile (n W P : ℕ) : ℕ := GeneralPaperPricedSort.profile (n+2) W P+(3*P+48*W)*(n+2)+20*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (points : List ℕ)
    (hPoints : ∀ x∈points,x≤U) :
    (run primitive W U points).2≤profile points.length W (primitive (1+binaryWordWidth U)) := by
  let P := primitive (1+binaryWordWidth U)
  let clipped := GeneralPaperPricedListMap.run W (clip primitive W U) points
  let input := 0::U::clipped.1
  let sorted := GeneralPaperPricedSort.run (leRun primitive) W input
  have hInput : ∀ x∈input,x≤U := by
    intro x hx
    rcases List.mem_cons.mp hx with hx|hx
    · subst x; exact Nat.zero_le _
    · rcases List.mem_cons.mp hx with hx|hx
      · subst x; exact Nat.le_refl _
      · have he : x∈points.map (fun y => min y U) := by
          simpa only [clipped,GeneralPaperPricedListMap.data,clip] using hx
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he
        exact Nat.min_le_right _ _
  have hLen : input.length=points.length+2 := by
    simp only [input,List.length_cons,clipped,GeneralPaperPricedListMap.length]
  have hc := GeneralPaperPricedListMap.work W (2*P+16*W) (clip primitive W U) points
    (fun x hx => clip_work primitive hMono W U x (hPoints x hx))
  have hs := GeneralPaperPricedSort.work (leRun primitive) W P input (by
    intro x hx y hy
    exact GeneralPaperIntegerWordPrice.compare_le primitive hMono x y (1+binaryWordWidth U)
      (Nat.add_le_add_left (binaryWordWidth_mono (hInput x hx)) 1)
      (Nat.add_le_add_left (binaryWordWidth_mono (hInput y hy)) 1))
  have hu := unique_work primitive hMono W U sorted.1 (by
    intro x hx
    exact hInput x ((GeneralPaperPricedSort.mem (leRun primitive) W input x).mp hx))
  rw [GeneralPaperPricedSort.length,hLen] at hu
  rw [hLen] at hs
  change clipped.2+sorted.2+(unique primitive W sorted.1).2+16*W≤_
  unfold profile
  change _≤GeneralPaperPricedSort.profile (points.length+2) W P+(3*P+48*W)*(points.length+2)+20*W
  change _≤(P+16*W)*(points.length+2)+2*W at hu
  change clipped.2≤(2*P+16*W+8*W)*points.length+2*W at hc
  nlinarith only [hc,hs,hu,Nat.zero_le (W*points.length),Nat.zero_le (P*points.length)]

end Blotto.GeneralPaperNaturalOrderPrice

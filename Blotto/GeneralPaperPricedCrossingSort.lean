import Blotto.GeneralPaperPricedCrossingPasses

/-! The whole filter/sort/deduplicate program returns the existing crossing
list exactly. A monotone rational-comparison price covers unit arithmetic
prices and the paper's actual-operand Rat prices with the same source data.
-/
namespace Blotto.GeneralPaperPricedCrossingSort
open GeneralPaperPricedCrossingPasses
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run (primitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : List ℚ × ℕ :=
  let filtered := filterRun primitive W lo hi points
  let sorted := GeneralPaperPricedSort.run (leRun primitive) W (lo::hi::filtered.1)
  let distinct := uniqueRun primitive W sorted.1
  (distinct.1,filtered.2+sorted.2+distinct.2+16*W)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) (points : List ℚ) :
    (run primitive W lo hi points).1=GeneralPaperRaySortedCrossings.ordered lo hi points := by
  simp only [run,unique_data,GeneralPaperPricedSort.data,filter_data,leRun,
    GeneralPaperRaySortedCrossings.ordered]

theorem length (primitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) (points : List ℚ) :
    (run primitive W lo hi points).1.length≤points.length+2 := by
  rw [data]
  exact GeneralPaperRaySortedCrossings.ordered_length lo hi points

theorem width (primitive : ℕ → ℕ) (W H : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hl : rationalWordWidth lo≤H) (hh : rationalWordWidth hi≤H)
    (hp : ∀ q∈points,rationalWordWidth q≤H) :
    ∀ q∈(run primitive W lo hi points).1,rationalWordWidth q≤H := by
  rw [data]
  intro q hq
  rcases (GeneralPaperRaySortedCrossings.ordered_mem lo hi points q).mp hq with he|he|⟨hq,_,_⟩
  · rw [he]; exact hl
  · rw [he]; exact hh
  · exact hp q hq

def profile (n W P : ℕ) : ℕ :=
  GeneralPaperPricedSort.profile (n+2) W P+(3*P+32*W)*(n+2)+20*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H : ℕ)
    (lo hi : ℚ) (points : List ℚ)
    (hl : rationalWordWidth lo≤H) (hh : rationalWordWidth hi≤H)
    (hp : ∀ q∈points,rationalWordWidth q≤H) :
    (run primitive W lo hi points).2≤profile points.length W (primitive H) := by
  let filtered := filterRun primitive W lo hi points
  let input := lo::hi::filtered.1
  let sorted := GeneralPaperPricedSort.run (leRun primitive) W input
  have hInput : ∀ q∈input,rationalWordWidth q≤H := by
    intro q hq
    rcases List.mem_cons.mp hq with he|hq
    · rw [he]; exact hl
    · rcases List.mem_cons.mp hq with he|hq
      · rw [he]; exact hh
      · have he : q∈points.filter (fun t => decide (lo≤t ∧ t≤hi)) := by
          simpa only [filtered,filter_data] using hq
        exact hp q (List.mem_filter.mp he).1
  have hLen : input.length≤points.length+2 := by
    have he := List.length_filter_le (fun t => decide (lo≤t ∧ t≤hi)) points
    simpa only [input,filtered,filter_data,List.length_cons] using Nat.add_le_add_right (Nat.add_le_add_right he 1) 1
  have hf := filter_work primitive hMono W H lo hi points hl hh hp
  have hs := (GeneralPaperPricedSort.work (leRun primitive) W (primitive H) input
    (fun a ha b hb => le_work primitive hMono a b H (hInput a ha) (hInput b hb))).trans
      (GeneralPaperPricedSort.profile_mono hLen)
  have hu := unique_work primitive hMono W H sorted.1 (fun q hq =>
    hInput q ((GeneralPaperPricedSort.mem (leRun primitive) W input q).mp hq))
  have hUnique : (uniqueRun primitive W sorted.1).2≤
      (primitive H+16*W)*(points.length+2)+2*W := by
    apply hu.trans
    have hn : sorted.1.length≤points.length+2 := by
      simpa only [sorted,GeneralPaperPricedSort.length] using hLen
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _
  change filtered.2+sorted.2+(uniqueRun primitive W sorted.1).2+16*W≤_
  unfold profile
  nlinarith only [hf,hs,hUnique]

theorem height_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W R : ℕ)
    (lo hi : ℚ) (points : List ℚ) (hl : RationalHeight lo R) (hh : RationalHeight hi R)
    (hp : ∀ q∈points,RationalHeight q R) :
    (run primitive W lo hi points).2≤profile points.length W (primitive (1+2*R)) :=
  work primitive hMono W (1+2*R) lo hi points
    (rationalWordWidth_of_height hl) (rationalWordWidth_of_height hh)
    (fun q hq => rationalWordWidth_of_height (hp q hq))

theorem bit_work (model : RationalCostModel) (W R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ q∈points,RationalHeight q R) :
    (run model.rat W lo hi points).2≤profile points.length W (model.rat (1+2*R)) :=
  height_work model.rat model.monotone W R lo hi points hl hh hp

theorem arithmetic_work (R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ q∈points,RationalHeight q R) :
    (run (fun _ => 1) 1 lo hi points).2≤profile points.length 1 1 :=
  height_work (fun _ => 1) (fun _ _ _ => le_rfl) 1 R lo hi points hl hh hp

end Blotto.GeneralPaperPricedCrossingSort

import Blotto.GeneralPaperRankArrayOperands

/-! Complete cached-rank generation prices. Queries, retained-data reads,
rank writes, both annotation additions, loop control and cached-depth
construction are charged. Neither model executes a work-sum traversal.
-/
namespace Blotto.GeneralPaperRankArrayPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperRankArrayExecution
open GeneralPaperRankArrayOperands (width)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def queryProfile (primitive : ℕ → ℕ) (W m depth V : ℕ) : ℕ :=
  2048*(depth+1)*(W+primitive (width m depth V))+4*primitive (width m depth V)+32*W

def profile (primitive : ℕ → ℕ) (W m k V : ℕ) : ℕ :=
  m*queryProfile primitive W m (35+k) V+44*(m+1)*arrayWord W m+
    2*primitive (width m (35+k) V)+160*W

def arithmeticProfile (m k : ℕ) : ℕ := m*(512*((35+k)+1)^2+135)+44*(m+1)+162

theorem lookup_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k depth V : ℕ)
    (values : Summary k) (cut : ℕ) (hDepth : depth=35+k) (hCut : cut≤V) (hValues : ∀ i,values.read i≤V) :
    (GeneralPaperSelectedRankPrice.run true primitive W k depth values cut).2≤
      2048*(depth+1)*(W+primitive (width m depth V)) := by
  have h := GeneralPaperSelectedRankPrice.bit_work primitive hMono W k depth V values cut hDepth hCut hValues
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono (by unfold width; omega)) W))

theorem fill_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k depth V : ℕ)
    (values : Summary k) (cuts : FixedArrayTable m ℕ) (hDepth : depth=35+k)
    (hCuts : ∀ q,cuts.read q≤V) (hValues : ∀ i,values.read i≤V) (count : ℕ) (hCount : count≤m) :
    (fill true (fun w => w) primitive W k depth values cuts count hCount).2≤
      count*queryProfile primitive W m depth V+
        PaperIndexedArrayConstruction.overhead (fun w => w) (arrayWord W m) m count+64*W := by
  induction count with
  | zero => simp only [fill,PaperIndexedArrayConstruction.overhead,slot,ite_true,Nat.zero_mul,Nat.zero_add]; exact Nat.le_refl _
  | succ count ih =>
    have hEarlier := ih (by omega)
    have hLookup := lookup_work primitive hMono W m k depth V values (cuts.read ⟨count,by omega⟩) hDepth
      (hCuts _) hValues
    have hAdds := GeneralPaperRankArrayOperands.additions_work true (fun w => w) primitive hMono W k depth V values cuts hDepth count hCount
    dsimp only at hAdds
    rw [fill,PaperIndexedArrayConstruction.overhead]
    dsimp only
    unfold slot
    simp only [ite_true]
    unfold queryProfile
    unfold queryProfile at hEarlier
    nlinarith only [hEarlier,hLookup,hAdds]

theorem bit_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k V : ℕ)
    (values : Summary k) (cuts : FixedArrayTable m ℕ) (hCuts : ∀ q,cuts.read q≤V) (hValues : ∀ i,values.read i≤V) :
    (prepare true (fun w => w) primitive W k values cuts).2≤profile primitive W m k V := by
  have hFill := fill_work primitive hMono W k (35+k) V values cuts rfl hCuts hValues m (Nat.le_refl _)
  have hOver := GeneralPaperControlArrayPrice.overhead (fun w => w) (arrayWord W m) m m
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (Nat.le_refl _)
    (GeneralPaperSummaryArrayControls.array_index W m)
  have hDepth := GeneralPaperRankArrayOperands.depth_work primitive hMono m k V
  unfold prepare run profile
  dsimp only
  omega

theorem fill_arithmetic_work {m : ℕ} (k depth : ℕ) (values : Summary k) (cuts : FixedArrayTable m ℕ)
    (count : ℕ) (hCount : count≤m) :
    (fill false (fun _ => 1) (fun _ => 1) 1 k depth values cuts count hCount).2≤
      count*(512*(depth+1)^2+135)+PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 m count+64 := by
  induction count with
  | zero => simp only [fill,PaperIndexedArrayConstruction.overhead,slot,Bool.false_eq_true,ite_false,Nat.zero_mul,Nat.zero_add,Nat.mul_one]; exact Nat.le_refl _
  | succ count ih =>
    have hEarlier := ih (by omega)
    have hLookup := GeneralPaperSelectedRankPrice.arithmetic_work k depth values (cuts.read ⟨count,by omega⟩)
    rw [fill,PaperIndexedArrayConstruction.overhead]
    dsimp only
    simp only [slot,Bool.false_eq_true,ite_false,GeneralPaperNaturalPrimitivePrice.binary,Nat.mul_one]
    nlinarith only [hEarlier,hLookup]

theorem arithmetic_work {m : ℕ} (k : ℕ) (values : Summary k) (cuts : FixedArrayTable m ℕ) :
    (prepare false (fun _ => 1) (fun _ => 1) 1 k values cuts).2≤arithmeticProfile m k := by
  have hFill := fill_arithmetic_work k (35+k) values cuts m (Nat.le_refl _)
  have hOver := GeneralPaperControlArrayPrice.overhead (fun _ => 1) 1 m m (Nat.le_refl _) (Nat.le_refl _)
    (fun _ _ => Nat.le_refl _)
  unfold prepare run arithmeticProfile GeneralPaperNaturalPrimitivePrice.binary
  dsimp only
  omega

theorem same_data {m : ℕ} (primitive : ℕ → ℕ) (W k : ℕ) (values : Summary k) (cuts : FixedArrayTable m ℕ) :
    (prepare true (fun w => w) primitive W k values cuts).1=
      (prepare false (fun _ => 1) (fun _ => 1) 1 k values cuts).1 := by
  rw [GeneralPaperRankArrayData.prepare_data,GeneralPaperRankArrayData.prepare_data]

end Blotto.GeneralPaperRankArrayPrice

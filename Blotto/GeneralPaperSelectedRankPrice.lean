import Blotto.GeneralPaperRankLookupPrice

/-! Reuse the summary array under its retained descriptor size. Reindexing
and the bounded-position transport are erased proofs, not array copies or
source-parameter executions. Native lookup rank/work/probes all agree.
-/
namespace Blotto.GeneralPaperSelectedRankPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def asSelected {n : ℕ} (k : ℕ) (hCount : n=(GeneralPaperSourceParameters.prepare k).summarySize)
    (found : GeneralPaperRankLookupPrice.Lookup n) : GeneralPaperSelectedRank.Lookup k :=
  ⟨⟨found.position.val,lt_of_lt_of_eq found.position.isLt (congrArg Nat.succ hCount)⟩,found.work,found.probes⟩

def run (bits : Bool) (primitive : ℕ → ℕ) (W k depth : ℕ)
    (values : GeneralPaperUnsignedCellConstancy.Summary k) (cut : ℕ) : GeneralPaperSelectedRank.Lookup k × ℕ :=
  let retained : FixedArrayTable values.data.size ℕ := ⟨values.data,rfl⟩
  let found := GeneralPaperRankLookupPrice.run bits primitive W depth retained cut
  (asSelected k values.size found.1,found.2+32*W)

theorem array_heq {n m : ℕ} (a : FixedArrayTable n ℕ) (b : FixedArrayTable m ℕ) (hData : a.data=b.data) : HEq a b := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      dsimp only at hData
      subst b
      have hn : n=m := ha.symm.trans hb
      cases hn
      rfl

theorem specification_data {n : ℕ} (k depth : ℕ) (values : FixedArrayTable n ℕ)
    (source : GeneralPaperUnsignedCellConstancy.Summary k) (cut : ℕ)
    (hCount : n=(GeneralPaperSourceParameters.prepare k).summarySize) (hValues : HEq values source) (hDepth : depth=35+k) :
    asSelected k hCount (GeneralPaperRankLookupPrice.specification depth values cut)=GeneralPaperSelectedRank.lookup k source cut := by
  subst n
  have hv := eq_of_heq hValues
  subst values
  subst depth
  rfl

theorem data (bits : Bool) (primitive : ℕ → ℕ) (W k depth : ℕ)
    (values : GeneralPaperUnsignedCellConstancy.Summary k) (cut : ℕ) (hDepth : depth=35+k) :
    (run bits primitive W k depth values cut).1=GeneralPaperSelectedRank.lookup k values cut := by
  let retained : FixedArrayTable values.data.size ℕ := ⟨values.data,rfl⟩
  have hs : values.data.size<2^depth := by rw [values.size,hDepth]; exact GeneralPaperSelectedRank.selected_size k
  have hv : HEq retained values := array_heq retained values rfl
  unfold run
  dsimp only
  rw [GeneralPaperRankLookupPrice.data bits primitive W depth retained cut hs]
  exact specification_data k depth retained values cut values.size hv hDepth

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k depth V : ℕ)
    (values : GeneralPaperUnsignedCellConstancy.Summary k) (cut : ℕ)
    (hDepth : depth=35+k) (hCut : cut≤V) (hValues : ∀ i,values.read i≤V) :
    (run true primitive W k depth values cut).2≤2048*(depth+1)*(W+primitive (GeneralPaperRankOperands.width depth V)) := by
  let retained : FixedArrayTable values.data.size ℕ := ⟨values.data,rfl⟩
  have hs : values.data.size<2^depth := by rw [values.size,hDepth]; exact GeneralPaperSelectedRank.selected_size k
  have hv : ∀ i,retained.read i≤V := by
    intro i
    have hi : i.val<(GeneralPaperSourceParameters.prepare k).summarySize := lt_of_lt_of_eq i.isLt values.size
    exact hValues ⟨i.val,hi⟩
  have h := GeneralPaperRankLookupPrice.bit_work primitive hMono W depth V retained cut hs hCut hv
  change (GeneralPaperRankLookupPrice.run true primitive W depth retained cut).2+32*W≤_
  nlinarith only [h,Nat.zero_le depth]

theorem arithmetic_work (k depth : ℕ) (values : GeneralPaperUnsignedCellConstancy.Summary k) (cut : ℕ) :
    (run false (fun _ => 1) 1 k depth values cut).2≤512*(depth+1)^2+99 := by
  have h := GeneralPaperRankLookupPrice.arithmetic_work depth (⟨values.data,rfl⟩ : FixedArrayTable values.data.size ℕ) cut
  change (GeneralPaperRankLookupPrice.run false (fun _ => 1) 1 depth (⟨values.data,rfl⟩ : FixedArrayTable values.data.size ℕ) cut).2+32≤_
  omega

end Blotto.GeneralPaperSelectedRankPrice

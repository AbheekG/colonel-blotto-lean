import Blotto.GeneralPaperRankProperties

/-! The actual selected summary size supplies both quotient depth and
binary-search fuel. A lookup returns a bounded rank with all duplicates
included; its source work is quadratic only in the accuracy exponent.
-/
namespace Blotto.GeneralPaperSelectedRank
open GeneralPaperRankSearch
set_option autoImplicit false
set_option maxHeartbeats 3000000

def selected (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ) (cut : ℕ) : Result :=
  run values cut (35+k) (35+k) 0 (GeneralPaperSourceParameters.prepare k).summarySize

theorem selected_size (k : ℕ) : (GeneralPaperSourceParameters.prepare k).summarySize<2^(35+k) := by
  rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
  convert GeneralPaperBoundedQuotient.dyadic_cap (34+k) using 1 <;> congr 1 <;> omega

theorem selected_valid (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone values.read) (cut : ℕ) : ValidRank values cut (selected k values cut).rank := by
  apply run_spec values cut (35+k) (35+k) 0 _ hMono (Nat.zero_le _) (le_refl _) (selected_size k)
    (by simpa only [Nat.sub_zero] using selected_size k)
  · intro i hi
    omega
  · intro i hi
    have := i.isLt
    omega

structure Lookup (k : ℕ) where
  position : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)
  work : ℕ
  probes : ℕ

def lookup (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ) (cut : ℕ) : Lookup k :=
  let result := selected k values cut
  ⟨⟨min result.rank (GeneralPaperSourceParameters.prepare k).summarySize,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,result.work+8,result.probes⟩

theorem lookup_valid (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone values.read) (cut : ℕ) : ValidRank values cut (lookup k values cut).position.val := by
  have he := selected_valid k values hMono cut
  simpa only [lookup,Nat.min_eq_left he.1] using he

theorem lookup_spec (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone values.read) (cut : ℕ) (i : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    values.read i<cut ↔ i.val<(lookup k values cut).position.val := (lookup_valid k values hMono cut).2 i

theorem lookup_monotone (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone values.read) : Monotone (fun cut => (lookup k values cut).position) := by
  intro small large hCuts
  exact GeneralPaperRankProperties.cut_order values small large _ _ hCuts
    (lookup_valid k values hMono small) (lookup_valid k values hMono large)

theorem lookup_zero (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone values.read) : (lookup k values 0).position.val=0 :=
  GeneralPaperRankProperties.unique values 0 _ 0 (lookup_valid k values hMono 0) (GeneralPaperRankProperties.valid_zero values)

theorem lookup_full (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone values.read) (cut : ℕ) (hAll : ∀ i, values.read i<cut) :
    (lookup k values cut).position.val=(GeneralPaperSourceParameters.prepare k).summarySize :=
  GeneralPaperRankProperties.unique values cut _ _ (lookup_valid k values hMono cut) (GeneralPaperRankProperties.valid_full values cut hAll)

theorem lookup_work (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ) (cut : ℕ) :
    (lookup k values cut).work≤(35+k)*(12*(35+k)+34)+16 := by
  have he := run_work values cut (35+k) (35+k) 0 (GeneralPaperSourceParameters.prepare k).summarySize
  change (run values cut (35+k) (35+k) 0 (GeneralPaperSourceParameters.prepare k).summarySize).work+8≤_
  omega

theorem lookup_probes (k : ℕ) (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ) (cut : ℕ) :
    (lookup k values cut).probes≤35+k := run_probes _ _ _ _ _ _

end Blotto.GeneralPaperSelectedRank

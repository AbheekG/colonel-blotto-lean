import Blotto.GeneralPaperEpochPrefixArray

/-! A cached rank gives two native prefix reads and the retained bounded
mesh quotient. Rank/location correspondence is an explicit epoch-index
interface, including all occurrences at repeated locations.
-/
namespace Blotto.GeneralPaperEpochPrefixQuery
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def sumPrefix {n : ℕ} (values : FixedArrayTable n ℕ) (count : ℕ) : ℕ :=
  ∑ r, if r.val<count then values.read r else 0

theorem sumPrefix_zero {n : ℕ} (values : FixedArrayTable n ℕ) : sumPrefix values 0=0 := by simp [sumPrefix]

theorem sumPrefix_succ {n : ℕ} (values : FixedArrayTable n ℕ) (count : ℕ) (hc : count<n) :
    sumPrefix values (count+1)=sumPrefix values count+values.read ⟨count,hc⟩ := by
  have he (r : Fin n) : (if r.val<count+1 then values.read r else 0)=
      (if r.val<count then values.read r else 0)+(if r=⟨count,hc⟩ then values.read r else 0) := by
    by_cases hSmall : r.val<count
    · have hn : r≠⟨count,hc⟩ := by
        intro h
        have hv := congrArg Fin.val h
        change r.val=count at hv
        omega
      simp only [hSmall,show r.val<count+1 by omega,hn,ite_true,ite_false,Nat.add_zero]
    · by_cases hEq : r=⟨count,hc⟩
      · subst r; simp
      · have hn : ¬r.val<count+1 := by
          intro h
          apply hEq
          apply Fin.ext
          change r.val=count
          omega
        simp only [hSmall,hEq,hn,ite_false,Nat.zero_add]
  unfold sumPrefix
  simp only [he,Finset.sum_add_distrib]
  simp

theorem read_prefix {n : ℕ} (values : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) :
    (GeneralPaperEpochPrefixArray.build values).read ⟨count,by omega⟩=sumPrefix values count := by
  induction count with
  | zero => rw [GeneralPaperEpochPrefixArray.read_build,sumPrefix_zero]; rfl
  | succ count ih =>
    have hLt : count<n := by omega
    change (GeneralPaperEpochPrefixArray.build values).read (⟨count,hLt⟩:Fin n).succ= _
    rw [GeneralPaperEpochPrefixArray.read_succ]
    change (GeneralPaperEpochPrefixArray.build values).read ⟨count,by omega⟩+values.read ⟨count,hLt⟩= _
    rw [ih (by omega),sumPrefix_succ values count hLt]

theorem read_total {n : ℕ} (values : FixedArrayTable n ℕ) :
    (GeneralPaperEpochPrefixArray.build values).read (Fin.last n)=∑ r, values.read r := by
  change (GeneralPaperEpochPrefixArray.build values).read ⟨n,by omega⟩= _
  rw [read_prefix values n (le_refl _)]
  simp only [sumPrefix,Fin.isLt,ite_true]

theorem read_location_count {n : ℕ} (values : FixedArrayTable n ℕ) (location : Fin n → ℕ)
    (rank : Fin (n+1)) (cut : ℕ) (hRank : ∀ r, location r<cut ↔ r.val<rank.val) :
    (GeneralPaperEpochPrefixArray.build values).read rank=∑ r, if location r<cut then values.read r else 0 := by
  rw [read_prefix values rank.val (by have := rank.isLt; omega)]
  apply Finset.sum_congr rfl
  intro r _
  simp only [hRank r]

theorem read_le_total {n : ℕ} (values : FixedArrayTable n ℕ) (rank : Fin (n+1)) :
    (GeneralPaperEpochPrefixArray.build values).read rank≤(GeneralPaperEpochPrefixArray.build values).read (Fin.last n) := by
  rw [read_prefix values rank.val (by have := rank.isLt; omega),read_total]
  apply Finset.sum_le_sum
  intro r _
  split_ifs <;> omega

def query {n : ℕ} (k : ℕ) (preparedPrefix : FixedArrayTable (n+1) ℕ) (rank : Fin (n+1)) : GeneralPaperBoundedQuotient.Result :=
  let result := GeneralPaperCDFMesh.selected k (preparedPrefix.read rank) (preparedPrefix.read (Fin.last n))
  ⟨result.quotient,result.remainder,result.work+16⟩

theorem query_bounds {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℕ) (rank : Fin (n+1))
    (hTotal : 0<∑ r, values.read r) :
    (query k (GeneralPaperEpochPrefixArray.build values) rank).quotient≤(GeneralPaperSourceParameters.prepare k).meshDenominator ∧
    |((GeneralPaperEpochPrefixArray.build values).read rank:ℚ)/(∑ r, values.read r)-
      GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (query k (GeneralPaperEpochPrefixArray.build values) rank).quotient|≤(GeneralPaperSourceParameters.prepare k).theta := by
  have he := GeneralPaperCDFMesh.selected_bounds k _ _
    (by rw [read_total]; exact hTotal) (read_le_total values rank)
  exact ⟨he.1,by simpa only [query,read_total] using he.2⟩

theorem query_work {n : ℕ} (k : ℕ) (preparedPrefix : FixedArrayTable (n+1) ℕ) (rank : Fin (n+1)) :
    (query k preparedPrefix rank).work=12*(30+k)+34 := by
  unfold query
  dsimp only
  rw [GeneralPaperCDFMesh.selected_work]

end Blotto.GeneralPaperEpochPrefixQuery

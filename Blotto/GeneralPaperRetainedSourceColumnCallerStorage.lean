import Blotto.GeneralPaperSourceRowsCallerReachedRates

/-! Erased physical parent observer for the retained source-column caller.
The actual child rows, normalized columns, returned columns and eleven
native dimension/work/check fields coexist. Child lifetimes are retained
by the preceding additive source-row and unit-source contracts. -/
namespace Blotto.GeneralPaperRetainedSourceColumnCallerStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 1800000

def price (W P Q : ℕ) : ℕ := P+Q+64*W
def metadataCap (W m k Qv T K P Q : ℕ) : ℕ := m+k+Qv+T+K+price W P Q+64*W+1
def window {T m K : ℕ} (W k Qv : ℕ)
    (rows : (FixedArrayTable T (FixedArrayTable m ℚ)×Bool)×ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×ℕ)
    (result : (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×Bool)×ℕ) : ℕ :=
  rowsFoot W rows.1.1+columnsFoot W columns.1+columnsFoot W result.1.1+
    fields W [m,k,Qv,T,K,rows.2,columns.2,result.2,rows.2+columns.2,64*W,
      GeneralPaperFinalStaticLoopStorage.bit rows.1.2]+128*W
def profile (W m k Qv T K R P Q : ℕ) : ℕ :=
  rowsProfile W T m R+2*columnsProfile W T m K R+
    11*(natBits (metadataCap W m k Qv T K P Q)+W)+160*W

theorem bounded {T m K : ℕ} (W k Qv R P Q : ℕ)
    (rows : (FixedArrayTable T (FixedArrayTable m ℚ)×Bool)×ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×ℕ)
    (result : (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×Bool)×ℕ)
    (hRows : ∀ i j,rationalWordWidth ((rows.1.1.read i).read j)≤R)
    (hColumns : columnsFoot W columns.1≤columnsProfile W T m K R)
    (hData : result.1.1=columns.1) (hP : rows.2≤P) (hQ : columns.2≤Q)
    (hShape : result.2=rows.2+columns.2+64*W) :
    window W k Qv rows columns result≤profile W m k Qv T K R P Q := by
  have hr := rows_bound W R rows.1.1 hRows
  have hReturned : columnsFoot W result.1.1≤columnsProfile W T m K R := by rw [hData];exact hColumns
  have hBit := GeneralPaperFinalStaticLoopStorage.bit_bound rows.1.2
  have hf := fields_bound W (natBits (metadataCap W m k Qv T K P Q))
    [m,k,Qv,T,K,rows.2,columns.2,result.2,rows.2+columns.2,64*W,
      GeneralPaperFinalStaticLoopStorage.bit rows.1.2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price;omega)
  change fields W _≤11*(natBits (metadataCap W m k Qv T K P Q)+W)+32*W at hf
  unfold window profile
  omega

end Blotto.GeneralPaperRetainedSourceColumnCallerStorage

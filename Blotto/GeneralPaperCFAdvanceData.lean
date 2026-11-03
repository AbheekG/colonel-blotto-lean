import Blotto.GeneralPaperCFDeterminant

/-! Exact continuant and selected-value projections of the executed loop.
Accepting replaces the selected fraction by the new continuant; stopping
preserves the last accepted fraction even though a rejected next continuant
has already been computed and charged.
-/
namespace Blotto.GeneralPaperCFAdvanceData
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem continuants (D divisionFuel : ℕ) (s : State) (hd : 0<s.denominator) :
    (advance D divisionFuel s).1.olderNum=s.previousNum ∧
      (advance D divisionFuel s).1.olderDen=s.previousDen ∧
      (advance D divisionFuel s).1.previousNum=
        (GeneralPaperConstructedNatDivision.run s.numerator s.denominator divisionFuel).quotient*s.previousNum+s.olderNum ∧
      (advance D divisionFuel s).1.previousDen=
        (GeneralPaperConstructedNatDivision.run s.numerator s.denominator divisionFuel).quotient*s.previousDen+s.olderDen := by
  simp only [advance,ite_eq_right hd.ne']
  split
  · split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩

theorem continuing_selection (D divisionFuel : ℕ) (s : State) (hMore : (advance D divisionFuel s).2=true) :
    ∃ f, (advance D divisionFuel s).1.selected=some f ∧
      f.num=(advance D divisionFuel s).1.previousNum ∧ f.den=(advance D divisionFuel s).1.previousDen := by
  dsimp only [advance] at hMore ⊢
  split at hMore
  · cases hMore
  · rename_i hz
    simp only [ite_eq_right hz]
    split at hMore
    · rename_i hp
      simp only [dite_eq_ite,hp,ite_true]
      split at hMore
      · rename_i hBound
        simp only [ite_eq_left hBound]
        exact ⟨_,rfl,rfl,rfl⟩
      · cases hMore
    · cases hMore

theorem stopped_selection (D divisionFuel : ℕ) (s : State) (hStop : (advance D divisionFuel s).2=false) :
    (advance D divisionFuel s).1.selected=s.selected := by
  dsimp only [advance] at hStop ⊢
  split at hStop
  · rename_i hz
    simp [hz]
  · rename_i hz
    split at hStop
    · rename_i hp
      split at hStop
      · cases hStop
      · rename_i hBound
        simp [hz,hp,hBound]
    · rename_i hp
      simp [hz,hp]

theorem quotient_positive (D width : ℕ) (s : State) (hPair : PairBound width s) (hd : 0<s.denominator)
    (hOrder : s.denominator≤s.numerator) :
    1≤(GeneralPaperConstructedNatDivision.run s.numerator s.denominator (width+2)).quotient := by
  rw [GeneralPaperConstructedNatDivision.quotient_eq _ _ _ hd (quotient_cap width _ _ hPair.1 hd)]
  apply (Nat.le_div_iff_mul_le hd).mpr
  simpa only [Nat.one_mul] using hOrder

theorem previous_den_mono (D width : ℕ) (s : State) (hPair : PairBound width s) (hOrder : s.denominator≤s.numerator) :
    s.previousDen≤(advance D (width+2) s).1.previousDen := by
  by_cases hz : s.denominator=0
  · simp only [advance,ite_eq_left hz,le_refl]
  · have hd : 0<s.denominator := by omega
    have hq := quotient_positive D width s hPair hd hOrder
    have he := Nat.mul_le_mul_right s.previousDen hq
    rw [(continuants D (width+2) s hd).2.2.2]
    nlinarith only [he]

theorem euclidean_order (D width : ℕ) (s : State) (hPair : PairBound width s) (hOrder : s.denominator≤s.numerator) :
    (advance D (width+2) s).1.denominator≤(advance D (width+2) s).1.numerator := by
  by_cases hz : s.denominator=0
  · simpa only [advance,ite_eq_left hz] using hOrder
  · have hd : 0<s.denominator := by omega
    have he := advance_euclidean D (width+2) s hd (quotient_cap width _ _ hPair.1 hd)
    rw [he.1,he.2]
    exact (Nat.mod_lt _ hd).le

end Blotto.GeneralPaperCFAdvanceData

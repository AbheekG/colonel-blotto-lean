import Blotto.GeneralPaperCodePayoff

/-! Every member of the paper's closed grid/Farey set has a literal code
produced by the actual decoder. The floor below is a proof-only bucket
witness; executed lookup still uses arithmetic-built midpoint quotients.
-/
namespace Blotto.GeneralPaperCodeCoverage
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperBucketGeometry
set_option autoImplicit false
set_option maxHeartbeats 2500000

def InBids (a : Alphabet) (value : ℚ) : Prop :=
  (∃ f : Farey.Fraction, f.den≤a.D ∧ 0≤f.value ∧ f.value≤1 ∧ value=f.value) ∨
  (∃ t, t≤a.C ∧ value=(grid a t).value)

theorem farey_meaning (a : Alphabet) (f : Farey.Fraction) (hDen : f.den≤a.D)
    (hZero : 0≤f.value) (hOne : f.value≤1) : ∃ code, Denotes a false code f.value false := by
  let t := Nat.floor ((a.C:ℚ)*f.value)
  have hc : (0:ℚ)<a.C := by exact_mod_cast a.scalePositive
  have hNonneg : 0≤(a.C:ℚ)*f.value := mul_nonneg hc.le hZero
  have hFloor : (t:ℚ)≤(a.C:ℚ)*f.value := Nat.floor_le hNonneg
  have hUpper : (a.C:ℚ)*f.value<(t:ℚ)+1 := Nat.lt_floor_add_one _
  have hLow : lower a.C t≤f.value := by
    apply (div_le_iff₀ hc).mpr
    simpa only [mul_comm] using hFloor
  have hHigh : f.value<upper a.C t := by
    apply (lt_div_iff₀ hc).mpr
    simpa only [mul_comm] using hUpper
  have hT : t≤a.C := by
    have he := Nat.floor_mono (mul_le_mul_of_nonneg_left hOne hc.le)
    simpa only [mul_one,Nat.floor_natCast] using he
  by_cases hGrid : f.value=lower a.C t
  · exact ⟨4*t,Or.inl ⟨t,hT,rfl,hGrid,rfl⟩⟩
  · have hStrict : lower a.C t<f.value := by
      rcases lt_or_eq_of_le hLow with hLt|hEq
      · exact hLt
      · exact (hGrid hEq.symm).elim
    have hTStrict : t<a.C := by
      have he := (div_lt_iff₀ hc).mp (hStrict.trans_le hOne)
      have hf : (t:ℚ)<a.C := by simpa only [one_mul] using he
      exact_mod_cast hf
    exact ⟨4*t+2,Or.inr (Or.inr (Or.inl ⟨t,f,hTStrict,hDen,⟨hStrict,hHigh⟩,rfl,rfl,rfl⟩))⟩

theorem closed_meaning (a : Alphabet) (value : ℚ) (h : InBids a value) :
    ∃ code, Denotes a false code value false := by
  rcases h with ⟨f,hDen,hZero,hOne,hValue⟩|⟨t,hT,hValue⟩
  · rw [hValue]
    exact farey_meaning a f hDen hZero hOne
  · exact ⟨4*t,Or.inl ⟨t,hT,rfl,hValue,rfl⟩⟩

theorem closed_decode (a : Alphabet) (value : ℚ) (h : InBids a value) :
    ∃ code choice, (decode a false code).choice=some choice ∧ choice.threshold.value=value ∧ choice.opened=false := by
  obtain ⟨code,hMeaning⟩ := closed_meaning a value h
  obtain ⟨choice,hSome,hValue,hOpen⟩ := GeneralPaperCodeDecodeComplete.denotes_complete a false code value false hMeaning
  exact ⟨code,choice,hSome,hValue,hOpen⟩

theorem closed_to_open (a : Alphabet) (code : ℕ) (value : ℚ)
    (h : Denotes a false code value false) (hLess : value<1) : Denotes a true (code+1) value true := by
  rcases h with ⟨t,hT,hCode,hValue,_⟩|⟨hFalse,_⟩|⟨t,f,hT,hDen,hInside,hCode,hValue,_⟩|⟨hFalse,_⟩
  · have hc : (0:ℚ)<a.C := by exact_mod_cast a.scalePositive
    have ht : t<a.C := by
      rw [hValue,grid_value] at hLess
      have he : (t:ℚ)<a.C := by simpa only [one_mul] using (div_lt_iff₀ hc).mp hLess
      exact_mod_cast he
    exact Or.inr (Or.inl ⟨rfl,t,ht,by omega,hValue,rfl⟩)
  · cases hFalse
  · exact Or.inr (Or.inr (Or.inr ⟨rfl,t,f,hT,hDen,hInside,by omega,hValue,rfl⟩))
  · cases hFalse

theorem open_decode (a : Alphabet) (value : ℚ) (h : InBids a value) (hLess : value<1) :
    ∃ code choice, (decode a true code).choice=some choice ∧ choice.threshold.value=value ∧ choice.opened=true := by
  obtain ⟨code,hMeaning⟩ := closed_meaning a value h
  obtain ⟨choice,hSome,hValue,hOpen⟩ := GeneralPaperCodeDecodeComplete.denotes_complete a true (code+1) value true
    (closed_to_open a code value hMeaning hLess)
  exact ⟨code+1,choice,hSome,hValue,hOpen⟩

theorem interior_in_bids (a : Alphabet) (t : ℕ) (f : Farey.Fraction)
    (hT : t<a.C) (hDen : f.den≤a.D) (hInside : Interior a.C t f.value) : InBids a f.value := by
  have hc : (0:ℚ)<a.C := by exact_mod_cast a.scalePositive
  have hLower : 0≤lower a.C t := by unfold lower; positivity
  have hUpper : upper a.C t≤1 := by
    apply (div_le_iff₀ hc).mpr
    have he : (t:ℚ)+1≤a.C := by exact_mod_cast hT
    simpa only [one_mul] using he
  exact Or.inl ⟨f,hDen,hLower.trans hInside.1.le,hInside.2.le.trans hUpper,rfl⟩

theorem decoded_in_bids (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (decode a response code).choice=some choice) : InBids a choice.threshold.value := by
  have hMeaning := (GeneralPaperCodeDecodeSound.decode_sound a response code choice hSome).1
  rcases hMeaning with ⟨t,hT,_,hValue,_⟩|⟨_,t,hT,_,hValue,_⟩|
    ⟨t,f,hT,hDen,hInside,_,hValue,_⟩|⟨_,t,f,hT,hDen,hInside,_,hValue,_⟩
  · exact Or.inr ⟨t,hT,hValue⟩
  · exact Or.inr ⟨t,hT.le,hValue⟩
  · rw [hValue]
    exact interior_in_bids a t f hT hDen hInside
  · rw [hValue]
    exact interior_in_bids a t f hT hDen hInside

theorem in_bids_iff_closed (a : Alphabet) (value : ℚ) : InBids a value ↔
    ∃ code choice, (decode a false code).choice=some choice ∧ choice.threshold.value=value ∧ choice.opened=false := by
  constructor
  · exact closed_decode a value
  · rintro ⟨code,choice,hSome,hValue,_⟩
    rw [←hValue]
    exact decoded_in_bids a false code choice hSome

theorem opened_below_one (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (decode a response code).choice=some choice) (hOpen : choice.opened=true) : choice.threshold.value<1 := by
  have hCap := valid_code_bound a response code (GeneralPaperCodeDecodeSound.decode_valid a response code choice hSome)
  have he := GeneralPaperCodeOrder.decode_monotone a response response code (4*a.C) choice ⟨grid a a.C,false⟩ hSome
    (GeneralPaperCodeDecodeSound.decode_one a response) hCap
  rcases (GeneralPaperResponseTag.le_iff _ _).mp he with hLt|⟨_,hFlag⟩
  · change choice.threshold.value<(grid a a.C).value at hLt
    rw [grid_one] at hLt
    exact hLt
  · change choice.opened=false ∨ false=true at hFlag
    simp only [hOpen,Bool.true_eq_false,Bool.false_eq_true,or_self] at hFlag

theorem in_bids_open_iff (a : Alphabet) (value : ℚ) : (InBids a value ∧ value<1) ↔
    ∃ code choice, (decode a true code).choice=some choice ∧ choice.threshold.value=value ∧ choice.opened=true := by
  constructor
  · rintro ⟨hBids,hLess⟩
    exact open_decode a value hBids hLess
  · rintro ⟨code,choice,hSome,hValue,hOpen⟩
    rw [←hValue]
    exact ⟨decoded_in_bids a true code choice hSome,opened_below_one a true code choice hSome hOpen⟩

end Blotto.GeneralPaperCodeCoverage

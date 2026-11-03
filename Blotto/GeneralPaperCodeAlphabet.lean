import Blotto.GeneralPaperMidpointRealWork

/-! Prepared integer controls and literal decoded choices for the paper's
union of grid and Farey bids. Control identities are proof metadata; their
selected outer construction and complete prices remain separate joins.
-/
namespace Blotto.GeneralPaperCodeAlphabet
set_option autoImplicit false

structure Alphabet where
  D : ℕ
  C : ℕ
  lambda : ℕ
  orderPositive : 0<D
  scalePositive : 0<C
  separated : D*D≤C
  dyadic : 8*C=2^lambda

structure Choice where
  threshold : Farey.Fraction
  opened : Bool

def grid (a : Alphabet) (t : ℕ) : Farey.Fraction := ⟨t,a.C,a.scalePositive⟩

def Choice.tag (choice : Choice) : GeneralPaperResponseTag.Tag := ⟨choice.threshold.value,choice.opened⟩

def Choice.physical (choice : Choice) (delta : ℚ) : ℚ := choice.threshold.value+if choice.opened then delta else 0

def Denotes (a : Alphabet) (response : Bool) (code : ℕ) (value : ℚ) (opened : Bool) : Prop :=
  (∃ t, t≤a.C ∧ code=4*t ∧ value=(grid a t).value ∧ opened=false) ∨
  (response=true ∧ ∃ t, t<a.C ∧ code=4*t+1 ∧ value=(grid a t).value ∧ opened=true) ∨
  (∃ (t : ℕ) (f : Farey.Fraction), t<a.C ∧ f.den≤a.D ∧ GeneralPaperBucketGeometry.Interior a.C t f.value ∧
    code=4*t+2 ∧ value=f.value ∧ opened=false) ∨
  (response=true ∧ ∃ (t : ℕ) (f : Farey.Fraction), t<a.C ∧ f.den≤a.D ∧ GeneralPaperBucketGeometry.Interior a.C t f.value ∧
    code=4*t+3 ∧ value=f.value ∧ opened=true)

def Valid (a : Alphabet) (response : Bool) (code : ℕ) : Prop := ∃ value opened, Denotes a response code value opened

theorem grid_value (a : Alphabet) (t : ℕ) : (grid a t).value=(t:ℚ)/a.C := rfl

theorem grid_zero (a : Alphabet) : (grid a 0).value=0 := by simp only [grid_value,Nat.cast_zero,zero_div]

theorem grid_one (a : Alphabet) : (grid a a.C).value=1 := by rw [grid_value,div_self (by exact_mod_cast a.scalePositive.ne')]

theorem valid_grid (a : Alphabet) (response : Bool) (t : ℕ) (ht : t≤a.C) : Valid a response (4*t) :=
  ⟨(grid a t).value,false,Or.inl ⟨t,ht,rfl,rfl,rfl⟩⟩

theorem valid_code_bound (a : Alphabet) (response : Bool) (code : ℕ) (h : Valid a response code) : code≤4*a.C := by
  obtain ⟨value,opened,h⟩ := h
  rcases h with ⟨t,ht,rfl,_,_⟩|⟨_,t,ht,rfl,_,_⟩|⟨t,f,ht,_,_,rfl,_,_⟩|⟨_,t,f,ht,_,_,rfl,_,_⟩ <;> omega

theorem valid_in_alphabet (a : Alphabet) (response : Bool) (code : ℕ) (h : Valid a response code) : code<8*a.C := by
  have he := valid_code_bound a response code h
  have hp := a.scalePositive
  omega

end Blotto.GeneralPaperCodeAlphabet

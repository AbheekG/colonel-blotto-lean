import Blotto.GeneralPaperSourcePrecallPreparation

/-! Fast integer division for the bit implementation of constructed
mantissas. The arithmetic-only bounded quotient remains the real-RAM
implementation. Under its constructed cap, every returned field agrees,
including the legacy work annotation. No original input is decoded here.
-/
namespace Blotto.GeneralPaperFastConstructedDivision
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (n d depth : ℕ) : GeneralPaperBoundedQuotient.Result :=
  ⟨n/d,((n%d:ℕ):ℚ),12*depth+2⟩

theorem quotient_data (n d depth : ℕ) (hd : 0<d) (hCap : n<d*2^depth) :
    (GeneralPaperBoundedQuotient.run n d depth).quotient=n/d := by
  have hs := GeneralPaperBoundedQuotient.run_spec n d (by exact_mod_cast hd) depth
    (by positivity) (by exact_mod_cast hCap)
  let q := (GeneralPaperBoundedQuotient.run n d depth).quotient
  have hlo : d*q≤n := by
    have hh : (d:ℚ)*(q:ℚ)≤n := by dsimp only [q]; linarith only [hs.1,hs.2.1]
    exact_mod_cast hh
  have hhi : n<d*(q+1) := by
    have hh : (n:ℚ)<(d:ℚ)*((q:ℚ)+1) := by dsimp only [q]; nlinarith only [hs.1,hs.2.2]
    exact_mod_cast hh
  have hn := Nat.div_add_mod n d
  have hr := Nat.mod_lt n hd
  change q=n/d
  apply le_antisymm
  · by_contra h
    have hm := Nat.mul_le_mul_left d (show n/d+1≤q by omega)
    nlinarith only [hn,hr,hlo,hm]
  · by_contra h
    have hm := Nat.mul_le_mul_left d (show q+1≤n/d by omega)
    nlinarith only [hn,hhi,hm,Nat.zero_le (n%d)]

theorem data (n d depth : ℕ) (hd : 0<d) (hCap : n<d*2^depth) :
    run n d depth=GeneralPaperBoundedQuotient.run n d depth := by
  have hq := quotient_data n d depth hd hCap
  have hs := GeneralPaperBoundedQuotient.run_spec n d (by exact_mod_cast hd) depth
    (by positivity) (by exact_mod_cast hCap)
  have hn : (n:ℚ)=(d:ℚ)*((n/d:ℕ):ℚ)+((n%d:ℕ):ℚ) := by
    exact_mod_cast (Nat.div_add_mod n d).symm
  have hr : (GeneralPaperBoundedQuotient.run n d depth).remainder=((n%d:ℕ):ℚ) := by
    rw [hq] at hs
    linarith only [hs.1,hn]
  have hw := GeneralPaperBoundedQuotient.run_work (n:ℚ) (d:ℚ) depth
  cases he : GeneralPaperBoundedQuotient.run (n:ℚ) (d:ℚ) depth with
  | mk q r work =>
    rw [he] at hq hr hw
    dsimp only at hq hr hw
    subst q; subst r; subst work
    rfl

end Blotto.GeneralPaperFastConstructedDivision

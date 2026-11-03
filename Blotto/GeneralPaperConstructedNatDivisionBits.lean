import Blotto.GeneralPaperGrowingQuotientBits

/-! Exact native constructed natural division with an actual-depth bit
price. The returned natural remainder is formed by the native product and
subtraction, and both raw results are charged before any reduction.
-/
namespace Blotto.GeneralPaperConstructedNatDivisionBits
set_option autoImplicit false
set_option maxHeartbeats 6000000

def rawWork (primitive : ℕ → ℕ) (n d q : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) d q+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) n (d*q)

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (n d fuel : ℕ) (hd : 0<d) :
    rawWork primitive n d (GeneralPaperNaturalGrowingQuotient.run n d fuel).quotient≤
      4*primitive (GeneralPaperGrowingQuotientBits.width n d) := by
  let L := GeneralPaperGrowingQuotientBits.width n d
  let q := (GeneralPaperNaturalGrowingQuotient.run n d fuel).quotient
  have hb := GeneralPaperNaturalGrowingQuotient.operand_bounds n d fuel hd
  have hq : binaryWordWidth q≤binaryWordWidth n := binaryWordWidth_mono hb.1
  have hp : binaryWordWidth (d*q)≤binaryWordWidth n := binaryWordWidth_mono hb.2.2
  have hr := binaryWordWidth_mono (show n-d*q≤n by omega)
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) d q L
    (by dsimp [L,GeneralPaperGrowingQuotientBits.width]; omega)
    (by dsimp [L,GeneralPaperGrowingQuotientBits.width]; omega)
    (by dsimp [L,GeneralPaperGrowingQuotientBits.width]; omega)
  have hs := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a-b) n (d*q) L
    (by dsimp [L,GeneralPaperGrowingQuotientBits.width]; omega)
    (by dsimp [L,GeneralPaperGrowingQuotientBits.width]; omega)
    (by dsimp [L,GeneralPaperGrowingQuotientBits.width]; omega)
  change rawWork primitive n d q≤4*primitive L
  unfold rawWork
  omega

def run (primitive : ℕ → ℕ) (W n d fuel : ℕ) : GeneralPaperConstructedNatDivision.Result × ℕ :=
  let found := GeneralPaperGrowingQuotientBits.run primitive W n d fuel
  (⟨found.1.quotient,n-d*found.1.quotient,found.1.depth,found.1.work+12⟩,
    found.2+rawWork primitive n d found.1.quotient+64*W)

theorem data (primitive : ℕ → ℕ) (W n d fuel : ℕ) :
    (run primitive W n d fuel).1=GeneralPaperConstructedNatDivision.run n d fuel := by
  simp only [run,GeneralPaperGrowingQuotientBits.data,GeneralPaperConstructedNatDivision.run,
    ←GeneralPaperNaturalGrowingQuotient.data,GeneralPaperNaturalGrowingQuotient.lift]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W n d fuel : ℕ) (hd : 0<d) :
    (run primitive W n d fuel).2≤1024*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1)*
      (W+primitive (GeneralPaperGrowingQuotientBits.width n d)) := by
  let P := primitive (GeneralPaperGrowingQuotientBits.width n d)
  have hg := GeneralPaperGrowingQuotientBits.work primitive hMono W n d fuel hd
  have hr := raw_work primitive hMono n d fuel hd
  unfold run
  dsimp only
  rw [GeneralPaperGrowingQuotientBits.data]
  change (GeneralPaperGrowingQuotientBits.run primitive W n d fuel).2+
    rawWork primitive n d (GeneralPaperNaturalGrowingQuotient.run n d fuel).quotient+64*W≤_
  change _≤256*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1)*(W+P) at hg
  change _≤4*P at hr
  change _≤1024*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1)*(W+P)
  nlinarith only [hg,hr,Nat.zero_le ((GeneralPaperConstructedNatDivision.run n d fuel).depth*W),
    Nat.zero_le ((GeneralPaperConstructedNatDivision.run n d fuel).depth*P)]

theorem unit_work (n d fuel : ℕ) (hd : 0<d) :
    (run (fun _ => 1) 1 n d fuel).2≤2048*((GeneralPaperConstructedNatDivision.run n d fuel).depth+1) := by
  have hh := work (fun _ => 1) (by intro a b hab; rfl) 1 n d fuel hd
  nlinarith only [hh]

end Blotto.GeneralPaperConstructedNatDivisionBits

import Blotto.GeneralPaperCacheConstructionGrowth

/-! Literal positive-ceiling bit primitives, operands, partial/native work
fields and scratch. Arbitrary original rational precision is retained once
in the active scalar window; no rational-denominator aggregation executes. -/
namespace Blotto.GeneralPaperPositiveCeilingConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPositiveCeiling
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W H : ℕ) : ℕ := 8*model.rat H+64*W

def controls (model : RationalCostModel) (W : ℕ) (x : ℚ) : List ℕ :=
  let n := x.num.natAbs
  let d := x.den
  let q := n/d
  let r := n%d
  let read := model.rat (rationalWordWidth x)
  let divide := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n d
  let modulus := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) n d
  let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) q 1
  let test := model.rat (GeneralPaperNaturalPrimitivePrice.word r)
  [n,d,q,r,q+1,(bits model W x).1,read,divide,modulus,add,test,read+divide,
    read+divide+modulus,read+divide+modulus+add,read+divide+modulus+add+test,64*W,(bits model W x).2]

def window (model : RationalCostModel) (W : ℕ) (x : ℚ) : ℕ :=
  let n := x.num.natAbs
  let d := x.den
  rationalWordWidth x+fields W (controls model W x)+model.rat (rationalWordWidth x)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n d+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) n d+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (n/d) 1+
    model.rat (GeneralPaperNaturalPrimitivePrice.word (n%d))+128*W

def profile (model : RationalCostModel) (W H : ℕ) : ℕ :=
  H+8*model.rat H+17*(H+natBits (price model W H+64*W+1)+W)+160*W

theorem bounded (model : RationalCostModel) (W H : ℕ) (x : ℚ) (hH : width x≤H) :
    window model W x≤profile model W H := by
  let n := x.num.natAbs
  let d := x.den
  let q := n/d
  let r := n%d
  let read := model.rat (rationalWordWidth x)
  let divide := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n d
  let modulus := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a%b) n d
  let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) q 1
  let test := model.rat (GeneralPaperNaturalPrimitivePrice.word r)
  have hw : (bits model W x).2≤price model W H :=
    (bits_work model W x).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 8 (model.monotone hH)) _)
  have hShape : (bits model W x).2=read+divide+modulus+add+test+64*W := rfl
  have hOut : (bits model W x).1≤n+d+1 := by
    have hq := Nat.div_le_self n d
    change (if r=0 then q else q+1)≤n+d+1
    split_ifs <;> dsimp only [q] <;> omega
  have hq : q≤n := Nat.div_le_self n d
  have hr : r≤n := Nat.mod_le n d
  have hWord : binaryWordWidth (n+d+1)≤H := by
    have ha := GeneralPaperReferenceScaling.word_add n d
    have hb := GeneralPaperReferenceScaling.word_add (n+d) 1
    rw [show binaryWordWidth 1=1 by decide] at hb
    unfold width rationalWordWidth at hH
    dsimp only [n,d] at ha hb ⊢
    omega
  have hCap : natBits (n+d+1+price model W H+64*W+1)≤H+natBits (price model W H+64*W+1) := by
    have h := GeneralPaperReferenceScaling.word_add (n+d+1) (price model W H+64*W+1)
    unfold natBits
    have he : n+d+1+price model W H+64*W+1=(n+d+1)+(price model W H+64*W+1) := by omega
    rw [he]
    omega
  have hf := fields_bound W (H+natBits (price model W H+64*W+1)) (controls model W x) (by
    intro z hz
    apply le_trans (b:=natBits (n+d+1+price model W H+64*W+1)) _ hCap
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    change z=n ∨ z=d ∨ z=q ∨ z=r ∨ z=q+1 ∨ z=(bits model W x).1 ∨ z=read ∨ z=divide ∨
      z=modulus ∨ z=add ∨ z=test ∨ z=read+divide ∨ z=read+divide+modulus ∨ z=read+divide+modulus+add ∨
      z=read+divide+modulus+add+test ∨ z=64*W ∨ z=(bits model W x).2 at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤17*(H+natBits (price model W H+64*W+1)+W)+32*W at hf
  have hx : rationalWordWidth x≤H := by unfold width at hH;omega
  change rationalWordWidth x+fields W (controls model W x)+read+divide+modulus+add+test+128*W≤_
  unfold profile price at *
  omega

@[fun_prop]
theorem scaling (model : RationalCostModel) (H : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W H) := by
  unfold profile price
  fun_prop

end Blotto.GeneralPaperPositiveCeilingConstructionStorage

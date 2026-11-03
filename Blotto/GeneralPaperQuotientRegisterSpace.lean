import Blotto.GeneralPaperQuotientRegisterBounds

/-! Paper-model bit reservations for fixed-register quotient steps.
Both old/new configurations and all step scratch are counted. Arithmetic
scratch is bounded by its bit-operation budget under the paper convention;
no allocator, reference-counting or compiled-stack interpretation is used.
-/
namespace Blotto.GeneralPaperQuotientRegisterSpace
open GeneralPaperQuotientTraversal GeneralPaperQuotientRegisters GeneralPaperQuotientRegisterBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000

def operandWord (n a : ℕ) : ℕ := 1+binaryWordWidth (magnitude n a)
def counterWord (fuel : ℕ) : ℕ := 32+binaryWordWidth (fuel+1)

theorem value_word (n a x : ℕ) (hx : x≤magnitude n a) : binaryWordWidth x≤operandWord n a := by
  have hh := binaryWordWidth_mono hx
  unfold operandWord
  omega

theorem operand_word (n a x : ℕ) (hx : x≤magnitude n a) : 1+binaryWordWidth x≤operandWord n a :=
  Nat.add_le_add_left (binaryWordWidth_mono hx) 1

def upFootprint (W n a : ℕ) (s : UpState) : ℕ :=
  binaryWordWidth n+binaryWordWidth a+binaryWordWidth s.scale+
    binaryWordWidth s.fuel+binaryWordWidth s.count+8*W

def downFootprint (W n a : ℕ) (s : DownState) : ℕ :=
  binaryWordWidth n+binaryWordWidth a+binaryWordWidth s.scale+
    binaryWordWidth s.quotient+binaryWordWidth s.remainder+binaryWordWidth s.remaining+8*W

theorem up_footprint (W n a fuel : ℕ) (s : UpState) (h : UpValid n a fuel s) (hW : counterWord fuel≤W) :
    upFootprint W n a s≤3*operandWord n a+10*W := by
  have hn := value_word n a n (by unfold magnitude; omega)
  have ha := value_word n a a (by unfold magnitude; omega)
  have hs := value_word n a s.scale h.2.1
  have hf := binaryWordWidth_mono (show s.fuel≤fuel+1 by have hh:=h.2.2; omega)
  have hc := binaryWordWidth_mono (show s.count≤fuel+1 by have hh:=h.2.2; omega)
  unfold upFootprint counterWord at *
  omega

theorem down_footprint (W n a fuel : ℕ) (s : DownState) (h : DownValid n a fuel s) (hW : counterWord fuel≤W) :
    downFootprint W n a s≤5*operandWord n a+9*W := by
  have hn := value_word n a n (by unfold magnitude; omega)
  have ha := value_word n a a (by unfold magnitude; omega)
  have hs := value_word n a s.scale h.2.2.2.2
  have hp := down_payload n a fuel s h
  have hq := value_word n a s.quotient (by unfold magnitude; omega)
  have hr := value_word n a s.remainder (by unfold magnitude; omega)
  have hf := binaryWordWidth_mono (show s.remaining≤fuel+1 by have hh:=h.2.1; omega)
  unfold downFootprint counterWord at *
  omega

def upScratch (model : RationalCostModel) (n : ℕ) (s : UpState) : ℕ :=
  GeneralPaperIntegerWordPrice.compare model.rat n s.scale+
    if s.fuel=0 ∨ n<s.scale then 0 else
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 s.scale

theorem up_scratch (model : RationalCostModel) (n a fuel : ℕ) (s : UpState) (h : UpValid n a fuel s) :
    upScratch model n s≤3*model.rat (operandWord n a) := by
  have hn := operand_word n a n (by unfold magnitude; omega)
  have hs := operand_word n a s.scale h.2.1
  have hc := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone n s.scale (operandWord n a) hn hs
  unfold upScratch
  split
  · omega
  · rename_i hContinue
    have hDouble : 2*s.scale≤magnitude n a := by unfold magnitude; omega
    have hd := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b)
      2 s.scale (magnitude n a) (by unfold magnitude; omega) h.2.1 hDouble
    change _≤2*model.rat (operandWord n a) at hd
    omega

def downScratch (model : RationalCostModel) (s : DownState) : ℕ :=
  let smaller := s.scale/2
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) s.scale 2+
  GeneralPaperIntegerWordPrice.compare model.rat smaller s.remainder+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 s.quotient+
  if smaller≤s.remainder then
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (2*s.quotient) 1+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) s.remainder smaller
  else model.rat (1+binaryWordWidth s.remainder)

theorem down_scratch (model : RationalCostModel) (n a fuel : ℕ) (s : DownState) (h : DownValid n a fuel s) :
    downScratch model s≤9*model.rat (operandWord n a) := by
  let M := magnitude n a
  let P := model.rat (operandWord n a)
  have hp := down_payload n a fuel s h
  have hn : n≤M := by dsimp [M,magnitude]; omega
  have hScale : s.scale≤M := h.2.2.2.2
  have hHalf : s.scale/2≤M := (show s.scale/2≤s.scale by omega).trans hScale
  have hQ : s.quotient≤M := hp.1.trans hn
  have hR : s.remainder≤M := hp.2.trans hn
  have hDouble : 2*s.quotient≤M := by dsimp [M,magnitude]; omega
  have hPlus : 2*s.quotient+1≤M := by dsimp [M,magnitude]; omega
  have hd := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    s.scale 2 M hScale (by dsimp [M,magnitude]; omega) hHalf
  have hc := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone (s.scale/2) s.remainder (operandWord n a)
    (operand_word n a _ hHalf) (operand_word n a _ hR)
  have hq := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b)
    2 s.quotient M (by dsimp [M,magnitude]; omega) hQ hDouble
  have ha := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
    (2*s.quotient) 1 M hDouble (by dsimp [M,magnitude]; omega) hPlus
  have hs := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a-b)
    s.remainder (s.scale/2) M hR hHalf (by omega)
  have hr := model.monotone (operand_word n a s.remainder hR)
  change _≤2*P at hd hq ha hs
  change _≤P at hc hr
  unfold downScratch
  dsimp only
  change _≤9*P
  split <;> omega

def upWindow (model : RationalCostModel) (W n a : ℕ) (s next : UpState) : ℕ :=
  upFootprint W n a s+upFootprint W n a next+upScratch model n s+16*W

def downWindow (model : RationalCostModel) (W n a : ℕ) (s next : DownState) : ℕ :=
  downFootprint W n a s+downFootprint W n a next+downScratch model s+16*W

theorem up_window (model : RationalCostModel) (W n a fuel : ℕ) (s next : UpState)
    (h : UpValid n a fuel s) (hs : upStep n s=some next) (hW : counterWord fuel≤W) :
    upWindow model W n a s next≤64*(W+model.rat (operandWord n a)) := by
  have h0 := up_footprint W n a fuel s h hW
  have h1 := up_footprint W n a fuel next (up_next n a fuel s next h hs) hW
  have h2 := up_scratch model n a fuel s h
  have hP := model.word_le (operandWord n a)
  unfold upWindow
  omega

theorem down_window (model : RationalCostModel) (W n a fuel : ℕ) (ha : 0<a) (s next : DownState)
    (h : DownValid n a fuel s) (hs : downStep s=some next) (hW : counterWord fuel≤W) :
    downWindow model W n a s next≤64*(W+model.rat (operandWord n a)) := by
  have h0 := down_footprint W n a fuel s h hW
  have h1 := down_footprint W n a fuel next (down_next n a fuel ha s next h hs) hW
  have h2 := down_scratch model n a fuel s h
  have hP := model.word_le (operandWord n a)
  unfold downWindow
  omega

end Blotto.GeneralPaperQuotientRegisterSpace

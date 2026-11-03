import Blotto.GeneralPaperDyadicMultiplyPrice

/-! Encoded exponent and degree bounds at every constructed table prefix.
The exponent potential includes one normalization allowance and doubles on
squaring. Its logarithm, rather than its expanded magnitude, controls cost.
-/
namespace Blotto.GeneralPaperPowerTableBounds
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
set_option autoImplicit false
set_option maxHeartbeats 6000000

def budget (p width : ℕ) (base : Number) : ℕ := 2^width*(base.exponent.natAbs+p+1)
def width (p columns : ℕ) (base : Number) : ℕ :=
  256+64*(p+columns+binaryWordWidth (base.exponent.natAbs+p+1)+1)

theorem exponent_potential (unit p columns : ℕ) (base : Number) :
    (build unit p base columns).top.number.exponent.natAbs+p+1≤budget p columns base ∧
      ∀ entry∈(build unit p base columns).entries,entry.number.exponent.natAbs+p+1≤budget p columns base := by
  induction columns with
  | zero =>
    constructor
    · change base.exponent.natAbs+p+1≤2^0*(base.exponent.natAbs+p+1); simp only [pow_zero,one_mul,le_refl]
    · intro entry he; cases he
  | succ columns ih =>
    let previous := build unit p base columns
    have hMono : budget p columns base≤budget p (columns+1) base :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega))
    have hNext : (if columns=0 then (⟨1,base⟩:Entry) else square unit p previous.top).number.exponent.natAbs+p+1≤budget p (columns+1) base := by
      split
      · have hOne : 1≤2^(columns+1) := by have := Nat.two_pow_pos (columns+1); omega
        simpa only [one_mul,budget] using Nat.mul_le_mul_right (base.exponent.natAbs+p+1) hOne
      · have he := GeneralPaperDyadicFastMultiply.exponent_bound unit p previous.top.number previous.top.number
        have hPrev := ih.1
        change previous.top.number.exponent.natAbs+p+1≤budget p columns base at hPrev
        change (GeneralPaperDyadicMultiply.multiply unit p previous.top.number previous.top.number).number.exponent.natAbs+p+1≤_
        dsimp only [budget]
        rw [pow_succ]
        dsimp only [budget] at hPrev
        nlinarith only [he,hPrev]
    refine ⟨hNext,?_⟩
    intro entry he
    change entry∈(if columns=0 then (⟨1,base⟩:Entry) else square unit p previous.top)::previous.entries at he
    rcases List.mem_cons.mp he with he|he
    · subst entry; exact hNext
    · exact (ih.2 entry he).trans hMono

theorem top_degree (unit p columns : ℕ) (base : Number) : (build unit p base columns).top.degree≤2^columns := by
  cases columns with
  | zero => exact Nat.le_refl _
  | succ columns =>
    rw [GeneralPaperRoundedPowerTable.top_degree]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)

theorem budget_word (p columns : ℕ) (base : Number) :
    binaryWordWidth (budget p columns base)≤1+2*columns+binaryWordWidth (base.exponent.natAbs+p+1) := by
  have hm := binaryWordWidth_mul (2^columns) (base.exponent.natAbs+p+1)
  have hp := GeneralPaperNatPowerOperands.power_width 2 columns
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  unfold budget
  omega

theorem budget_mono (p columns : ℕ) (base : Number) : budget p columns base≤budget p (columns+1) base :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega))

theorem multiply_width (unit p columns : ℕ) (hPower : unit=2^p) (base : Number) (left right : Number)
    (hl : left.exponent.natAbs≤budget p columns base) (hr : right.exponent.natAbs≤budget p columns base) :
    GeneralPaperDyadicMultiplyPrice.width unit p left right≤width p columns base := by
  have hu := GeneralPaperParameterOperandBounds.dyadic_word p
  rw [(GeneralPaperScoreScaleParameters.power_data p).1] at hu
  rw [←hPower] at hu
  have hp := GeneralPaperInitializerControlCounters.word_le_self p
  have hL := (binaryWordWidth_mono hl).trans (budget_word p columns base)
  have hR := (binaryWordWidth_mono hr).trans (budget_word p columns base)
  unfold GeneralPaperDyadicMultiplyPrice.width width
  omega

theorem mono (p columns : ℕ) (base : Number) : width p columns base≤width p (columns+1) base := by unfold width; omega

def metadataCap (p columns : ℕ) : ℕ := (columns+1)*(12*(p+1)+82)+2

theorem metadata_word (p columns : ℕ) (base : Number) : 1+binaryWordWidth (metadataCap p columns)≤width p columns base := by
  have hp := GeneralPaperInitializerControlCounters.word_le_self (p+1)
  have hc := GeneralPaperInitializerControlCounters.word_le_self (columns+1)
  have hm := binaryWordWidth_mul 12 (p+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (12*(p+1)) 82
  have hb := binaryWordWidth_mul (columns+1) (12*(p+1)+82)
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add ((columns+1)*(12*(p+1)+82)) 2
  have h12 : binaryWordWidth 12=4 := by decide
  have h82 : binaryWordWidth 82=7 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  unfold metadataCap width
  omega

def metadataCost (primitive : ℕ → ℕ) (old child bump : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) old child+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (old+child) bump

theorem metadata_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (old child bump cap L : ℕ)
    (h : old+child+bump≤cap) (hWidth : 1+binaryWordWidth cap≤L) : metadataCost primitive old child bump≤4*primitive L := by
  have ha := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) old child cap (by omega) (by omega) (by omega)
  have hb := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) (old+child) bump cap (by omega) (by omega) h
  have hp := hMono hWidth
  have h1 := ha.trans (Nat.mul_le_mul_left 2 hp)
  have h2 := hb.trans (Nat.mul_le_mul_left 2 hp)
  unfold metadataCost
  omega

end Blotto.GeneralPaperPowerTableBounds

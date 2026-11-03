import Blotto.GeneralPaperMaterializedPowerCache

/-! Fixed query operand envelope and a consumable exponent budget. A
chosen table entry can increase the accumulator magnitude by at most its
own magnitude plus one normalization shift; removing that entry pays it.
-/
namespace Blotto.GeneralPaperPowerQueryBounds
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
set_option autoImplicit false
set_option maxHeartbeats 6000000

structure Entries (unit D E : ℕ) (entries : List Entry) : Prop where
  normal : ∀ e∈entries, Normal unit e.number
  degree : ∀ e∈entries, e.degree≤D
  exponent : ∀ e∈entries, e.number.exponent.natAbs≤E

theorem tail (unit D E : ℕ) (entry : Entry) (entries : List Entry) (h : Entries unit D E (entry::entries)) :
    Entries unit D E entries :=
  ⟨fun e he => h.normal e (List.mem_cons_of_mem _ he),fun e he => h.degree e (List.mem_cons_of_mem _ he),
    fun e he => h.exponent e (List.mem_cons_of_mem _ he)⟩

def width (p columns D R : ℕ) : ℕ := 256+64*(p+columns+binaryWordWidth D+binaryWordWidth R+1)

theorem multiply_width (unit p columns D R : ℕ) (hPower : unit=2^p) (left right : Number)
    (hl : left.exponent.natAbs≤R) (hr : right.exponent.natAbs≤R) :
    GeneralPaperDyadicMultiplyPrice.width unit p left right≤width p columns D R := by
  have hu := GeneralPaperParameterOperandBounds.dyadic_word p
  rw [(GeneralPaperScoreScaleParameters.power_data p).1,←hPower] at hu
  have hp := GeneralPaperInitializerControlCounters.word_le_self p
  have hL := binaryWordWidth_mono hl
  have hR := binaryWordWidth_mono hr
  unfold GeneralPaperDyadicMultiplyPrice.width width
  omega

theorem metadata_word (p columns D R : ℕ) :
    1+binaryWordWidth (GeneralPaperPowerTableBounds.metadataCap p columns)≤width p columns D R := by
  have hp := GeneralPaperInitializerControlCounters.word_le_self (p+1)
  have hc := GeneralPaperInitializerControlCounters.word_le_self (columns+1)
  have hm := binaryWordWidth_mul 12 (p+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (12*(p+1)) 82
  have hb := binaryWordWidth_mul (columns+1) (12*(p+1)+82)
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add ((columns+1)*(12*(p+1)+82)) 2
  have h12 : binaryWordWidth 12=4 := by decide
  have h82 : binaryWordWidth 82=7 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  unfold GeneralPaperPowerTableBounds.metadataCap width
  omega

theorem columns_degree (entries : List Entry) (columns : ℕ) (h : GeneralPaperRoundedPowerQuery.Columns entries columns) :
    ∀ entry∈entries,entry.degree≤2^columns := by
  induction columns generalizing entries with
  | zero => cases entries with
    | nil => intro entry he; cases he
    | cons e rest => exact False.elim h
  | succ columns ih =>
    cases entries with
    | nil => exact False.elim h
    | cons e rest =>
      have hc : e.degree=2^columns ∧ GeneralPaperRoundedPowerQuery.Columns rest columns := h
      have hm : 2^columns≤(2:ℕ)^(columns+1) := Nat.pow_le_pow_right (by decide) (by omega)
      intro entry he
      rcases List.mem_cons.mp he with he|he
      · subst entry; rw [hc.1]; exact hm
      · exact (ih rest hc.2 entry he).trans hm

theorem constructed (unit p columns : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (base : Number) (hNormal : Normal unit base) (hPositive : 0<base.mantissa) :
    Entries unit (2^columns) (GeneralPaperPowerTableBounds.budget p columns base)
      (build unit p base columns).entries := by
  refine ⟨?_,columns_degree _ _ (GeneralPaperRoundedPowerQuery.build_columns unit p columns base),?_⟩
  · intro e he
    exact ((build_good unit p hUnit hPower base hNormal hPositive columns).2 e he).2.1
  · intro e he
    have hh := (GeneralPaperPowerTableBounds.exponent_potential unit p columns base).2 e he
    omega

end Blotto.GeneralPaperPowerQueryBounds

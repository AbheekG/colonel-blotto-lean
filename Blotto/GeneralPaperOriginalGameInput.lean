import Blotto.GeneralPaperCalibratedStoredSampler
import Blotto.GeneralPaperNativeDrawHeadline
import Blotto.GeneralPaperNativePreparationTimeHeadline
import Blotto.GeneralPaperRealPreparationHeadline
import Blotto.GeneralPaperOneFieldRealPreparation

/-! The paper's structured original rational game input, before any
one-field/equal/unequal branch is selected. Lengths refer to the retained
binary encodings; valid normalized values are the canonical input model. -/
namespace Blotto.GeneralPaperOriginalGameInput
set_option autoImplicit false

structure Input where
  n : ℕ
  values : FixedArrayTable n ℚ
  selector : RationalFieldSelector n
  correct : ∀ j,values.read j = selector.weight j
  words : BinaryAccuracyWords
  budget : ℚ
  budget_valid : 0 < budget ∧ budget ≤ 1

def epsilon (p : Input) : ℚ := (p.words.numerator.value : ℚ) / p.words.denominator.value

theorem epsilon_positive (p : Input) : 0 < epsilon p :=
  div_pos (by exact_mod_cast p.words.numerator.value_pos) (by exact_mod_cast p.words.denominator.value_pos)

def equalInput (model : RationalCostModel) (p : Input) : GeneralPaperEqualInputDomain.Input model :=
  ⟨p.n,p.values,p.selector,p.correct,(GeneralPaperBinaryAccuracy.prepare id 1 p.words).1,p.words,rfl,p.budget⟩

def unequalInput (p : Input) (hStrict : p.budget < 1) : GeneralPaperNativeResourceDomain.Problem :=
  ⟨p.n,p.values,p.selector,p.correct,p.words,p.budget,⟨p.budget_valid.1,hStrict⟩⟩

theorem equal_epsilon (model : RationalCostModel) (p : Input) :
    GeneralPaperEqualInputHeadline.epsilon (equalInput model p) = epsilon p := rfl

theorem unequal_epsilon (p : Input) (hStrict : p.budget < 1) :
    GeneralPaperNativeWorkingSpaceHeadline.epsilon (unequalInput p hStrict) = epsilon p := rfl

theorem strict_of_ne (p : Input) (hNe : p.budget ≠ 1) : p.budget < 1 :=
  lt_of_le_of_ne p.budget_valid.2 hNe

theorem fields_positive (p : Input) : 0 < p.n := p.selector.fields_positive

end Blotto.GeneralPaperOriginalGameInput

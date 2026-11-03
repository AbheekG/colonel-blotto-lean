import Blotto.GeneralPaperNativeLightWeights

/-! The native reduced-field size identity changes only erased array size
proofs. Physical columns and their references are unchanged; semantic
readers agree with the exact named-field equivalence used in the paper. -/
namespace Blotto.GeneralPaperPhysicalFieldCast
set_option autoImplicit false
set_option maxHeartbeats 1600000

def columns {m p T K : ℕ} (h : m=p) (stored : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    FixedArrayTable p (GeneralPaperQuantizedColumn.Column T K) := h ▸ stored

def dictionary {m p T K : ℕ} (h : m=p) (d : GeneralPaperDictionary.Dictionary T m K) :
    GeneralPaperDictionary.Dictionary T p K := h ▸ d

theorem data {m p T K : ℕ} (h : m=p) (stored : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    (columns h stored).data=stored.data := by subst p;rfl

theorem read {m p T K : ℕ} (h : m=p) (stored : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (j : Fin m) :
    (columns h stored).read (Fin.cast h j)=stored.read j := by subst p;rfl

theorem dictionary_data {m p T K : ℕ} (h : m=p) (stored : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    GeneralPaperRowQuantizer.dictionary (columns h stored)=dictionary h (GeneralPaperRowQuantizer.dictionary stored) := by subst p;rfl

theorem real_row {m p T K : ℕ} (h : m=p) (stored : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hT : 0<T) (i : Fin T) :
    (GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary (columns h stored)) hT).realRow i=
      GeneralPaperFieldRelabel.allocation (finCongr h.symm)
        ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary stored) hT).realRow i) := by subst p;rfl

theorem unit {m p T K : ℕ} (h : m=p) (stored : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hT : 0<T) (hK : 0<K)
    (hu : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary stored) hT hK) :
    GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary (columns h stored)) hT hK := by
  subst p
  exact hu

theorem height {m p T K : ℕ} (h : m=p) (stored : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (H : ℕ)
    (hh : ∀ j l,RationalHeight ((stored.read j).anchors.read l) H) :
    ∀ j l,RationalHeight (((columns h stored).read j).anchors.read l) H := by
  subst p
  exact hh

end Blotto.GeneralPaperPhysicalFieldCast

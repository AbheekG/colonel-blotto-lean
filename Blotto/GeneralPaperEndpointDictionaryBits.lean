import Blotto.GeneralPaperCheckedPairEndpointSize
import Blotto.RationalExpressionWordWidth

/-! Encoding size of the literal dictionary's rational anchors and original
row-label indices. This is a descriptor COMPONENT, not total compiler
working storage, source/control metadata or original-game output size.
-/
namespace Blotto.GeneralPaperEndpointDictionaryBits
open GeneralPaperProxyParameters GeneralPaperEndpointDictionarySize GeneralPaperDictionary
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

def dataBits {T m K : ℕ} (d : Dictionary T m K) : ℕ :=
  (∑ j,∑ l,rationalWordWidth (d.anchor j l))+(∑ i,∑ j,binaryWordWidth (d.label i j).val)

theorem entry_word {m : ℕ} (k : ℕ) (q : ℚ) (hq : RationalHeight q (width m k)) :
    rationalWordWidth q≤13+6*binaryWordWidth (prepare m k).H := by
  have hh := rationalWordWidth_of_height hq
  have hw := width_bound m k
  omega

theorem anchors {T m : ℕ} (k : ℕ) (d : Dictionary T m (prepare m k).K)
    (hc : ∀ j l,RationalHeight (d.anchor j l) (width m k)) :
    (∑ j,∑ l,rationalWordWidth (d.anchor j l))≤m*(prepare m k).K*(13+6*binaryWordWidth (prepare m k).H) := by
  calc
    _ ≤ ∑ _j : Fin m,∑ _l : Fin (prepare m k).K,(13+6*binaryWordWidth (prepare m k).H) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => entry_word k _ (hc j l)))
    _ = _ := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]; ring

theorem labels {T m K : ℕ} (d : Dictionary T m K) :
    (∑ i,∑ j,binaryWordWidth (d.label i j).val)≤T*m*binaryWordWidth K := by
  calc
    _ ≤ ∑ _i : Fin T,∑ _j : Fin m,binaryWordWidth K :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => binaryWordWidth_mono (d.label i j).isLt.le))
    _ = _ := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]; ring

theorem bound {T m : ℕ} (k : ℕ) (d : Dictionary T m (prepare m k).K)
    (hc : ∀ j l,RationalHeight (d.anchor j l) (width m k)) :
    dataBits d≤m*(prepare m k).K*(13+6*binaryWordWidth (prepare m k).H)+T*m*binaryWordWidth (prepare m k).K :=
  Nat.add_le_add (anchors k d hc) (labels d)

theorem actual_pair {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ pair,GeneralPaperCheckedSourcePair.run k Qv hQv weights hp hs b=some pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair ∧
      ((GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich → dataBits pair.rich≤
        m*(prepare m k).K*(13+6*binaryWordWidth (prepare m k).H)+
          (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows*m*binaryWordWidth (prepare m k).K) ∧
      ((GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor → dataBits pair.poor≤
        m*(prepare m k).K*(13+6*binaryWordWidth (prepare m k).H)+
          (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows*m*binaryWordWidth (prepare m k).K) := by
  obtain ⟨pair,hr,hc,hA,hB⟩ := GeneralPaperCheckedPairEndpointSize.run_contract k Qv hm hQv weights hp hs b hb
  exact ⟨pair,hr,hc,fun hm => bound k pair.rich (hA hm),fun hm => bound k pair.poor (hB hm)⟩

end Blotto.GeneralPaperEndpointDictionaryBits

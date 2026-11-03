import Blotto.GeneralPaperDictionary

/-! Literal floor scores and the strict lower-score threshold of the selected
general algorithm. `slackTuples` is an enumerative reference specification;
an efficient exact-score DP and its costs must refine it separately. The
transfer theorem uses actual continuous security, not a numerical upper
certificate. Constructing its endpoint dictionary remains a separate task.
-/
namespace Blotto.GeneralPaperStrictScore
open GeneralPaperDictionary
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

def score {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) : ℕ :=
  ⌊(S:ℚ)*v.weight j*((l.val+1:ℚ)/(K:ℚ))⌋₊

def totalScore {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (l : Fin m → Fin K) : ℕ :=
  ∑ j,score v S j (l j)

theorem score_bounds {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) :
    (score v S j l:ℝ) ≤ (S:ℝ)*v.values.weight j*((l.val+1:ℝ)/(K:ℝ)) ∧
    (S:ℝ)*v.values.weight j*((l.val+1:ℝ)/(K:ℝ)) < (score v S j l:ℝ)+1 := by
  have hp := v.positive j
  have hlo : (score v S j l:ℚ) ≤ (S:ℚ)*v.weight j*((l.val+1:ℚ)/(K:ℚ)) :=
    Nat.floor_le (by positivity)
  have hhi : (S:ℚ)*v.weight j*((l.val+1:ℚ)/(K:ℚ)) < (score v S j l:ℚ)+1 :=
    Nat.lt_floor_add_one _
  have hloR : ((score v S j l:ℚ):ℝ) ≤ ((S:ℚ)*v.weight j*((l.val+1:ℚ)/(K:ℚ)):ℝ) := by
    exact_mod_cast hlo
  have hhiR : ((S:ℚ)*v.weight j*((l.val+1:ℚ)/(K:ℚ)):ℝ) < ((score v S j l:ℚ)+1:ℚ) := by
    exact_mod_cast hhi
  change (score v S j l:ℝ) ≤ (S:ℝ)*(v.weight j:ℝ)*((l.val+1:ℝ)/(K:ℝ)) ∧ _
  constructor
  · simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_one] using hloR
  · change (S:ℝ)*(v.weight j:ℝ)*((l.val+1:ℝ)/(K:ℝ)) < _
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_one] using hhiR

theorem totalScore_bounds {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (l : Fin m → Fin K) :
    (totalScore v S l:ℝ)/(S:ℝ) ≤ prefixPayoff v.values l ∧
      prefixPayoff v.values l ≤ ((totalScore v S l:ℝ)+m)/(S:ℝ) := by
  have hs : (0:ℝ)<S := by exact_mod_cast hS
  have hlo := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (score_bounds v S j (l j)).1)
  have hhi := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (score_bounds v S j (l j)).2.le)
  have hSum : (∑ j,(score v S j (l j):ℝ))=(totalScore v S l:ℝ) := by
    simp only [totalScore,Nat.cast_sum]
  have hPrefix : (∑ j,(S:ℝ)*v.values.weight j*((l j).val+1)/(K:ℝ))=
      (S:ℝ)*prefixPayoff v.values l := by
    unfold prefixPayoff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hShape : (∑ j,(S:ℝ)*v.values.weight j*(((l j).val+1)/(K:ℝ)))=
      (S:ℝ)*prefixPayoff v.values l := by
    simpa only [mul_div_assoc] using hPrefix
  rw [hSum,hShape] at hlo
  rw [hShape,Finset.sum_add_distrib,hSum] at hhi
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,mul_one] at hhi
  exact ⟨(div_le_iff₀ hs).mpr (by nlinarith only [hlo]),
    (le_div_iff₀ hs).mpr (by nlinarith only [hhi])⟩

def rationalCost {T m K : ℕ} (d : Dictionary T m K) (l : Fin m → Fin K) : ℚ :=
  ∑ j,d.anchor j (l j)

theorem rationalCost_cast {T m K : ℕ} (d : Dictionary T m K) (l : Fin m → Fin K) :
    (rationalCost d l:ℝ)=cost d l := by simp only [rationalCost,cost,Rat.cast_sum]

def slackTuples {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ) : Finset (Fin m → Fin K) :=
  Finset.univ.filter (fun l => rationalCost d l<budget)

def threshold {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ) (v : RationalFieldSelector m) (S : ℕ) : ℕ :=
  (slackTuples d budget).sup (totalScore v S)

theorem slack_nonempty {T m K : ℕ} (d : Dictionary T m K) (hK : 0<K) (budget : ℚ) (hBudget : 0<budget)
    (hZero : ∀ j,d.anchor j ⟨0,hK⟩=0) : (slackTuples d budget).Nonempty := by
  refine ⟨fun _ => ⟨0,hK⟩,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change (∑ j,d.anchor j ⟨0,hK⟩)<budget
  simpa only [hZero,Finset.sum_const_zero] using hBudget

theorem threshold_attained {T m K : ℕ} (d : Dictionary T m K) (budget : ℚ) (v : RationalFieldSelector m)
    (S : ℕ) (h : (slackTuples d budget).Nonempty) :
    ∃ l,rationalCost d l<budget ∧ threshold d budget v S=totalScore v S l := by
  obtain ⟨l,hl,he⟩ := Finset.exists_mem_eq_sup (slackTuples d budget) h (totalScore v S)
  exact ⟨l,(Finset.mem_filter.mp hl).2,he⟩

theorem threshold_lower {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hBalanced : Balanced d) (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (hOrder : ∀ j,Monotone (d.anchor j)) (hNonnegative : ∀ j l,0 ≤ d.anchor j l)
    (hZero : ∀ j,d.anchor j ⟨0,hK⟩=0) (budget : ℚ) (hBudget : 0<budget) :
    (threshold d budget v S:ℝ)/(S:ℝ) ≤ security v.values (budget:ℝ) (law d hT).law := by
  obtain ⟨l,hl,he⟩ := threshold_attained d budget v S (slack_nonempty d hK budget hBudget hZero)
  rw [he]
  have hc : cost d l<(budget:ℝ) := by rw [← rationalCost_cast]; exact_mod_cast hl
  exact (totalScore_bounds v S hS l).1.trans
    (strict_tuple_lower_bound d hT hBalanced v.values hOrder hNonnegative _ l hc)

theorem largest_affordable {K : ℕ} (a : Fin K → ℚ) (hK : 0<K) (hOrder : Monotone a)
    (hZero : a ⟨0,hK⟩=0) (y : ℝ) (hy : 0≤y) :
    ∃ l : Fin K,∀ r,(a r:ℝ) ≤ y ↔ r ≤ l := by
  let affordable := Finset.univ.filter (fun r : Fin K => (a r:ℝ) ≤ y)
  have hMember : (⟨0,hK⟩ : Fin K) ∈ affordable := by simp [affordable,hZero,hy]
  have hNonempty : affordable.Nonempty := ⟨_,hMember⟩
  refine ⟨affordable.max' hNonempty,?_⟩
  intro r
  constructor
  · intro hr
    exact Finset.le_max' affordable r (by simp only [affordable,Finset.mem_filter,Finset.mem_univ,true_and]; exact hr)
  · intro hr
    have hm := (Finset.mem_filter.mp (Finset.max'_mem affordable hNonempty)).2
    have ha : (a r:ℝ) ≤ a (affordable.max' hNonempty) := by exact_mod_cast hOrder hr
    exact ha.trans hm

def replace {T m K : ℕ} (d : Dictionary T m K) (anchors : Fin m → Fin K → ℚ) : Dictionary T m K :=
  ⟨d.label,anchors⟩

theorem balanced_replace {T m K : ℕ} (d : Dictionary T m K) (h : Balanced d)
    (anchors : Fin m → Fin K → ℚ) : Balanced (replace d anchors) := h

theorem endpoint_security_bound {T m K : ℕ} (old : Dictionary T m K) (anchors : Fin m → Fin K → ℚ)
    (hT : 0<T) (hK : 0<K) (hBalanced : Balanced old) (v : RationalFieldSelector m)
    (S : ℕ) (hS : 0<S) (oldBudget : ℚ) (hOldBudget : 0<oldBudget)
    (hOldOrder : ∀ j,Monotone (old.anchor j)) (hOldNonnegative : ∀ j l,0 ≤ old.anchor j l)
    (hOldZero : ∀ j,old.anchor j ⟨0,hK⟩=0)
    (hNewOrder : ∀ j,Monotone (anchors j)) (hNewZero : ∀ j,anchors j ⟨0,hK⟩=0)
    (budget gamma : ℝ) (hBudget : 0≤budget) (hGap : budget<gamma)
    (hBad : ∀ l,threshold old oldBudget v S<totalScore v S l → gamma ≤ cost (replace old anchors) l) :
    security v.values budget (law (replace old anchors) hT).law ≤
      security v.values (oldBudget:ℝ) (law old hT).law+(m:ℝ)/(S:ℝ) := by
  have hs : (0:ℝ)<S := by exact_mod_cast hS
  have hLower := threshold_lower old hT hK hBalanced v S hS hOldOrder hOldNonnegative hOldZero oldBudget hOldBudget
  apply security_le v.values hBudget
  intro y hy
  have hEach (j : Fin m) := largest_affordable (anchors j) hK (hNewOrder j) (hNewZero j) (y j) (hy.1 j)
  choose l hl using hEach
  have hc : cost (replace old anchors) l ≤ budget := by
    apply le_trans (b := ∑ j,y j)
    · apply Finset.sum_le_sum
      intro j _
      exact (hl j (l j)).mpr le_rfl
    · exact hy.2
  have hScore : totalScore v S l ≤ threshold old oldBudget v S := by
    by_contra h
    have hb := hBad l (lt_of_not_ge h)
    linarith
  have hUpper := prefix_upper (replace old anchors) hT (balanced_replace old hBalanced anchors) v.values l y hl
  have hRounded := (totalScore_bounds v S hS l).2
  have hScoreReal : (totalScore v S l:ℝ) ≤ threshold old oldBudget v S := by exact_mod_cast hScore
  have hFinal := div_le_div_of_nonneg_right hScoreReal hs.le
  rw [add_div] at hRounded
  linarith

theorem one_le_threshold_error {m K : ℕ} (v : RationalFieldSelector m) (hK : 0<K)
    (S : ℕ) (hS : 0<S) (h : ℕ) (hAll : ∀ l : Fin m → Fin K,totalScore v S l ≤ h) :
    (1:ℝ) ≤ ((h:ℝ)+m)/(S:ℝ) := by
  let top : Fin K := ⟨K-1,by omega⟩
  have hk : (K:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hK
  have hIndex : ((K-1:ℕ):ℝ)+1=(K:ℝ) := by exact_mod_cast (Nat.sub_add_cancel (show 1≤K by omega))
  have hp : prefixPayoff v.values (fun _ => top)=1 := by
    unfold prefixPayoff
    dsimp only [top]
    simp only [hIndex,mul_div_cancel_right₀ _ hk]
    exact v.values.normalized
  have hBound := (totalScore_bounds v S hS (fun _ => top)).2
  rw [hp] at hBound
  have hReal : (totalScore v S (fun _ => top):ℝ) ≤ h := by exact_mod_cast hAll (fun _ => top)
  have hs : (0:ℝ) ≤ S := by positivity
  have he : (totalScore v S (fun _ => top):ℝ)+(m:ℝ) ≤ (h:ℝ)+(m:ℝ) := by linarith only [hReal]
  exact hBound.trans (div_le_div_of_nonneg_right he hs)

theorem empty_bad_security_bound {T m K : ℕ} (old : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hBalanced : Balanced old) (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (hOrder : ∀ j,Monotone (old.anchor j)) (hNonnegative : ∀ j l,0 ≤ old.anchor j l)
    (hZero : ∀ j,old.anchor j ⟨0,hK⟩=0) (oldBudget : ℚ) (hOldBudget : 0<oldBudget)
    (hAll : ∀ l : Fin m → Fin K,totalScore v S l ≤ threshold old oldBudget v S) (budget : ℝ) (hBudget : 0≤budget) :
    security v.values budget (law (replace old (fun _ _ => 0)) hT).law ≤
      security v.values (oldBudget:ℝ) (law old hT).law+(m:ℝ)/(S:ℝ) := by
  have hOne := one_le_threshold_error v hK S hS _ hAll
  have hLower := threshold_lower old hT hK hBalanced v S hS hOrder hNonnegative hZero oldBudget hOldBudget
  have hUpper := ContinuousSecurityValues.security_le_one v.values budget hBudget
    (law (replace old (fun _ _ => 0)) hT).law
  rw [add_div] at hOne
  linarith

theorem security_mono_budget {m : ℕ} (v : Values m) (a b : ℝ) (ha : 0≤a) (hab : a≤b) (p : Mixed m) :
    security v a p ≤ security v b p := by
  apply security_le v ha
  intro y hy
  exact purePayoff_le_security v ⟨hy.1,hy.2.trans hab⟩ p

end Blotto.GeneralPaperStrictScore

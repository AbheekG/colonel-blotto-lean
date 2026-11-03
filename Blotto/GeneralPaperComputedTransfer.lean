import Blotto.GeneralPaperTransferPreparation

/-! Semantic budget-transfer bounds from the actual prepared dictionary
and computed strict score threshold. Endpoint existence and construction are
separate obligations; these theorems accept its explicit affine constraints.
No numerical upper security certificate or tuple enumeration is evaluated.
-/
namespace Blotto.GeneralPaperTransferPreparation
open GeneralPaperDictionary GeneralPaperStrictScore GeneralPaperComputedThreshold
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem reference_threshold {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) :
    GeneralPaperStrictScore.threshold (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary
      (opposingProxy/ownBudget) v S=(prepare hT hK hDiv rows ownBudget opposingProxy v S).threshold := by
  rw [← compute_eq_reference _ v S hK,prepare_threshold]

theorem endpoint_bound {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (hOpposing : 0<opposingProxy) (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (hRows : ∀ i,Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ)))
    (budget gamma : ℝ) (hBudget : 0≤budget) (hGap : budget<gamma) :
    let p := prepare hT hK hDiv rows ownBudget opposingProxy v S
    ∀ anchors : Fin m → Fin K → ℚ,
      (∀ j,Monotone (anchors j)) → (∀ j,anchors j ⟨0,hK⟩=0) →
      (∀ l,p.threshold<totalScore v S l → gamma≤cost (replace p.dictionary anchors) l) →
      security v.values budget (law (replace p.dictionary anchors) hT).law ≤
        security v.values (opposingProxy:ℝ) (law (GeneralPaperRowQuantizer.original rows) hT).law+
          1/(K:ℝ)+(m:ℝ)/(S:ℝ) := by
  dsimp only
  intro anchors hOrder hZero hBad
  have hu := prepared_unit hT hK hDiv rows ownBudget opposingProxy hOwn v S hRows
  have ht := reference_threshold hT hK hDiv rows ownBudget opposingProxy v S
  have he := endpoint_security_bound _ anchors hT hK hu.balanced v S hS
    (opposingProxy/ownBudget) (div_pos hOpposing hOwn) hu.ordered hu.nonnegative hu.zero hOrder hZero
    budget gamma hBudget hGap (fun l hl => hBad l (by rwa [ht] at hl))
  have hs := source_security hT hK hDiv rows ownBudget opposingProxy hOwn hOpposing.le v S hRows
  linarith only [he,hs]

theorem empty_bad_bound {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (hOpposing : 0<opposingProxy) (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (hRows : ∀ i,Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ)))
    (budget : ℝ) (hBudget : 0≤budget) :
    let p := prepare hT hK hDiv rows ownBudget opposingProxy v S
    (∀ l : Fin m → Fin K,totalScore v S l≤p.threshold) →
      security v.values budget (law (replace p.dictionary (fun _ _ => 0)) hT).law ≤
        security v.values (opposingProxy:ℝ) (law (GeneralPaperRowQuantizer.original rows) hT).law+
          1/(K:ℝ)+(m:ℝ)/(S:ℝ) := by
  dsimp only
  intro hAll
  have hu := prepared_unit hT hK hDiv rows ownBudget opposingProxy hOwn v S hRows
  have ht := reference_threshold hT hK hDiv rows ownBudget opposingProxy v S
  have he := empty_bad_security_bound _ hT hK hu.balanced v S hS hu.ordered hu.nonnegative hu.zero
    (opposingProxy/ownBudget) (div_pos hOpposing hOwn) (fun l => by rw [ht]; exact hAll l) budget hBudget
  have hs := source_security hT hK hDiv rows ownBudget opposingProxy hOwn hOpposing.le v S hRows
  linarith only [he,hs]

theorem unchanged_bound {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (hOpposing : 0≤opposingProxy) (v : RationalFieldSelector m) (S : ℕ)
    (hRows : ∀ i,Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ)))
    (budget : ℝ) (hBudget : 0≤budget) (hSmaller : budget≤((opposingProxy/ownBudget:ℚ):ℝ)) :
    security v.values budget (law (prepare hT hK hDiv rows ownBudget opposingProxy v S).dictionary hT).law ≤
      security v.values (opposingProxy:ℝ) (law (GeneralPaperRowQuantizer.original rows) hT).law+1/(K:ℝ) := by
  exact (security_mono_budget v.values budget _ hBudget hSmaller _).trans
    (source_security hT hK hDiv rows ownBudget opposingProxy hOwn hOpposing v S hRows)

theorem replacement_rows {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (anchors : Fin m → Fin K → ℚ) (hOrder : ∀ j,Monotone (anchors j))
    (hZero : ∀ j,anchors j ⟨0,hK⟩=0)
    (hRows : ∀ i, (∑ j,(anchors j (d.label i j):ℝ))≤1) (i : Fin T) :
    Feasible 1 ((law (replace d anchors) hT).realRow i) := by
  refine ⟨?_,hRows i⟩
  intro j
  have hn := hOrder j (show (⟨0,hK⟩ : Fin K)≤d.label i j by
    change 0≤(d.label i j).val
    exact Nat.zero_le _)
  rw [hZero j] at hn
  change (0:ℝ)≤(anchors j (d.label i j):ℝ)
  exact_mod_cast hn

theorem replacement_supported {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (anchors : Fin m → Fin K → ℚ) (hOrder : ∀ j,Monotone (anchors j))
    (hZero : ∀ j,anchors j ⟨0,hK⟩=0)
    (hRows : ∀ i, (∑ j,(anchors j (d.label i j):ℝ))≤1) :
    Supported 1 (law (replace d anchors) hT).law :=
  RationalWholeRowLaw.law_supported _ 1 (replacement_rows d hT hK anchors hOrder hZero hRows)

theorem normalized_pair_bound {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rowsA rowsB : FixedArrayTable T (FixedArrayTable m ℚ)) (rho : ℚ) (hRho : 0<rho)
    (v : RationalFieldSelector m) (S : ℕ)
    (hA : ∀ i,Feasible 1 (fun j => ((rowsA.read i).read j:ℝ)))
    (hB : ∀ i,Feasible (rho:ℝ) (fun j => ((rowsB.read i).read j:ℝ)))
    (delta : ℝ) (hSource :
      security v.values (rho:ℝ) (law (GeneralPaperRowQuantizer.original rowsA) hT).law+
        security v.values 1 (law (GeneralPaperRowQuantizer.original rowsB) hT).law≤1+delta) :
    security v.values (rho:ℝ) (law (prepare hT hK hDiv rowsA 1 rho v S).dictionary hT).law+
      security v.values (1/(rho:ℝ)) (law (prepare hT hK hDiv rowsB rho 1 v S).dictionary hT).law≤
        1+delta+2/(K:ℝ) := by
  have hA' : ∀ i,Feasible ((1:ℚ):ℝ) (fun j => ((rowsA.read i).read j:ℝ)) := by
    simpa only [Rat.cast_one] using hA
  have ha := source_security hT hK hDiv rowsA 1 rho (by norm_num) hRho.le v S hA'
  have hb := source_security hT hK hDiv rowsB rho 1 hRho (by norm_num) v S hB
  simp only [div_one,Rat.cast_div,Rat.cast_one] at ha hb
  rw [show 2/(K:ℝ)=1/(K:ℝ)+1/(K:ℝ) by ring]
  linarith only [ha,hb,hSource]

end Blotto.GeneralPaperTransferPreparation

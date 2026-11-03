import Blotto.GeneralPaperProfitGridPoints

/-! Largest grid entry below a strict integer cut, using the retained
arithmetic-only binary rank search. A caller supplies a precomputed depth;
there is no integer-floor or input-encoding-length primitive in a query.
-/
namespace Blotto.GeneralPaperFloorSearch
open GeneralPaperRankSearch
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result (n : ℕ) where
  label : Fin n
  work : ℕ

def lookup {n : ℕ} (values : FixedArrayTable n ℕ) (hN : 0<n) (depth cut : ℕ) : Result n :=
  let found := run values cut depth depth 0 n
  ⟨⟨min (found.rank-1) (n-1),by have := Nat.min_le_right (found.rank-1) (n-1); omega⟩,found.work+16⟩

theorem search_valid {n : ℕ} (values : FixedArrayTable n ℕ) (depth cut : ℕ)
    (hMono : Monotone values.read) (hSize : n<2^depth) :
    ValidRank values cut (run values cut depth depth 0 n).rank := by
  apply run_spec values cut depth depth 0 n hMono (Nat.zero_le _) (le_refl _) hSize (by simpa only [Nat.sub_zero] using hSize)
  · intro i hi; omega
  · intro i hi; have := i.isLt; omega

theorem lookup_value {n : ℕ} (values : FixedArrayTable n ℕ) (hN : 0<n) (depth cut : ℕ)
    (hMono : Monotone values.read) (hSize : n<2^depth) (hFirst : values.read ⟨0,hN⟩<cut) :
    values.read (lookup values hN depth cut).label<cut := by
  have hs := search_valid values depth cut hMono hSize
  have hr : 0<(run values cut depth depth 0 n).rank := (hs.2 ⟨0,hN⟩).mp hFirst
  apply (hs.2 _).mpr
  change min ((run values cut depth depth 0 n).rank-1) (n-1)<_
  omega

theorem lookup_maximal {n : ℕ} (values : FixedArrayTable n ℕ) (hN : 0<n) (depth cut : ℕ)
    (hMono : Monotone values.read) (hSize : n<2^depth) (hFirst : values.read ⟨0,hN⟩<cut)
    (i : Fin n) (hI : values.read i<cut) : i≤(lookup values hN depth cut).label := by
  have hs := search_valid values depth cut hMono hSize
  have hr : 0<(run values cut depth depth 0 n).rank := (hs.2 ⟨0,hN⟩).mp hFirst
  have hi := (hs.2 i).mp hI
  change i.val≤min ((run values cut depth depth 0 n).rank-1) (n-1)
  have := i.isLt
  omega

theorem lookup_work {n : ℕ} (values : FixedArrayTable n ℕ) (hN : 0<n) (depth cut : ℕ) :
    (lookup values hN depth cut).work≤depth*(12*depth+34)+24 := by
  have he := run_work values cut depth depth 0 n
  change (run values cut depth depth 0 n).work+16≤_
  omega

end Blotto.GeneralPaperFloorSearch

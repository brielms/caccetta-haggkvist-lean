import LeanCH.BR.BR35Local

/-!
# BR(3,5), part 2: the out-neighbourhood `D[O(u)]` and Lemma 5.1 (Lean 4.35.0)

Paper source: `checkpoints/boundary_20261111/BR35_attempt_subagent.md`, sections 3 and 5.

**`five_shape`** (replaces the hand classification of section 3; only what is used later). Let `S` be a 5-set with
no loop, digon or directed triangle, every vertex of which has a head inside `S`. Then `e(D[S]) ≤ 8`, and if
`e(D[S]) = 8` there is a vertex `e ∈ S` heading the four others, each of which has exactly one head in `S`
(shape R of the paper).

Proof. If for some `v` every vertex of `T = S \ {v}` keeps a head in `T`, then `BR(3,1)` (`four_regular`) gives every
`x ∈ T` exactly one head in `T`, so `e(D[S]) = 4 + out_T(v) + in_T(v) ≤ 8`. At equality `v` is adjacent to all of
`T`; the heads `A` of `v` in `T` are closed under the unique head map (a head `b` of `a ∈ A` with `b → v` closes
`v → a → b → v`), so if `v` had a parent in `T`, `A` would be a nonempty set of at most three vertices each with a
head inside (`small_out`). Hence `v` heads all of `T`. Otherwise every `T_v = S \ {v}` has a vertex `t_v` with no head
in `T_v`; its only head in `S` is `v`. The map `v ↦ t_v` is injective, so every vertex of `S` has exactly one head in
`S` and `e(D[S]) = 5`.

**Lemma 5.1 (local forms).** For `m ∈ M`:
* `full_heads`: a full row (`O ⊆ I(m)`) heads nothing in `O` and only vertices of `I` that head nothing in `O`
  (`I₀`), so `5 ≤ out_M(m) + out_{I₀}(m)` (paper (L6)).
* `noMO`: a row missing at most one vertex of `O` heads nothing in `O` (`m → x` needs `x ↛ m` and a head `y ∈ O` of
  `x` with `y ↛ m`).
* `p_le`: a vertex `w ∈ I` headed by `m` heads only vertices of `O` that miss `m` (paper (L3)).
-/

namespace LeanCH.BR.BR35

open CH Compose.Boundary Compose.FloorSix

section generic

variable {G : CH.Digraph} {n : Nat}

/-- **The 5-vertex lemma.** -/
theorem five_shape (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {S : Finset Nat} (hS : S ⊆ Finset.range n) (hcard : S.card = 5) (pos : ∀ x ∈ S, 1 ≤ oc G S x) :
    ∑ x ∈ S, oc G S x ≤ 8 ∧
      (8 ≤ ∑ x ∈ S, oc G S x → ∃ e ∈ S, ∀ c ∈ S, c ≠ e → G e c = true ∧ oc G S c = 1) := by
  classical
  have lt : ∀ x ∈ S, x < n := fun x hx => Finset.mem_range.mp (hS hx)
  by_cases hA : ∃ v ∈ S, ∀ x ∈ S.erase v, 1 ≤ oc G (S.erase v) x
  · obtain ⟨v, hv, hkeep⟩ := hA
    have hvn : v < n := lt v hv
    have hTsub : S.erase v ⊆ Finset.range n := (Finset.erase_subset v S).trans hS
    have hTcard : (S.erase v).card = 4 := by rw [Finset.card_erase_of_mem hv, hcard]
    have hvT : v ∉ S.erase v := Finset.notMem_erase v S
    have hST : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
    generalize S.erase v = T at hkeep hTsub hTcard hvT hST
    subst hST
    have reg := four_regular loopless noShort hTsub hTcard hkeep
    have hocS : ∀ x, oc G (insert v T) x = (if G x v = true then 1 else 0) + oc G T x :=
      fun x => oc_insert hvT x
    have hvv : (if G v v = true then 1 else 0) = 0 := by rw [loopless v hvn]; rfl
    have hsum : ∑ x ∈ insert v T, oc G (insert v T) x = oc G T v + ic G T v + 4 := by
      rw [Finset.sum_insert hvT, hocS v, hvv]
      have h1 : ∑ x ∈ T, oc G (insert v T) x = ∑ x ∈ T, ((if G x v = true then 1 else 0) + 1) :=
        Finset.sum_congr rfl (fun x hx => by rw [hocS x, reg x hx])
      rw [h1, Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const, smul_eq_mul, hTcard]
      unfold ic
      omega
    have hbound : oc G T v + ic G T v ≤ 4 := by
      have := oc_ic_le loopless noShort hTsub hvn (B := T) (fun y hy _ => hy)
      rwa [hTcard] at this
    refine ⟨by omega, fun h8 => ⟨v, Finset.mem_insert_self v T, ?_⟩⟩
    have heq : oc G T v + ic G T v = 4 := by omega
    -- every vertex of `T` is adjacent to `v`
    have adj : ∀ y ∈ T, G v y = true ∨ G y v = true := by
      intro y hy
      by_contra hcon
      have h1 := oc_ic_le loopless noShort hTsub hvn (B := T.erase y) (fun z hz hG => by
        refine Finset.mem_erase.mpr ⟨?_, hz⟩
        rintro rfl
        exact hcon hG)
      rw [Finset.card_erase_of_mem hy, hTcard] at h1
      omega
    have hposv : 1 ≤ oc G T v := by
      have := pos v (Finset.mem_insert_self v T)
      rw [hocS v, hvv] at this
      omega
    -- `v` has no parent in `T`
    have hic0 : ic G T v = 0 := by
      by_contra hic
      apply small_out loopless noShort (A := T.filter (fun y => G v y = true))
        ((Finset.filter_subset _ T).trans hTsub) (by unfold oc at heq; omega)
        (Finset.card_pos.mp hposv)
      intro a ha
      obtain ⟨haT, hva⟩ := Finset.mem_filter.mp ha
      obtain ⟨b, hbT, hab⟩ := exists_of_oc (le_of_eq (reg a haT).symm)
      refine ⟨b, Finset.mem_filter.mpr ⟨hbT, ?_⟩, hab⟩
      rcases adj b hbT with h | h
      · exact h
      · exact (no3 loopless noShort hvn (Finset.mem_range.mp (hTsub haT)) (Finset.mem_range.mp (hTsub hbT))
          hva hab h).elim
    have hall := all_of_oc (G := G) (A := T) (w := v) (by omega)
    intro c hc hcv
    have hcT : c ∈ T := by
      rcases Finset.mem_insert.mp hc with h | h
      · exact absurd h hcv
      · exact h
    refine ⟨hall c hcT, ?_⟩
    have hcv' : G c v = false := by
      cases h : G c v
      · rfl
      · exact (no2 loopless noShort hvn (Finset.mem_range.mp (hTsub hcT)) (hall c hcT) h).elim
    rw [hocS c, hcv', reg c hcT]
    rfl
  · push Not at hA
    have key : ∀ v ∈ S, ∃ t, t ∈ S ∧ G t v = true ∧ ∀ y ∈ S, y ≠ v → G t y = false := by
      intro v hv
      obtain ⟨t, ht, h0⟩ := hA v hv
      obtain ⟨htv, htS⟩ := Finset.mem_erase.mp ht
      have hno : ∀ y ∈ S, y ≠ v → G t y = false := by
        intro y hy hyv
        cases h : G t y
        · rfl
        · have := oc_pos (A := S.erase v) (Finset.mem_erase.mpr ⟨hyv, hy⟩) h
          omega
      obtain ⟨y, hy, hty⟩ := exists_of_oc (pos t htS)
      have hyv : y = v := by
        by_contra hne
        rw [hno y hy hne] at hty
        exact Bool.false_ne_true hty
      exact ⟨t, htS, hyv ▸ hty, hno⟩
    choose! t ht using key
    have hone : ∀ v ∈ S, oc G S (t v) = 1 := by
      intro v hv
      obtain ⟨htS, htv, hno⟩ := ht v hv
      have h1 : oc G S (t v) ≤ ({v} : Finset Nat).card := oc_le_of_sub (fun y hy hG => by
        by_contra hne
        rw [hno y hy (by simpa using hne)] at hG
        exact Bool.false_ne_true hG)
      have h2 := pos (t v) htS
      simp only [Finset.card_singleton] at h1
      omega
    have hmaps : Set.MapsTo t ↑S ↑(S.filter (fun x => oc G S x = 1)) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨(ht v hv).1, hone v hv⟩
    have hinj : Set.InjOn t ↑S := by
      intro v1 h1 v2 h2 heq
      by_contra hne
      have a := (ht v1 h1).2.1
      rw [heq, (ht v2 h2).2.2 v1 h1 hne] at a
      exact Bool.false_ne_true a
    have hcardW := Finset.card_le_card_of_injOn t hmaps hinj
    have hWS := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ S) hcardW
    have hall : ∀ x ∈ S, oc G S x = 1 := fun x hx => by
      rw [← hWS] at hx
      exact (Finset.mem_filter.mp hx).2
    have h5 : ∑ x ∈ S, oc G S x = 5 := by
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, hcard]
    exact ⟨by omega, fun h => by omega⟩

end generic

namespace Root

variable {G : CH.Digraph} {u : Nat} {I O M : Finset Nat} (R : Root G u I O M)
include R

/-- (L6) A full row of `M` heads nothing in `O`, and its heads in `I` lie in `I₀`. -/
theorem full_heads {m : Nat} (hm : m ∈ M) (hfull : ∀ x ∈ O, G x m = true) :
    5 ≤ oc G M m + oc G (I.filter (fun w => ∀ x ∈ O, G w x = false)) m := by
  have h1 := R.M_out hm
  have h2 : oc G O m = 0 := oc_eq_zero (fun x hx => R.H.back (R.ltO hx) (R.ltM hm) (hfull x hx))
  have h3 : oc G (I \ I.filter (fun w => ∀ x ∈ O, G w x = false)) m = 0 := by
    apply oc_eq_zero
    intro w hw
    obtain ⟨hwI, hwn⟩ := Finset.mem_sdiff.mp hw
    cases h : G m w
    · rfl
    · exfalso
      apply hwn
      refine Finset.mem_filter.mpr ⟨hwI, fun x hx => ?_⟩
      cases h' : G w x
      · rfl
      · have := R.H.tri (R.ltM hm) (R.ltI hwI) (R.ltO hx) h h'
        rw [hfull x hx] at this
        exact Bool.noConfusion this
  have h4 := oc_sdiff (G := G) (Finset.filter_subset (fun w => ∀ x ∈ O, G w x = false) I) m
  omega

/-- Lemma 5.1, local form: a row of `M` missing at most one vertex of `O` heads nothing in `O`. -/
theorem noMO {m : Nat} (hm : m ∈ M) (h4 : 4 ≤ ic G O m) {x : Nat} (hx : x ∈ O) : G m x = false := by
  cases hmx : G m x
  · rfl
  exfalso
  have hxm : G x m = false := R.H.back (R.ltM hm) (R.ltO hx) hmx
  obtain ⟨y, hy, hxy⟩ := exists_of_oc (R.O_inner hx)
  have hym : G y m = false := R.H.tri (R.ltM hm) (R.ltO hx) (R.ltO hy) hmx hxy
  have hxy' : x ≠ y := R.H.ne_of_arc (R.ltO hx) hxy
  have hsub : O.filter (fun v => G v m = true) ⊆ (O.erase x).erase y := by
    intro v hv
    obtain ⟨hvO, hvm⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hvO⟩⟩
    · rintro rfl
      rw [hym] at hvm
      exact Bool.false_ne_true hvm
    · rintro rfl
      rw [hxm] at hvm
      exact Bool.false_ne_true hvm
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hxy', hy⟩), Finset.card_erase_of_mem hx,
    R.cO] at h1
  unfold ic at h4
  omega

/-- (L3) A vertex `w ∈ I` headed by `m ∈ M` heads only vertices of `O` that miss `m`. -/
theorem p_le {m w : Nat} (hm : m ∈ M) (hw : w ∈ I) (hmw : G m w = true) : oc G O w + ic G O m ≤ 5 := by
  have h1 : oc G O w ≤ (O.filter (fun v => ¬ G v m = true)).card := oc_le_of_sub (fun x hx hwx => by
    refine Finset.mem_filter.mpr ⟨hx, ?_⟩
    rw [R.H.tri (R.ltM hm) (R.ltI hw) (R.ltO hx) hmw hwx]
    exact Bool.false_ne_true)
  have h2 := Finset.card_filter_add_card_filter_not (s := O) (fun v => G v m = true)
  rw [R.cO] at h2
  unfold ic
  omega

end Root

end LeanCH.BR.BR35

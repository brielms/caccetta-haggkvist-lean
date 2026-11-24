import checkpoints.shen_extension.FourthStrip

/-!
# The order qs-1 at the cutoff q = 2s-6, for s ≥ 8

`FourthStrip.lean` shows that at this order every vertex has
|B_(R-1)| = s(R-1)+1, |B_R| = sR and |B_(R+1)| = s(R+1)-1 (R = s-3).
This file adds |B_(R-2)| = s(R-2)+1, bounds the missing cells of the table
L_(R-1) → L_R by s+1, shows that no row of that table is empty, and then
applies shell transport with forward distance R and reverse distance R+1.
Every column then misses at least two rows, which needs 2(s-1) missing cells.

The trap lemmas and the two-pass transport follow the other session's
`DotTwoPassShellTransport_20261117.lean`, which treats the symmetric case
q = 2R+1.  Here the reverse path is one step longer than the forward one.
-/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-! ## Generic pieces -/

/-- Equal closed balls of radius k have equal roots when k+1 ≤ q. -/
theorem ball_root_injective_short {D : CH.Digraph} {V : Finset ℕ} {x y k q : ℕ}
    (hf : QFree D V q) (hq : k+1≤q) (hx : x ∈ V) (hy : y ∈ V)
    (he : ball D V x k = ball D V y k) : x=y := by
  by_contra hne
  have hb : y ∈ ball D V x k := he ▸ self_mem_ball hy
  obtain ⟨_,l,hl,wl⟩ := mem_ball.mp hb
  cases l with
  | zero => cases wl; exact hne rfl
  | succ l =>
    obtain ⟨v,wv,_,hvy⟩ := wl.unsnoc
    have hv : v ∈ V := by
      rcases wv.end_mem_or with hh|hh
      · exact hh ▸ hx
      · exact hh
    have hvb : v ∈ ball D V x k := mem_ball.mpr ⟨hv,l,by omega,wv⟩
    rw [he] at hvb
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hvb
    exact hf y (j+1) (by omega) (by omega) (wj.snoc hy hvy)

/-- Two distinct vertices cannot reach each other within radii summing to at most q. -/
theorem return_false {D : CH.Digraph} {V : Finset ℕ} {q i j x y : ℕ}
    (hf : QFree D V q) (hij : i+j≤q) (hne : x≠y)
    (h1 : y ∈ ball D V x i) (h2 : x ∈ ball D V y j) : False := by
  obtain ⟨_,m,hm,wm⟩ := mem_ball.mp h1
  obtain ⟨_,l,hl,wl⟩ := mem_ball.mp h2
  have hpos : 0<m := by
    cases m with
    | zero => cases wm; exact (hne rfl).elim
    | succ m => omega
  exact hf x (m+l) (by omega) (by omega) (wm.append wl)

/-- A walk that never leaves Z without gaining an arc to h stays in Z until h is reached. -/
theorem target_traps {D : CH.Digraph} {V U Z : Finset ℕ} {k y h : ℕ}
    (hy : y ∈ Z) (hh : h ∈ V)
    (hstep : ∀ v ∈ Z, ∀ z ∈ V, D v z = true → z ∈ U)
    (hgood : ∀ z ∈ U, z ∉ Z → D z h = true)
    (hbad : h ∉ ball D V y (k+1)) : ball D V y k ⊆ Z := by
  have aux : ∀ l z, Walk D V y z l → l≤k → z ∈ Z := by
    intro l
    induction l with
    | zero =>
      intro z wz _
      cases wz
      exact hy
    | succ l ih =>
      intro z wz hl
      obtain ⟨v,wv,hz,hvz⟩ := wz.unsnoc
      have hv := ih v wv (by omega)
      have hzU := hstep v hv z hz hvz
      by_contra hn
      exact hbad (mem_ball.mpr ⟨hh,l+2,by omega,wz.snoc hh (hgood z hzU hn)⟩)
  intro z hz
  obtain ⟨_,l,hl,wl⟩ := mem_ball.mp hz
  exact aux l z wl hl

/-- An origin that misses a full column within k+1 steps has its k-ball inside the
punctured k-ball of the root. -/
theorem full_bad_ball {D : CH.Digraph} {V : Finset ℕ} {u k q h y : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : k+1≤q) (hh : h ∈ V)
    (hfull : ∀ z ∈ ball D V u (k+1) \ ball D V u k, D z h = true)
    (hy : y ∈ (ball D V u (k+1)).erase u)
    (hbad : h ∉ ball D V y (k+1)) :
    ball D V y k ⊆ (ball D V u k).erase u := by
  have good (z) (hz : z ∈ (ball D V u (k+1)).erase u)
      (hn : z ∉ (ball D V u k).erase u) : D z h = true := by
    apply hfull z
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hz,
      fun hi => hn (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,hi⟩)⟩
  have step (x) (hx : x ∈ (ball D V u k).erase u) (z) (hz : z ∈ V) (hxz : D x z = true) :
      z ∈ (ball D V u (k+1)).erase u :=
    (mem_outN.mp (outN_prefix_erase_root hf hu hk (Finset.mem_of_mem_erase hx)
      (mem_outN.mpr ⟨hz,hxz⟩))).1
  have hyZ : y ∈ (ball D V u k).erase u := by
    by_contra hn
    exact hbad (mem_ball.mpr ⟨hh,1,by omega,.step hh (good y hy hn) (.refl h)⟩)
  exact target_traps hyZ hh step good hbad

/-- With an empty row a, an origin that misses a column whose only hole is a has its
k-ball inside the punctured k-ball of the root together with a. -/
theorem zero_row_bad_ball {D : CH.Digraph} {V : Finset ℕ} {k q u a h y : ℕ}
    (hf : QFree D V q) (hq : k+2≤q) (hu : u ∈ V)
    (ha : a ∈ ball D V u (k+1) \ ball D V u k)
    (hzero : ∀ z ∈ ball D V u (k+2) \ ball D V u (k+1), ¬ D a z = true)
    (hh : h ∈ V)
    (hgood : ∀ z ∈ ball D V u (k+1) \ ball D V u k, z≠a → D z h = true)
    (hy : y ∈ (ball D V u (k+1)).erase u) (hbad : h ∉ ball D V y (k+1)) :
    ball D V y k ⊆ insert a ((ball D V u k).erase u) := by
  have haB : a ∈ ball D V u (k+1) := (Finset.mem_sdiff.mp ha).1
  have good (z) (hz : z ∈ (ball D V u (k+1)).erase u)
      (hn : z ∉ insert a ((ball D V u k).erase u)) : D z h = true := by
    have hzS : z ∈ ball D V u (k+1) \ ball D V u k :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hz,
        fun hi => hn (Finset.mem_insert.mpr (Or.inr
          (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,hi⟩)))⟩
    exact hgood z hzS (fun he => hn (Finset.mem_insert.mpr (Or.inl he)))
  have step (x) (hx : x ∈ insert a ((ball D V u k).erase u)) (z) (hz : z ∈ V)
      (hxz : D x z = true) : z ∈ (ball D V u (k+1)).erase u := by
    have hxB : x ∈ ball D V u (k+1) := by
      rcases Finset.mem_insert.mp hx with he|hi
      · exact he ▸ haB
      · exact ball_mono_radius (by omega) (Finset.mem_of_mem_erase hi)
    have hzB : z ∈ ball D V u (k+1) := by
      rcases Finset.mem_insert.mp hx with he|hi
      · have hz1 : z ∈ ball D V u (k+2) := ball_step hxB hz hxz
        by_contra hn
        exact hzero z (Finset.mem_sdiff.mpr ⟨hz1,hn⟩) (he ▸ hxz)
      · exact ball_step (Finset.mem_of_mem_erase hi) hz hxz
    refine Finset.mem_erase.mpr ⟨?_,hzB⟩
    intro he
    subst he
    exact no_back_arc hf hu hxB (by omega) hxz
  have hyZ : y ∈ insert a ((ball D V u k).erase u) := by
    by_contra hn
    exact hbad (mem_ball.mpr ⟨hh,1,by omega,.step hh (good y hy hn) (.refl h)⟩)
  exact target_traps hyZ hh step good hbad

/-- A bank of three heads whose large balls are at least as big as the complement of U,
where every origin of U that fails to reach some head has the same small ball Z. -/
theorem exceptional_bank_false {D : CH.Digraph} {V U C Z : Finset ℕ} {q r L k0 : ℕ}
    (hf : QFree D V q) (hUV : U ⊆ V) (hCK : C ⊆ V \ U)
    (hk0 : k0+1≤q) (hrL : r+L≤q) (hL : L+2≤q)
    (hY : ∀ y ∈ U, (∃ h ∈ C, h ∉ ball D V y r) → ball D V y k0 = Z)
    (hsize : ∀ h ∈ C, (V \ U).card≤(ball D V h L).card)
    (hC3 : 3≤C.card) (hCq : C.card≤q) : False := by
  let Y := U.filter (fun y => ∃ h ∈ C, h ∉ ball D V y r)
  have hYcard : Y.card≤1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    obtain ⟨hyU,hyb⟩ := Finset.mem_filter.mp hy
    obtain ⟨hzU,hzb⟩ := Finset.mem_filter.mp hz
    exact ball_root_injective_short hf hk0 (hUV hyU) (hUV hzU)
      ((hY y hyU hyb).trans (hY z hzU hzb).symm)
  let K := (V \ U) ∪ Y
  have hKsize : K.card≤(V \ U).card+1 :=
    (Finset.card_union_le _ _).trans (by omega)
  have hCV : C ⊆ V := fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1
  have hballs (h) (hh : h ∈ C) : ball D V h L ⊆ K := by
    intro z hz
    have hzV : z ∈ V := ball_subset hz
    by_cases hzU : z ∈ U
    · apply Finset.mem_union.mpr
      right
      by_contra hn
      have hforw : h ∈ ball D V z r := by
        by_contra hb
        exact hn (Finset.mem_filter.mpr ⟨hzU,h,hh,hb⟩)
      have hne : z≠h := by
        intro he
        subst he
        exact (Finset.mem_sdiff.mp (hCK hh)).2 hzU
      exact return_false hf hrL hne hforw hz
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hzV,hzU⟩))
  have hCK2 : C ⊆ K := fun h hh => Finset.mem_union.mpr (Or.inl (hCK hh))
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h L).card≤1 := by
    have hc := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    have hs := hsize h hh
    omega
  exact near_full_container_false hf hL hCV hCK2 hballs hmiss hC3 hCq

/-- Shell transport with a reverse path one step longer than the forward radius. -/
theorem asym_column_transport {D : CH.Digraph} {V : Finset ℕ} {k q u h v a : ℕ}
    (hf : QFree D V q) (hq : 2*k+4≤q) (hu : u ∈ V) (hh : h ∈ V)
    (whv : Walk D V h v (k+2)) (hvu : D v u = true)
    (ha : a ∈ ball D V u (k+1)) (hah : D a h = true) :
    a ∈ ball D V v (k+2) \ ball D V v (k+1) := by
  obtain ⟨haV,l,hl,wa⟩ := mem_ball.mp ha
  apply Finset.mem_sdiff.mpr
  constructor
  · exact mem_ball.mpr ⟨haV,l+1,by omega,.step hu hvu wa⟩
  · intro hb
    obtain ⟨_,j,hj,wb⟩ := mem_ball.mp hb
    exact hf a _ (by omega) (by omega) ((Walk.step hh hah whv).append wb)

/-- If layers have m+1 rows, next layers have m heads, every head returns to its root in
exactly k+3 steps and no row is empty, then every column has fewer than m parents. -/
theorem asym_column_bound {D : CH.Digraph} {V : Finset ℕ} {k q m u h : ℕ}
    (hf : QFree D V q) (hq : 2*k+4≤q)
    (hS : ∀ x ∈ V, (ball D V x (k+1) \ ball D V x k).card=m+1)
    (hT : ∀ x ∈ V, (ball D V x (k+2) \ ball D V x (k+1)).card=m)
    (hrev : ∀ x ∈ V, ∀ y ∈ ball D V x (k+2) \ ball D V x (k+1), Walk D V y x (k+3))
    (hrow : ∀ x ∈ V, ∀ a ∈ ball D V x (k+1) \ ball D V x k,
      ∃ z ∈ ball D V x (k+2) \ ball D V x (k+1), D a z = true)
    (hu : u ∈ V) (hh : h ∈ ball D V u (k+2) \ ball D V u (k+1)) :
    ((ball D V u (k+1) \ ball D V u k).filter (fun a => D a h = true)).card < m := by
  by_contra! hlarge
  have hhV : h ∈ V := ball_subset (Finset.mem_sdiff.mp hh).1
  obtain ⟨v,whv,_,hvu⟩ := (hrev u hu h hh).unsnoc
  have hv : v ∈ V := by
    rcases whv.end_mem_or with he|he
    · exact he ▸ hhV
    · exact he
  have hsub : (ball D V u (k+1) \ ball D V u k).filter (fun a => D a h = true) ⊆
      ball D V v (k+2) \ ball D V v (k+1) := by
    intro a ha
    obtain ⟨ha,hah⟩ := Finset.mem_filter.mp ha
    exact asym_column_transport hf hq hu hhV whv hvu (Finset.mem_sdiff.mp ha).1 hah
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hT v hv]; exact hlarge)
  obtain ⟨w,whw,_,hwv⟩ := whv.unsnoc
  have hw : w ∈ V := by
    rcases whw.end_mem_or with he|he
    · exact he ▸ hhV
    · exact he
  have hnot : ¬ (ball D V v (k+1) \ ball D V v k) ⊆
      ball D V w (k+2) \ ball D V w (k+1) := by
    intro hs
    have hc := Finset.card_le_card hs
    rw [hS v hv,hT w hw] at hc
    omega
  obtain ⟨a,ha,han⟩ := Finset.not_subset.mp hnot
  obtain ⟨z,hz,haz⟩ := hrow v hv a ha
  have hzc : z ∈ (ball D V u (k+1) \ ball D V u k).filter (fun a => D a h = true) := by
    rw [heq]; exact hz
  have hzh : D z h = true := (Finset.mem_filter.mp hzc).2
  exact han (asym_column_transport hf hq hv (ball_subset (Finset.mem_sdiff.mp hz).1)
    (Walk.step hhV hzh whw) hwv (Finset.mem_sdiff.mp ha).1 haz)

/-- Missing cells counted by rows and by columns. -/
theorem holes_transpose (D : CH.Digraph) (S T : Finset ℕ) :
    ∑ a ∈ S, (T \ outN D T a).card =
      ∑ h ∈ T, (S \ S.filter (fun a => D a h = true)).card := by
  have row (a : ℕ) : T \ outN D T a = T.filter (fun h => D a h ≠ true) := by
    ext h
    simp only [Finset.mem_sdiff,mem_outN,Finset.mem_filter]
    tauto
  have col (h : ℕ) :
      S \ S.filter (fun a => D a h = true) = S.filter (fun a => D a h ≠ true) := by
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_filter]
    tauto
  simp only [row,col,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

#print axioms exceptional_bank_false
#print axioms asym_column_bound
#print axioms holes_transpose
end LeanCH.BR.ShenFourthStrip

/-! ## The flat order -/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- At the flat order every vertex of L_R(x) returns to x in exactly R+1 steps. -/
theorem flat_reverse_walk {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    ∀ x ∈ V, ∀ y ∈ ball D V x (a+4) \ ball D V x (a+3), Walk D V y x (a+5) := by
  intro x hx y hy
  obtain ⟨hy1,hy0⟩ := Finset.mem_sdiff.mp hy
  have hyV := ball_subset hy1
  have hpos : 1≤(a+7)*(a+5) := by nlinarith
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hi := fun v hv => third_inner_growth hf hm (v:=v) hv hn ha
  have hj (v) (hv : v ∈ V) : (a+7)*(a+5)-1≤(ball D V v (a+5)).card := by
    have h := third_outer_growth hf hm hv hn ha
    omega
  have hcomp := two_balls_boundary_complement hf (by omega : (a+3)+(a+5)≤2*a+8) hi hj
    (by omega) hx
  have hyR : y ∈ reverseBall D V x (a+5) := by
    rw [hcomp]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hyV,hy0⟩)
  have hxb : x ∈ ball D V y (a+5) := (Finset.mem_filter.mp hyR).2
  obtain ⟨_,l,hl,wl⟩ := mem_ball.mp hxb
  by_cases hl4 : l≤a+4
  · exfalso
    have hne : x≠y := by
      intro he
      subst he
      exact hy0 (self_mem_ball hx)
    exact return_false hf (by omega : (a+4)+(a+4)≤2*a+8) hne hy1
      (mem_ball.mpr ⟨hx,l,hl4,wl⟩)
  · have he : l=a+5 := by omega
    subst he
    exact wl

/-- At the flat order every (R-2)-ball has exactly s(R-2)+1 vertices. -/
theorem third_inner2_exact {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hu : u ∈ V)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    (ball D V u (a+2)).card=(a+7)*(a+2)+1 := by
  by_contra hne
  have hflat := third_order_flat hf hm hn ha
  obtain ⟨h3,h4,_,_⟩ := hflat u hu
  have hprev := inner_growth hf hm hu (a+2) (by omega) (by omega)
  let B := ball D V u (a+3)
  let U := B.erase u
  let S := B \ ball D V u (a+2)
  let T := ball D V u (a+4) \ B
  have hBc : B.card=(a+7)*(a+3)+1 := h3
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hu)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    change U.card=B.card-1 at he
    omega
  have hT : T.card+B.card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V u (a+2)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hexp : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hexq : (a+7)*(a+3)=(a+7)*(a+2)+(a+7) := by ring
  have hexr : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hTc : T.card=a+6 := by omega
  have hc : S.card≤a+6 := by omega
  have hprod : (a+6)*(a+6)=(a+7)*(a+4)+(a+8) := by ring
  have budget : U.card+(a+6)*T.card+(a+4)≤(2*a+8)*(a+7)-1+T.card := by
    rw [hTc]; omega
  have hrect := same_rectangle (L:=(2*a+8)*(a+7)-1) hf hm hu (by omega : 1≤a+7)
    (fun F W hf1 hm1 hn1 => by have := order_above_second hf1 hm1 hn1; omega)
    (by omega : (a+2)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by omega : 1≤a+4)
  have hSc : S.card=a+6 := hrect.1
  let C := T.filter (fun h => ∀ w ∈ S, D w h=true)
  have hC : a+4≤C.card := by
    have he : C = (ball D V u ((a+2)+2) \ ball D V u ((a+2)+1)).filter
        (fun h => ∀ w ∈ ball D V u ((a+2)+1) \ ball D V u (a+2), D w h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [he]
    exact hrect.2
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hn (Finset.mem_of_mem_erase hU)⟩
  have hK : (V \ U).card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hsmall : ((ball D V u (a+2)).erase u).card+1=(ball D V u (a+2)).card := by
    have he := Finset.card_erase_of_mem (s:=ball D V u (a+2)) (self_mem_ball hu)
    have hp : 0<(ball D V u (a+2)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    omega
  refine exceptional_bank_false (U:=U) (C:=C) (Z:=(ball D V u (a+2)).erase u)
    (r:=a+3) (L:=a+5) (k0:=a+2) hf hUV hCK (by omega) (by omega) (by omega) ?_ ?_
    (by omega) ((Finset.card_le_card hCT).trans (by omega))
  · rintro y hy ⟨h,hh,hbad⟩
    have hhV : h ∈ V := (Finset.mem_sdiff.mp (hCK hh)).1
    have hsub := full_bad_ball (k:=a+2) hf hu (by omega) hhV
      (fun z hz => (Finset.mem_filter.mp hh).2 z hz) hy hbad
    have hlarge := inner_growth hf hm (hUV hy) (a+2) (by omega) (by omega)
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · intro h hh
    have hhV : h ∈ V := (Finset.mem_sdiff.mp (hCK hh)).1
    have h5 := (hflat h hhV).2.2.1
    omega

/-- Layer sizes at the flat order. -/
theorem flat_layers {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    ∀ x ∈ V, (ball D V x (a+3) \ ball D V x (a+2)).card=a+7 ∧
      (ball D V x (a+4) \ ball D V x (a+3)).card=a+6 := by
  intro x hx
  obtain ⟨h3,h4,_,_⟩ := third_order_flat hf hm hn ha x hx
  have h2 := third_inner2_exact hf hm hx hn ha
  have hS : (ball D V x (a+3) \ ball D V x (a+2)).card+(ball D V x (a+2)).card=
      (ball D V x (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hT : (ball D V x (a+4) \ ball D V x (a+3)).card+(ball D V x (a+3)).card=
      (ball D V x (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hexp : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hexq : (a+7)*(a+3)=(a+7)*(a+2)+(a+7) := by ring
  constructor <;> omega

/-- The table L_(R-1) → L_R has at most s+1 missing cells at the flat order. -/
theorem flat_holes {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hu : u ∈ V)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    ∑ z ∈ ball D V u (a+3) \ ball D V u (a+2),
      ((ball D V u (a+4) \ ball D V u (a+3)) \
        outN D (ball D V u (a+4) \ ball D V u (a+3)) z).card ≤ a+8 := by
  obtain ⟨hSc,hTc⟩ := flat_layers hf hm hn ha u hu
  obtain ⟨h3,_,_,_⟩ := third_order_flat hf hm hn ha u hu
  have hret := minOut_prefix_erase (d:=1) (k:=a+3) hf hu (by omega : (a+3)+1≤2*a+8) hm
    (by change 1+(ball D V u (a+4) \ ball D V u (a+3)).card≤a+7; omega)
  have cap : (2*a+8)*(a+7)-1+
      (∑ z ∈ ball D V u (a+3) \ ball D V u (a+2),
        ((ball D V u (a+4) \ ball D V u (a+3)) \
          outN D (ball D V u (a+4) \ ball D V u (a+3)) z).card) ≤
      ((ball D V u (a+3)).erase u).card+
        (ball D V u (a+3) \ ball D V u (a+2)).card*
          (ball D V u (a+4) \ ball D V u (a+3)).card :=
    PrefixTensor.same_degree_missing_capacity (k:=a+2) hf hm hu (by omega : 1≤a+7)
      (fun F W hf1 hm1 hn1 => by have := order_above_second hf1 hm1 hn1; omega)
      (by omega : (a+2)+2≤2*a+8) hret
  rw [hSc,hTc] at cap
  have he := Finset.card_erase_of_mem (s:=ball D V u (a+3)) (self_mem_ball hu)
  have hprod : (a+7)*(a+6)=(a+7)*(a+4)+2*(a+7) := by ring
  have hexp : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  omega

/-- No row of the table L_(R-1) → L_R is empty at the flat order. -/
theorem flat_no_zero_row {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) :
    ∀ u ∈ V, ∀ z0 ∈ ball D V u (a+3) \ ball D V u (a+2),
      ∃ h ∈ ball D V u (a+4) \ ball D V u (a+3), D z0 h = true := by
  intro u hu z0 hz0
  by_contra hcon
  have hzero : ∀ h ∈ ball D V u (a+4) \ ball D V u (a+3), ¬ D z0 h = true :=
    fun h hh hd => hcon ⟨h,hh,hd⟩
  let S := ball D V u (a+3) \ ball D V u (a+2)
  let T := ball D V u (a+4) \ ball D V u (a+3)
  let U := (ball D V u (a+3)).erase u
  let f := fun h => (S \ S.filter (fun z => D z h = true)).card
  have hholes := flat_holes hf hm hu hn ha
  rw [holes_transpose D] at hholes
  change (∑ h ∈ T, f h)≤a+8 at hholes
  have ham (h) (hh : h ∈ T) : z0 ∈ S \ S.filter (fun z => D z h = true) :=
    Finset.mem_sdiff.mpr ⟨hz0,fun hc => hzero h hh (Finset.mem_filter.mp hc).2⟩
  have fone (h) (hh : h ∈ T) : 1≤f h := Finset.card_pos.mpr ⟨z0,ham h hh⟩
  let B := T.filter (fun h => 2≤f h)
  have hBS : B ⊆ T := Finset.filter_subset _ _
  have hsum : T.card+B.card ≤ ∑ h ∈ T, f h := by
    rw [Finset.card_eq_sum_ones T,Finset.card_eq_sum_ones B]
    simp only [B,Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h hh
    have hp := fone h hh
    split_ifs <;> omega
  have hTc : T.card=a+6 := (flat_layers hf hm hn ha u hu).2
  have hBcard : B.card≤2 := by omega
  let C := T \ B
  have hCsub : C ⊆ T := Finset.sdiff_subset
  have hsplit : C.card+B.card=T.card := Finset.card_sdiff_add_card_eq_card hBS
  have hCcard : a+4≤C.card := by omega
  have hg (h) (hh : h ∈ C) : ∀ z ∈ S, z≠z0 → D z h = true := by
    have hhT := hCsub hh
    have hnB : h ∉ B := (Finset.mem_sdiff.mp hh).2
    have hn2 : ¬ 2≤f h := fun hn2 => hnB (Finset.mem_filter.mpr ⟨hhT,hn2⟩)
    have h1 : (S \ S.filter (fun z => D z h = true)).card=1 := by
      have hp := fone h hhT
      change f h=1
      omega
    have he : ({z0} : Finset ℕ)=S \ S.filter (fun z => D z h = true) :=
      Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (ham h hhT))
        (by rw [h1]; simp)
    intro z hz hza
    by_contra hnd
    have hzm : z ∈ S \ S.filter (fun z => D z h = true) :=
      Finset.mem_sdiff.mpr ⟨hz,fun hc => hnd (Finset.mem_filter.mp hc).2⟩
    rw [← he] at hzm
    exact hza (Finset.mem_singleton.mp hzm)
  have hUV : U ⊆ V := (Finset.erase_subset u _).trans ball_subset
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hnb⟩ := Finset.mem_sdiff.mp (hCsub hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hnb (Finset.mem_of_mem_erase hU)⟩
  have hflat := third_order_flat hf hm hn ha
  obtain ⟨h3,_,_,_⟩ := hflat u hu
  have h2 := third_inner2_exact hf hm hu hn ha
  have hK : (V \ U).card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hUc : U.card+1=(ball D V u (a+3)).card := by
    have he := Finset.card_erase_of_mem (s:=ball D V u (a+3)) (self_mem_ball hu)
    have hp : 0<(ball D V u (a+3)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    change U.card=(ball D V u (a+3)).card-1 at he
    omega
  have hexp : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hexr : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hZc : (insert z0 ((ball D V u (a+2)).erase u)).card=(a+7)*(a+2)+1 := by
    have han : z0 ∉ (ball D V u (a+2)).erase u :=
      fun hh => (Finset.mem_sdiff.mp hz0).2 (Finset.mem_of_mem_erase hh)
    rw [Finset.card_insert_of_notMem han,Finset.card_erase_of_mem (self_mem_ball hu),h2]
    omega
  refine exceptional_bank_false (U:=U) (C:=C) (Z:=insert z0 ((ball D V u (a+2)).erase u))
    (r:=a+3) (L:=a+5) (k0:=a+2) hf hUV hCK (by omega) (by omega) (by omega) ?_ ?_
    (by omega) ((Finset.card_le_card hCsub).trans (by omega))
  · rintro y hy ⟨h,hh,hbad⟩
    have hhV : h ∈ V := (Finset.mem_sdiff.mp (hCK hh)).1
    have hb := zero_row_bad_ball (k:=a+2) hf (by omega) hu hz0 hzero hhV (hg h hh) hy hbad
    have hyc := third_inner2_exact hf hm (hUV hy) hn ha
    exact Finset.eq_of_subset_of_card_le hb (by rw [hZc,hyc])
  · intro h hh
    have hhV : h ∈ V := (Finset.mem_sdiff.mp (hCK hh)).1
    have h5 := (hflat h hhV).2.2.1
    omega

/-- The order qs-1 is impossible when s ≥ 8. -/
theorem third_endpoint_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card)
    (hn : V.card+1=(2*a+8)*(a+7)) (ha : 1≤a) : False := by
  have hne : V.Nonempty := Finset.card_pos.mp (by nlinarith)
  obtain ⟨u,hu⟩ := hne
  have hlay := flat_layers hf hm hn ha
  have hrow := flat_no_zero_row hf hm hn ha
  have hrev := flat_reverse_walk hf hm hn ha
  have hholes := flat_holes hf hm hu hn ha
  rw [holes_transpose D] at hholes
  have hc (h) (hh : h ∈ ball D V u (a+4) \ ball D V u (a+3)) :
      2 ≤ ((ball D V u (a+3) \ ball D V u (a+2)) \
        (ball D V u (a+3) \ ball D V u (a+2)).filter (fun z => D z h = true)).card := by
    have hb : ((ball D V u (a+3) \ ball D V u (a+2)).filter
        (fun z => D z h = true)).card<a+6 :=
      asym_column_bound (k:=a+2) (m:=a+6) hf (by omega)
      (fun x hx => (hlay x hx).1) (fun x hx => (hlay x hx).2) hrev hrow hu hh
    have hs : (ball D V u (a+3) \ ball D V u (a+2)).filter (fun z => D z h = true) ⊆
        ball D V u (a+3) \ ball D V u (a+2) := Finset.filter_subset _ _
    have he := Finset.card_sdiff_add_card_eq_card hs
    rw [(hlay u hu).1] at he
    omega
  have hsum := Finset.sum_le_sum hc
  rw [Finset.sum_const_nat (fun _ _ => rfl),(hlay u hu).2] at hsum
  omega

/-- Order at least qs for s ≥ 8. -/
theorem order_to_top {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ v ∈ V, a+7≤(outN D V v).card) (hne : V.Nonempty)
    (ha : 1≤a) : (2*a+8)*(a+7)≤V.card := by
  have h := order_above_second hf hm hne
  by_contra! hh
  exact third_endpoint_false hf hm (by omega) ha

/-- CH at the cutoff q = 2s-6 for every order n < qs, s ≥ 8. -/
theorem cycle_fourth_strip_below_top {s q n : ℕ} {D : CH.Digraph}
    (hs : 8≤s) (hq : q=2*s-6) (hn : 0<n) (hnq : n<q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a, s=a+7 := ⟨s-7,by omega⟩
  subst s
  have hq' : q=2*a+8 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := order_to_top (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩ (by omega)
  rw [Finset.card_range] at ho
  omega

#print axioms flat_reverse_walk
#print axioms third_inner2_exact
#print axioms flat_holes
#print axioms flat_no_zero_row
#print axioms third_endpoint_false
#print axioms order_to_top
#print axioms cycle_fourth_strip_below_top
end LeanCH.BR.ShenFourthStrip

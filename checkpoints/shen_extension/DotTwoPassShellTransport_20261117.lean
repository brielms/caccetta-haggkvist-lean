import checkpoints.shen_extension.ThirdStripEndpoints

/-!
Actual-source two-pass shell transport. New independent module, not a capstone.
All source obligations remain explicit. No sorry or custom axiom is used.
-/
namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

noncomputable def shell (D : CH.Digraph) (V : Finset ℕ) (R u : ℕ) : Finset ℕ :=
  ball D V u (R+1) \ ball D V u R

noncomputable def layer (D : CH.Digraph) (V : Finset ℕ) (R u : ℕ) : Finset ℕ :=
  ball D V u R \ ball D V u (R-1)

noncomputable def column (D : CH.Digraph) (V : Finset ℕ) (R u h : ℕ) : Finset ℕ :=
  (layer D V R u).filter (fun a => D a h = true)

theorem shell_subset {D : CH.Digraph} {V : Finset ℕ} {R u : ℕ} :
    shell D V R u ⊆ V :=
  fun _ h => ball_subset (Finset.mem_sdiff.mp h).1

theorem layer_subset {D : CH.Digraph} {V : Finset ℕ} {R u : ℕ} :
    layer D V R u ⊆ V :=
  fun _ h => ball_subset (Finset.mem_sdiff.mp h).1

theorem shell_walk {D : CH.Digraph} {V : Finset ℕ} {R u h : ℕ}
    (hh : h ∈ shell D V R u) : Walk D V u h (R+1) := by
  obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hh
  obtain ⟨hhV,l,hl,wl⟩ := mem_ball.mp hin
  have hn : ¬ l ≤ R := fun hm => hout (mem_ball.mpr ⟨hhV,l,hm,wl⟩)
  have he : l=R+1 := by omega
  subst l
  exact wl

/-- One actual reverse-walk penultimate transports the entire column.
The same v and the same h-to-v walk work for every a in the root ball. -/
theorem column_transport {D : CH.Digraph} {V : Finset ℕ} {R q u h v a : ℕ}
    (hf : QFree D V q) (hq : 2*R+1≤q)
    (hu : u ∈ V) (hh : h ∈ V)
    (whv : Walk D V h v R) (hvu : D v u = true)
    (ha : a ∈ ball D V u R) (hah : D a h = true) :
    a ∈ shell D V R v := by
  obtain ⟨haV,l,hl,wa⟩ := mem_ball.mp ha
  apply Finset.mem_sdiff.mpr
  constructor
  · exact mem_ball.mpr ⟨haV,l+1,by omega,.step hu hvu wa⟩
  · intro hb
    obtain ⟨_,j,hj,wb⟩ := mem_ball.mp hb
    exact hf a ((R+1)+j) (by omega) (by omega)
      ((Walk.step hh hah whv).append wb)

/-- Every column has fewer than m parents when the actual shells have m
vertices, the preceding layers have m+1 vertices, shells are symmetric,
and every actual preceding-layer row has a next-shell head. -/
theorem two_pass_column_bound {D : CH.Digraph} {V : Finset ℕ} {R q m u h : ℕ}
    (hf : QFree D V q) (hR : 1≤R) (hq : 2*R+1≤q)
    (hS : ∀ x ∈ V, (layer D V R x).card=m+1)
    (hT : ∀ x ∈ V, (shell D V R x).card=m)
    (hsym : ∀ x ∈ V, ∀ y ∈ shell D V R x, x ∈ shell D V R y)
    (hrow : ∀ x ∈ V, ∀ a ∈ layer D V R x,
      ∃ z ∈ shell D V R x, D a z = true)
    (hu : u ∈ V) (hh : h ∈ shell D V R u) :
    (column D V R u h).card < m := by
  by_contra! hlarge
  have hhV : h ∈ V := shell_subset hh
  have whu := shell_walk (hsym u hu h hh)
  obtain ⟨v,whv,_,hvu⟩ := whu.unsnoc
  have hv : v ∈ V := by
    rcases whv.end_mem_or with he|he
    · exact he ▸ hhV
    · exact he
  have hsub : column D V R u h ⊆ shell D V R v := by
    intro a ha
    obtain ⟨ha,hah⟩ := Finset.mem_filter.mp ha
    exact column_transport hf hq hu hhV whv hvu (Finset.mem_sdiff.mp ha).1 hah
  have heq : column D V R u h = shell D V R v :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hT v hv]; exact hlarge)
  have whv' : Walk D V h v ((R-1)+1) := by
    simpa only [Nat.sub_add_cancel hR] using whv
  obtain ⟨w,whw,_,hwv⟩ := whv'.unsnoc
  have hw : w ∈ V := by
    rcases whw.end_mem_or with he|he
    · exact he ▸ hhV
    · exact he
  have hnot : ¬ layer D V R v ⊆ shell D V R w := by
    intro hs
    have hc := Finset.card_le_card hs
    rw [hS v hv,hT w hw] at hc
    omega
  obtain ⟨a,ha,han⟩ := Finset.not_subset.mp hnot
  obtain ⟨z,hz,haz⟩ := hrow v hv a ha
  have hzc : z ∈ column D V R u h := heq ▸ hz
  have hzh : D z h = true := (Finset.mem_filter.mp hzc).2
  have wzw : Walk D V z w R := by
    simpa only [Nat.sub_add_cancel hR] using (Walk.step hhV hzh whw)
  exact han (column_transport hf hq hv (shell_subset hz) wzw hwv
    (Finset.mem_sdiff.mp ha).1 haz)

#print axioms column_transport
#print axioms two_pass_column_bound
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

noncomputable def holes (D : CH.Digraph) (V : Finset ℕ) (R u : ℕ) : ℕ :=
  ∑ a ∈ layer D V R u,
    (shell D V R u \ outN D (shell D V R u) a).card

/-- The physical row and column missing-cell counts are the same tensor. -/
theorem holes_transpose {D : CH.Digraph} {V : Finset ℕ} {R u : ℕ} :
    holes D V R u = ∑ h ∈ shell D V R u,
      (layer D V R u \ column D V R u h).card := by
  have row (a : ℕ) :
      shell D V R u \ outN D (shell D V R u) a =
        (shell D V R u).filter (fun h => D a h ≠ true) := by
    ext h
    simp [outN]; tauto
  have col (h : ℕ) :
      layer D V R u \ column D V R u h =
        (layer D V R u).filter (fun a => D a h ≠ true) := by
    ext a
    simp [column]; tauto
  simp only [holes,row,col,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- The checked two-pass mechanism forces at least two physical holes in
EVERY actual column. -/
theorem two_pass_holes_lower {D : CH.Digraph} {V : Finset ℕ} {R q m u : ℕ}
    (hf : QFree D V q) (hR : 1≤R) (hq : 2*R+1≤q)
    (hS : ∀ x ∈ V, (layer D V R x).card=m+1)
    (hT : ∀ x ∈ V, (shell D V R x).card=m)
    (hsym : ∀ x ∈ V, ∀ y ∈ shell D V R x, x ∈ shell D V R y)
    (hrow : ∀ x ∈ V, ∀ a ∈ layer D V R x,
      ∃ z ∈ shell D V R x, D a z = true)
    (hu : u ∈ V) : 2*m ≤ holes D V R u := by
  rw [holes_transpose]
  have hc (h) (hh : h ∈ shell D V R u) :
      2 ≤ (layer D V R u \ column D V R u h).card := by
    have hb := two_pass_column_bound hf hR hq hS hT hsym hrow hu hh
    have hs : column D V R u h ⊆ layer D V R u := Finset.filter_subset _ _
    have he := Finset.card_sdiff_add_card_eq_card hs
    rw [hS u hu] at he
    omega
  have hsum := Finset.sum_le_sum hc
  simpa [hT u hu,Nat.mul_comm] using hsum

/-- A complete conditional flat contradiction. The no-zero-row supplier
remains an explicit graph premise, not an axiom or hidden proof hole. -/
theorem two_pass_flat_false {D : CH.Digraph} {V : Finset ℕ} {R q m u : ℕ}
    (hf : QFree D V q) (hR : 1≤R) (hq : 2*R+1≤q) (hm : 2≤m)
    (hS : ∀ x ∈ V, (layer D V R x).card=m+1)
    (hT : ∀ x ∈ V, (shell D V R x).card=m)
    (hsym : ∀ x ∈ V, ∀ y ∈ shell D V R x, x ∈ shell D V R y)
    (hrow : ∀ x ∈ V, ∀ a ∈ layer D V R x,
      ∃ z ∈ shell D V R x, D a z = true)
    (hu : u ∈ V) (hholes : holes D V R u ≤ m+1) : False := by
  have hh := two_pass_holes_lower hf hR hq hS hT hsym hrow hu
  omega

/-- Literal complementary reach, not an abstract Boolean oracle, supplies
symmetry of the actual exact-distance shell. -/
theorem shell_symm_of_complement {D : CH.Digraph} {V : Finset ℕ} {R : ℕ}
    (hc : ∀ x ∈ V, ∀ y ∈ V, x≠y →
      (y ∈ ball D V x R ↔ x ∉ ball D V y (R+1))) :
    ∀ x ∈ V, ∀ y ∈ shell D V R x, x ∈ shell D V R y := by
  intro x hx y hy
  obtain ⟨hy1,hy0⟩ := Finset.mem_sdiff.mp hy
  have hyV : y ∈ V := ball_subset hy1
  have hne : x≠y := by
    intro he
    subst y
    exact hy0 (self_mem_ball hx)
  apply Finset.mem_sdiff.mpr
  constructor
  · by_contra hn
    exact hy0 ((hc x hx y hyV hne).mpr hn)
  · intro hb
    exact ((hc y hyV x hx hne.symm).mp hb) hy1

#print axioms holes_transpose
#print axioms two_pass_holes_lower
#print axioms two_pass_flat_false
#print axioms shell_symm_of_complement
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- Equal actual closed balls have equal roots at the sharp k+1 cutoff. -/
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

/-- A first-exit trap retaining the actual target arc at every exit. -/
theorem target_traps_short_ball {D : CH.Digraph} {V U Z : Finset ℕ} {R y h : ℕ}
    (hR : 1≤R) (hy : y ∈ Z) (hh : h ∈ V)
    (hstep : ∀ v ∈ Z, ∀ z ∈ V, D v z = true → z ∈ U)
    (hgood : ∀ z ∈ U, z ∉ Z → D z h = true)
    (hbad : h ∉ ball D V y R) : ball D V y (R-1) ⊆ Z := by
  have aux : ∀ l z, Walk D V y z l → l<R → z ∈ Z := by
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
  exact aux l z wl (by omega)

/-- A completely missing prefix row removes the dangerous early exit.
All bad-origin balls are trapped in the same literal punctured inner set. -/
theorem zero_row_bad_ball {D : CH.Digraph} {V : Finset ℕ} {R q u a h y : ℕ}
    (hf : QFree D V q) (hR : 1≤R) (hq : R+1≤q) (hu : u ∈ V)
    (ha : a ∈ layer D V R u)
    (hzero : ∀ z ∈ shell D V R u, ¬ D a z = true)
    (hh : h ∈ shell D V R u)
    (hgood : ∀ z ∈ layer D V R u, z≠a → D z h = true)
    (hy : y ∈ (ball D V u R).erase u) (hbad : h ∉ ball D V y R) :
    ball D V y (R-1) ⊆ insert a ((ball D V u (R-1)).erase u) := by
  let U := (ball D V u R).erase u
  let Z := insert a ((ball D V u (R-1)).erase u)
  have haB : a ∈ ball D V u R := (Finset.mem_sdiff.mp ha).1
  have good (z) (hz : z ∈ U) (hn : z ∉ Z) : D z h = true := by
    have hzS : z ∈ layer D V R u := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_of_mem_erase hz,?_⟩
      intro hi
      exact hn (Finset.mem_insert.mpr (Or.inr
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,hi⟩)))
    have hza : z≠a := fun he => hn (Finset.mem_insert.mpr (Or.inl he))
    exact hgood z hzS hza
  have step (x) (hx : x ∈ Z) (z) (hz : z ∈ V) (hxz : D x z = true) : z ∈ U := by
    have hxB : x ∈ ball D V u R := by
      rcases Finset.mem_insert.mp hx with rfl|hi
      · exact haB
      · exact ball_mono_radius (by omega) (Finset.mem_of_mem_erase hi)
    have hzB : z ∈ ball D V u R := by
      rcases Finset.mem_insert.mp hx with rfl|hi
      · have hz1 := ball_step haB hz hxz
        by_contra hn
        exact hzero z (Finset.mem_sdiff.mpr ⟨hz1,hn⟩) hxz
      · have hb := ball_step (Finset.mem_of_mem_erase hi) hz hxz
        simpa only [Nat.sub_add_cancel hR] using hb
    apply Finset.mem_erase.mpr
    refine ⟨?_,hzB⟩
    intro he
    subst z
    exact no_back_arc hf hu hxB hq hxz
  have hyZ : y ∈ Z := by
    by_contra hn
    exact hbad (mem_ball.mpr ⟨shell_subset hh,1,by omega,
      .step (shell_subset hh) (good y hy hn) (.refl h)⟩)
  exact target_traps_short_ball hR hyZ (shell_subset hh) step good hbad

#print axioms ball_root_injective_short
#print axioms target_traps_short_ball
#print axioms zero_row_bad_ball
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- The actual flat sizes and physical cell budget discharge the
no-zero-row supplier. No row-safety or shared-origin oracle is assumed. -/
theorem no_zero_row_of_flat_counts {D : CH.Digraph} {V : Finset ℕ} {R q s b N : ℕ}
    (hf : QFree D V q) (hR : 2≤R) (hq : 2*R+1≤q) (hnear : R+3≤q)
    (hs : 5≤s)
    (hinner : ∀ x ∈ V, (ball D V x (R-1)).card=b)
    (houter : ∀ x ∈ V, (ball D V x (R+1)).card=N)
    (hK : ∀ x ∈ V, (V \ (ball D V x R).erase x).card=N)
    (hS : ∀ x ∈ V, (layer D V R x).card=s)
    (hT : ∀ x ∈ V, (shell D V R x).card=s-1)
    (hholes : ∀ x ∈ V, holes D V R x≤s) :
    ∀ u ∈ V, ∀ a ∈ layer D V R u,
      ∃ h ∈ shell D V R u, D a h = true := by
  intro u hu a ha
  by_contra! hzero
  let S := layer D V R u
  let T := shell D V R u
  let U := (ball D V u R).erase u
  let Z := insert a ((ball D V u (R-1)).erase u)
  let f := fun h => (S \ column D V R u h).card
  have ham (h) (hh : h ∈ T) : a ∈ S \ column D V R u h := by
    apply Finset.mem_sdiff.mpr
    refine ⟨ha,?_⟩
    intro hc
    exact hzero h hh (Finset.mem_filter.mp hc).2
  have fone (h) (hh : h ∈ T) : 1≤f h := by
    have hp := Finset.card_pos.mpr ⟨a,ham h hh⟩
    exact hp
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
  have hbudget := hholes u hu
  rw [holes_transpose] at hbudget
  change (∑ h ∈ T, f h)≤s at hbudget
  have hTcard : T.card=s-1 := hT u hu
  have hBcard : B.card≤1 := by omega
  let C := T \ B
  have hCsub : C ⊆ T := Finset.sdiff_subset
  have hsplit := Finset.card_sdiff_add_card_eq_card hBS
  have hCcard : 3≤C.card := by dsimp [C]; omega
  have hg (h) (hh : h ∈ C) : ∀ z ∈ S, z≠a → D z h = true := by
    have hhT := hCsub hh
    have hnB : h ∉ B := (Finset.mem_sdiff.mp hh).2
    have hn : ¬ 2≤f h := fun hn => hnB (Finset.mem_filter.mpr ⟨hhT,hn⟩)
    have h1 : (S \ column D V R u h).card=1 := by
      have hp := fone h hhT
      change f h=1
      omega
    have he : ({a} : Finset ℕ)=S \ column D V R u h :=
      Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (ham h hhT))
        (by rw [h1]; simp)
    intro z hz hza
    by_contra hn
    have hzm : z ∈ S \ column D V R u h :=
      Finset.mem_sdiff.mpr ⟨hz,fun hc => hn (Finset.mem_filter.mp hc).2⟩
    rw [← he] at hzm
    exact hza (Finset.mem_singleton.mp hzm)
  have hZcard : Z.card=b := by
    have han : a ∉ (ball D V u (R-1)).erase u :=
      fun hh => (Finset.mem_sdiff.mp ha).2 (Finset.mem_of_mem_erase hh)
    have hp : 0<b := by
      rw [← hinner u hu]
      exact Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    dsimp [Z]
    rw [Finset.card_insert_of_notMem han,
      Finset.card_erase_of_mem (self_mem_ball hu),hinner u hu]
    omega
  let Y := U.filter (fun y => ∃ h ∈ C, h ∉ ball D V y R)
  have hYball (y) (hy : y ∈ Y) : ball D V y (R-1)=Z := by
    obtain ⟨hyU,h,hh,hbad⟩ := Finset.mem_filter.mp hy
    have hyV : y ∈ V := ball_subset (Finset.mem_of_mem_erase hyU)
    have hb := zero_row_bad_ball hf (by omega : 1≤R) (by omega) hu ha hzero
      (hCsub hh) (hg h hh) hyU hbad
    exact Finset.eq_of_subset_of_card_le hb (by rw [hZcard,hinner y hyV])
  have hYcard : Y.card≤1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    have hyV : y ∈ V := ball_subset
      (Finset.mem_of_mem_erase (Finset.mem_filter.mp hy).1)
    have hzV : z ∈ V := ball_subset
      (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1)
    exact ball_root_injective_short hf (by omega) hyV hzV
      ((hYball y hy).trans (hYball z hz).symm)
  let K := (V \ U) ∪ Y
  have hKsize : K.card≤N+1 := by
    have hh := Finset.card_union_le (V \ U) Y
    have hk : (V \ U).card=N := hK u hu
    dsimp [K]
    omega
  have hballs (h) (hh : h ∈ C) : ball D V h (R+1) ⊆ K := by
    intro z hz
    have hzV : z ∈ V := ball_subset hz
    have hhT := hCsub hh
    have hhV : h ∈ V := shell_subset hhT
    by_cases hzU : z ∈ U
    · apply Finset.mem_union.mpr
      right
      by_contra hn
      have hforw : h ∈ ball D V z R := by
        by_contra hb
        exact hn (Finset.mem_filter.mpr ⟨hzU,h,hh,hb⟩)
      have hne : z≠h := by
        intro he
        subst z
        exact (Finset.mem_sdiff.mp hhT).2 (Finset.mem_of_mem_erase hzU)
      have hc := reach_tensor_return_capacity hf (by omega : R+(R+1)≤q) hzV hhV
      simp [reachTensor,hforw,hz,hne] at hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hzV,hzU⟩))
  obtain ⟨C3,hC3,h3⟩ := Finset.exists_subset_card_eq hCcard
  have hCV : C3 ⊆ V := fun _ hh => shell_subset (hCsub (hC3 hh))
  have hCK : C3 ⊆ K := fun h hh =>
    hballs h (hC3 hh) (self_mem_ball (hCV hh))
  have hmiss (h) (hh : h ∈ C3) : (K \ ball D V h (R+1)).card≤1 := by
    have hc := Finset.card_sdiff_add_card_eq_card (hballs h (hC3 hh))
    rw [houter h (hCV hh)] at hc
    omega
  exact near_full_container_false hf (by omega : (R+1)+2≤q) hCV hCK
    (fun h hh => hballs h (hC3 hh)) hmiss (by omega) (by omega)

#print axioms no_zero_row_of_flat_counts
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenThirdStrip
open Classical

/-- The complete actual flat packet at the third-strip upper endpoint is
impossible. The physical hole budget and no-zero-row supplier are derived,
not assumed. Source-wide reduction TO these three ball equalities and the
complement identity remains a separate formalization obligation. -/
theorem third_strip_flat_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a)
    (hf : QFree D V (2*a+7))
    (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+7)*(a+6))
    (hinner : ∀ v ∈ V, (ball D V v (a+2)).card=(a+6)*(a+2)+1)
    (hmid : ∀ v ∈ V, (ball D V v (a+3)).card=(a+6)*(a+3)+1)
    (houter : ∀ v ∈ V, (ball D V v (a+4)).card=(a+6)*(a+4))
    (hcomp : ∀ x ∈ V, ∀ y ∈ V, x≠y →
      (y ∈ ball D V x (a+3) ↔ x ∉ ball D V y (a+4))) : False := by
  have hS (x) (hx : x ∈ V) : (layer D V (a+3) x).card=a+6 := by
    have he := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=x) (by omega : a+2≤a+3))
    rw [hinner x hx,hmid x hx] at he
    change (layer D V (a+3) x).card + ((a+6)*(a+2)+1) =
      (a+6)*(a+3)+1 at he
    nlinarith
  have hT (x) (hx : x ∈ V) : (shell D V (a+3) x).card=a+5 := by
    have he := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=x) (by omega : a+3≤a+4))
    rw [hmid x hx,houter x hx] at he
    change (shell D V (a+3) x).card + ((a+6)*(a+3)+1) =
      (a+6)*(a+4) at he
    nlinarith
  have hU (x) (hx : x ∈ V) : ((ball D V x (a+3)).erase x).card=(a+6)*(a+3) := by
    rw [Finset.card_erase_of_mem (self_mem_ball hx),hmid x hx]
    omega
  have hK (x) (hx : x ∈ V) :
      (V \ (ball D V x (a+3)).erase x).card=(a+6)*(a+4) := by
    have hsub : (ball D V x (a+3)).erase x ⊆ V :=
      (Finset.erase_subset _ _).trans ball_subset
    have he := Finset.card_sdiff_add_card_eq_card hsub
    rw [hU x hx,hn] at he
    nlinarith
  have hholes (x) (hx : x ∈ V) : holes D V (a+3) x≤a+6 := by
    have hret : ∀ v ∈ (ball D V x (a+3)).erase x,
        1≤(outN D ((ball D V x (a+3)).erase x) v).card := by
      intro v hv
      have hvV : v ∈ V := ball_subset (Finset.mem_of_mem_erase hv)
      have hsub := outN_prefix_loss hf hx (by omega : (a+3)+1≤2*a+7) hv
      have hc := (hm v hvV).trans
        ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
      have he : a+3+1=a+4 := by omega
      rw [he] at hc
      have ht := hT x hx
      change (ball D V x (a+4) \ ball D V x (a+3)).card=a+5 at ht
      omega
    have hp := PrefixTensor.same_degree_missing_capacity (s:=a+6)
      (L:=(2*a+7)*(a+6)) (k:=a+2) hf hm hx (by omega)
      (fun F W hfw hmw hnw => order_to_top (a:=a) hfw hmw hnw)
      (by omega) hret
    change (2*a+7)*(a+6)+holes D V (a+3) x ≤
      ((ball D V x (a+3)).erase x).card +
        (layer D V (a+3) x).card*(shell D V (a+3) x).card at hp
    rw [hU x hx,hS x hx,hT x hx] at hp
    nlinarith
  have hrow := no_zero_row_of_flat_counts (R:=a+3) (s:=a+6)
    (b:=(a+6)*(a+2)+1) (N:=(a+6)*(a+4)) hf (by omega) (by omega) (by omega)
    (by omega) hinner houter hK hS (by simpa using hT) hholes
  obtain ⟨u,hu⟩ := hne
  exact two_pass_flat_false (R:=a+3) (m:=a+5) hf (by omega) (by omega)
    (by omega) hS hT (shell_symm_of_complement hcomp) hrow hu (hholes u hu)

#print axioms third_strip_flat_false
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenThirdStrip
open Classical

/-- The current-degree physical tensor budget, with retained heads supplied
from the strict next-layer bound on the ORIGINAL graph. -/
theorem current_prefix_cells {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hu : u ∈ V) (hk : k+2≤2*a+7)
    (ht : (shell D V (k+1) u).card<a+6) :
    (2*a+7)*(a+6)+holes D V (k+1) u ≤
      ((ball D V u (k+1)).erase u).card+
        (layer D V (k+1) u).card*(shell D V (k+1) u).card := by
  have hret : ∀ v ∈ (ball D V u (k+1)).erase u,
      1≤(outN D ((ball D V u (k+1)).erase u) v).card := by
    intro v hv
    have hvV := ball_subset (Finset.mem_of_mem_erase hv)
    have hsub := outN_prefix_loss hf hu (by omega : (k+1)+1≤2*a+7) hv
    have hc := (hm v hvV).trans
      ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    change (ball D V u ((k+1)+1) \ ball D V u (k+1)).card<a+6 at ht
    omega
  have hp := PrefixTensor.same_degree_missing_capacity (s:=a+6)
    (L:=(2*a+7)*(a+6)) (k:=k) hf hm hu (by omega)
    (fun F W hfw hmw hnw => order_to_top (a:=a) hfw hmw hnw) hk hret
  simpa only [holes,layer,shell,Nat.add_sub_cancel,Nat.add_assoc] using hp

/-- Bounded arc witnesses lift an entire actual walk, charging every edge.
Both lower and upper lengths are retained, including the empty walk. -/
theorem lift_walk_bounded {D E : CH.Digraph} {V C : Finset ℕ} {e x y l : ℕ}
    (hedge : ∀ x ∈ C, ∀ y ∈ C, E x y = true →
      ∃ j, 1≤j ∧ j≤e ∧ Walk D V x y j)
    (hx : x ∈ C) (w : Walk E C x y l) :
    ∃ j, l≤j ∧ j≤e*l ∧ Walk D V x y j := by
  revert hx
  induction w with
  | refl x =>
    intro _
    exact ⟨0,by omega,by simp,.refl x⟩
  | @step x y z l hy hxy wy ih =>
    intro hx
    obtain ⟨j,hj,hje,wj⟩ := hedge x hx y hy hxy
    obtain ⟨m,hm,hme,wm⟩ := ih hy
    refine ⟨j+m,by omega,?_,wj.append wm⟩
    nlinarith

theorem qfree_of_bounded_arc_lift {D E : CH.Digraph} {V C : Finset ℕ} {q r e : ℕ}
    (hf : QFree D V q) (hbudget : e*r≤q)
    (hedge : ∀ x ∈ C, ∀ y ∈ C, E x y = true →
      ∃ j, 1≤j ∧ j≤e ∧ Walk D V x y j) : QFree E C r := by
  intro x l hl hr wl
  obtain ⟨n,he⟩ : ∃ n, l=n+1 := ⟨l-1,by omega⟩
  subst l
  obtain ⟨_,_,hx,_⟩ := wl.unsnoc
  obtain ⟨j,hj,hje,wj⟩ := lift_walk_bounded hedge hx wl
  exact hf x j (by omega) (hje.trans ((Nat.mul_le_mul_left e hr).trans hbudget)) wj

/-- Two omitted labels force every bank-to-bank k-reach to use at most
two original edges. Three distinct actual final predecessors pay the proof. -/
theorem omission_two_short {D : CH.Digraph} {V K C : Finset ℕ} {q k x y : ℕ}
    (hf : QFree D V q) (hk : k+3≤q) (hCV : C ⊆ V)
    (hballs : ∀ c ∈ C, ball D V c k ⊆ K)
    (hmiss : ∀ c ∈ C, (K \ ball D V c k).card≤2)
    (hx : x ∈ C) (hy : y ∈ C) (hxy : y ∈ ball D V x k) :
    y ∈ ball D V x 2 := by
  obtain ⟨hyV,m,hm,wm⟩ := mem_ball.mp hxy
  by_cases hsmall : m≤2
  · exact mem_ball.mpr ⟨hyV,m,hsmall,wm⟩
  obtain ⟨l,he⟩ : ∃ l, m=l+3 := ⟨m-3,by omega⟩
  subst m
  obtain ⟨v,wv,_,hvy⟩ := wm.unsnoc
  obtain ⟨z,wz,hvV,hzv⟩ := wv.unsnoc
  obtain ⟨w,ww,hzV,hwz⟩ := wz.unsnoc
  have hwV : w ∈ V := by
    rcases ww.end_mem_or with he|he
    · exact he ▸ hCV hx
    · exact he
  have hwK : w ∈ K := hballs x hx (mem_ball.mpr ⟨hwV,l,by omega,ww⟩)
  have hzK : z ∈ K := hballs x hx (mem_ball.mpr ⟨hzV,l+1,by omega,wz⟩)
  have hvK : v ∈ K := hballs x hx (mem_ball.mpr ⟨hvV,l+2,by omega,wv⟩)
  have hwn : w ∉ ball D V y k := by
    intro hb
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hb
    exact hf y (j+3) (by omega) (by omega)
      (wj.append (.step hzV hwz (.step hvV hzv (.step hyV hvy (.refl y)))))
  have hzn : z ∉ ball D V y k := by
    intro hb
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hb
    exact hf y (j+2) (by omega) (by omega)
      (wj.append (.step hvV hzv (.step hyV hvy (.refl y))))
  have hvn : v ∉ ball D V y k := by
    intro hb
    obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hb
    exact hf y (j+1) (by omega) (by omega) (wj.snoc hyV hvy)
  have hwzne : w≠z := by
    intro he
    subst z
    exact loopfree hf (by omega) hwV hwz
  have hzvne : z≠v := by
    intro he
    subst v
    exact loopfree hf (by omega) hzV hzv
  have hwvne : w≠v := by
    intro he
    subst v
    exact hf w 2 (by omega) (by omega) (.step hzV hwz (.step hwV hzv (.refl w)))
  have hsub : ({w,z,v} : Finset ℕ) ⊆ K \ ball D V y k := by
    intro b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl
    · exact Finset.mem_sdiff.mpr ⟨hwK,hwn⟩
    · exact Finset.mem_sdiff.mpr ⟨hzK,hzn⟩
    · exact Finset.mem_sdiff.mpr ⟨hvK,hvn⟩
  have hc := Finset.card_le_card hsub
  have hthree : ({w,z,v} : Finset ℕ).card=3 := by simp [hwzne,hwvne,hzvne]
  rw [hthree] at hc
  have hh := hmiss y hy
  omega

#print axioms current_prefix_cells
#print axioms lift_walk_bounded
#print axioms qfree_of_bounded_arc_lift
#print axioms omission_two_short
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

noncomputable def shortRelation (D : CH.Digraph) (V : Finset ℕ) (k : ℕ) : CH.Digraph :=
  fun x y => decide (x≠y ∧ y ∈ ball D V x k)

theorem omission_two_relation_qfree {D : CH.Digraph} {V K C : Finset ℕ} {q k r : ℕ}
    (hf : QFree D V q) (hk : k+3≤q) (hb : 2*r≤q) (hCV : C ⊆ V)
    (hballs : ∀ c ∈ C, ball D V c k ⊆ K)
    (hmiss : ∀ c ∈ C, (K \ ball D V c k).card≤2) :
    QFree (shortRelation D V k) C r := by
  apply qfree_of_bounded_arc_lift (e:=2) hf hb
  intro x hx y hy he
  have hh : x≠y ∧ y ∈ ball D V x k := by simpa [shortRelation] using he
  have hs := omission_two_short hf hk hCV hballs hmiss hx hy hh.2
  obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hs
  have hjp : 1≤j := by
    by_contra! hn
    have he : j=0 := by omega
    subst j
    cases wj
    exact hh.1 rfl
  exact ⟨j,hjp,hj,wj⟩

/-- Four roots with at most two omissions in ONE actual container are
impossible once the compressed four-cycle budget is paid. -/
theorem omission_two_four_false {D : CH.Digraph} {V K C : Finset ℕ} {q k : ℕ}
    (hf : QFree D V q) (hk : k+3≤q) (hq : 8≤q)
    (hCV : C ⊆ V) (hCK : C ⊆ K) (hC : C.card=4)
    (hballs : ∀ c ∈ C, ball D V c k ⊆ K)
    (hmiss : ∀ c ∈ C, (K \ ball D V c k).card≤2) : False := by
  have hE := omission_two_relation_qfree (r:=4) hf hk (by omega) hCV hballs hmiss
  obtain ⟨x,hx,hsink⟩ := exists_sink hE
    (Finset.card_pos.mp (by omega : 0<C.card)) (by omega)
  have hsub : C ⊆ insert x (K \ ball D V x k) := by
    intro y hy
    by_cases he : y=x
    · exact Finset.mem_insert.mpr (Or.inl he)
    · apply Finset.mem_insert.mpr
      right
      refine Finset.mem_sdiff.mpr ⟨hCK hy,?_⟩
      intro hb
      exact hsink y hy (by simp [shortRelation,Ne.symm he,hb])
  have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hm := hmiss x hx
  omega

/-- Six roots with at most two omissions violate the actual two-direction
capacity after the same-path compression. -/
theorem omission_two_six_false {D : CH.Digraph} {V K C : Finset ℕ} {q k : ℕ}
    (hf : QFree D V q) (hk : k+3≤q) (hq : 4≤q)
    (hCV : C ⊆ V) (hCK : C ⊆ K) (hC : C.card=6)
    (hballs : ∀ c ∈ C, ball D V c k ⊆ K)
    (hmiss : ∀ c ∈ C, (K \ ball D V c k).card≤2) : False := by
  let E := shortRelation D V k
  have hE : QFree E C 2 :=
    omission_two_relation_qfree hf hk (by omega) hCV hballs hmiss
  have hB (x) (hx : x ∈ C) : 4≤(ball E C x 1).card := by
    let F := C.filter (fun y => y ∈ ball D V x k)
    have hFC : F ⊆ C := Finset.filter_subset _ _
    have hsub : C \ F ⊆ K \ ball D V x k := by
      intro y hy
      obtain ⟨hyC,hyn⟩ := Finset.mem_sdiff.mp hy
      exact Finset.mem_sdiff.mpr ⟨hCK hyC,fun hb =>
        hyn (Finset.mem_filter.mpr ⟨hyC,hb⟩)⟩
    have hmissC := (Finset.card_le_card hsub).trans (hmiss x hx)
    have he := Finset.card_sdiff_add_card_eq_card hFC
    have hFcard : 4≤F.card := by omega
    have hFB : F ⊆ ball E C x 1 := by
      intro y hy
      obtain ⟨hyC,hyB⟩ := Finset.mem_filter.mp hy
      by_cases he : y=x
      · subst y
        exact self_mem_ball hx
      · exact mem_ball.mpr ⟨hyC,1,le_rfl,
          .step hyC (by simp [E,shortRelation,Ne.symm he,hyB]) (.refl y)⟩
    exact hFcard.trans (Finset.card_le_card hFB)
  have hh := card_ge_of_two_balls hE (by omega : 1+1≤2) hB hB
    (Finset.card_pos.mp (by omega : 0<C.card))
  omega

#print axioms omission_two_relation_qfree
#print axioms omission_two_four_false
#print axioms omission_two_six_false
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

noncomputable def fullColumns (D : CH.Digraph) (V : Finset ℕ) (R u : ℕ) : Finset ℕ :=
  (shell D V R u).filter (fun h => ∀ v ∈ layer D V R u, D v h = true)

/-- Every nonfull physical column consumes an actual missing cell. -/
theorem full_columns_bound {D : CH.Digraph} {V : Finset ℕ} {R u : ℕ} :
    (shell D V R u).card ≤ (fullColumns D V R u).card+holes D V R u := by
  let T := shell D V R u
  let S := layer D V R u
  let C := fullColumns D V R u
  let miss := fun v => T \ outN D T v
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have he := Finset.card_sdiff_add_card_eq_card hCT
  have hsub : T \ C ⊆ S.biUnion miss := by
    intro h hh
    obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp hh
    have hfail : ¬ ∀ v ∈ S, D v h = true :=
      fun hfull => hn (Finset.mem_filter.mpr ⟨ht,hfull⟩)
    push_neg at hfail
    obtain ⟨v,hv,hnv⟩ := hfail
    exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_sdiff.mpr
      ⟨ht,fun hed => hnv (mem_outN.mp hed).2⟩⟩
  have hsum := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  change (T \ C).card≤holes D V R u at hsum
  change T.card≤C.card+holes D V R u
  omega

/-- Actual full columns share a complementary-radius container once the
same punctured-prefix hitter is paid. -/
theorem full_bank_avoids {D : CH.Digraph} {V : Finset ℕ} {u k L q : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : (k+1)+L≤q)
    (hsize : ∀ y ∈ (ball D V u (k+1)).erase u,
      ((ball D V u k).erase u).card < (ball D V y k).card) :
    ∀ h ∈ fullColumns D V (k+1) u,
      ball D V h L ⊆ V \ (ball D V u (k+1)).erase u := by
  intro h hh y hy
  have hyV : y ∈ V := ball_subset hy
  obtain ⟨hhT,hfull⟩ := Finset.mem_filter.mp hh
  have hhV : h ∈ V := shell_subset hhT
  apply Finset.mem_sdiff.mpr
  refine ⟨hyV,?_⟩
  intro hyU
  obtain ⟨z,hz,hzy⟩ := PrefixTensor.hits_layer hf hu (by omega) hyU (hsize y hyU)
  have hzS : z ∈ layer D V (k+1) u := by
    simpa only [layer,Nat.add_sub_cancel] using hz
  have hforw := ball_step hzy hhV (hfull z hzS)
  have hne : y≠h := by
    intro he
    subst y
    exact (Finset.mem_sdiff.mp hhT).2 (Finset.mem_of_mem_erase hyU)
  have hc := reach_tensor_return_capacity hf hk hyV hhV
  simp [reachTensor,hforw,hy,hne] at hc

/-- Bad origins for an actual full column have the SAME punctured-inner
container. This permits one shared exceptional origin in the flat adapter. -/
theorem full_column_bad_ball {D : CH.Digraph} {V : Finset ℕ} {u k q h y : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : k+1≤q)
    (hh : h ∈ fullColumns D V (k+1) u)
    (hy : y ∈ (ball D V u (k+1)).erase u)
    (hbad : h ∉ ball D V y (k+1)) :
    ball D V y k ⊆ (ball D V u k).erase u := by
  let U := (ball D V u (k+1)).erase u
  let Z := (ball D V u k).erase u
  obtain ⟨hhT,hfull⟩ := Finset.mem_filter.mp hh
  have hhV : h ∈ V := shell_subset hhT
  have good (z) (hz : z ∈ U) (hn : z ∉ Z) : D z h = true := by
    have hzS : z ∈ layer D V (k+1) u := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_of_mem_erase hz,?_⟩
      simpa only [Nat.add_sub_cancel] using
        (fun hi => hn (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,hi⟩))
    exact hfull z hzS
  have step (x) (hx : x ∈ Z) (z) (hz : z ∈ V) (hxz : D x z = true) : z ∈ U :=
    (mem_outN.mp (outN_prefix_erase_root hf hu hk (Finset.mem_of_mem_erase hx)
      (mem_outN.mpr ⟨hz,hxz⟩))).1
  have hyZ : y ∈ Z := by
    by_contra hn
    exact hbad (mem_ball.mpr ⟨hhV,1,by omega,.step hhV (good y hy hn) (.refl h)⟩)
  have htrap := target_traps_short_ball (R:=k+1) (by omega) hyZ hhV step good hbad
  simpa only [Nat.add_sub_cancel] using htrap

#print axioms full_columns_bound
#print axioms full_bank_avoids
#print axioms full_column_bad_ball
end LeanCH.BR.DotTwoPassShellTransport

namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenThirdStrip
open Classical

private theorem first_cell_saturation {a N c t H : ℕ}
    (hN : N+t+1=(a+6)*(a+3)) (hc : c+t+1≤2*(a+6)) (ht : t≤a+5)
    (hp : (2*a+7)*(a+6)+H≤N+c*t) : t=a+5 ∧ c=a+6 ∧ H=0 := by
  have hmul := Nat.mul_le_mul_right t hc
  have he : t=a+5 := by
    by_contra! hn
    have htl : t≤a+4 := by omega
    have hh : (0:ℤ)≤((a:ℤ)+5-t)*((a:ℤ)+4-t) :=
      mul_nonneg (by omega) (by omega)
    zify at hN hc ht hp hmul htl
    nlinarith
  subst t
  have hec : c=a+6 := by nlinarith
  subst c
  exact ⟨rfl,rfl,by nlinarith⟩

private theorem second_cell_saturation {a N c t f H : ℕ}
    (hN : N+2=(a+6)*(a+4)+f) (ht : t+f=a+4) (hc : c≤a+5+f)
    (hp : (2*a+7)*(a+6)+H≤N+c*t) : f=0 ∧ c=a+5 ∧ t=a+4 ∧ H=0 := by
  have hmul := Nat.mul_le_mul_right t hc
  have he : f=0 := by
    cases f with
    | zero => rfl
    | succ f => nlinarith [Nat.zero_le (f*f)]
  subst f
  have het : t=a+4 := by omega
  subst t
  have hec : c=a+5 := by nlinarith
  subst c
  exact ⟨rfl,rfl,rfl,by nlinarith⟩

/-- An actual zero-excess root saturates the first physical rectangle. -/
theorem zero_root_first_table {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+6≤(outN D V v).card)
    (hu : u ∈ V) (hz : (ball D V u (a+3)).card=(a+6)*(a+3)) :
    (shell D V (a+2) u).card=a+5 ∧
    (layer D V (a+2) u).card=a+6 ∧ holes D V (a+2) u=0 ∧
    (ball D V u (a+1)).card=(a+6)*(a+1)+1 ∧
    ((ball D V u (a+2)).erase u).card=(a+6)*(a+2) := by
  let t := (shell D V (a+2) u).card
  let c := (layer D V (a+2) u).card
  let N := ((ball D V u (a+2)).erase u).card
  have htadd : t+(ball D V u (a+2)).card=(a+6)*(a+3) := by
    have he := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by omega : a+2≤a+3))
    simpa only [t, shell, show a+2+1=a+3 by omega, hz] using he
  have hcadd : c+(ball D V u (a+1)).card=(ball D V u (a+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hNadd : N+1=(ball D V u (a+2)).card := by
    have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+2))
    have hp : 0<(ball D V u (a+2)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    dsimp [N]
    omega
  have hlow := inner_growth hf hm hu (a+2) (by omega) (by omega)
  have hold := inner_growth hf hm hu (a+1) (by omega) (by omega)
  have ht : t≤a+5 := by nlinarith
  have hc : c+t+1≤2*(a+6) := by nlinarith
  have hN : N+t+1=(a+6)*(a+3) := by omega
  have hp := current_prefix_cells (k:=a+1) hf hm hu (by omega) (by change t<a+6; omega)
  change (2*a+7)*(a+6)+holes D V (a+2) u≤N+c*t at hp
  obtain ⟨htE,hcE,hH⟩ := first_cell_saturation hN hc ht hp
  refine ⟨htE,hcE,hH,?_,?_⟩ <;> nlinarith

/-- An equality enlarged ball saturates the second physical rectangle. -/
theorem R2_equality_table {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ x ∈ V, a+6≤(outN D V x).card)
    (hv : v ∈ V) (heq : (ball D V v (a+5)).card+3=(a+6)*(a+5)) :
    (ball D V v (a+4)).card+1=(a+6)*(a+4) ∧
    (shell D V (a+4) v).card=a+4 ∧
    (layer D V (a+4) v).card=a+5 ∧ holes D V (a+4) v=0 ∧
    (ball D V v (a+3)).card=(a+6)*(a+3) ∧
    ((ball D V v (a+4)).erase v).card+2=(a+6)*(a+4) := by
  let t := (shell D V (a+4) v).card
  let c := (layer D V (a+4) v).card
  let N := ((ball D V v (a+4)).erase v).card
  have hlow := radius_R1_growth hf hm hv
  obtain ⟨f,hfE⟩ := Nat.exists_eq_add_of_le hlow
  have htadd : t+(ball D V v (a+4)).card=(ball D V v (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hcadd : c+(ball D V v (a+3)).card=(ball D V v (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hNadd : N+1=(ball D V v (a+4)).card := by
    have he := Finset.card_erase_of_mem (self_mem_ball hv : v ∈ ball D V v (a+4))
    have hp : 0<(ball D V v (a+4)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    dsimp [N]
    omega
  have hr := radius_R_growth hf hm hv
  have htf : t+f=a+4 := by nlinarith
  have hcf : c≤a+5+f := by nlinarith
  have hNf : N+2=(a+6)*(a+4)+f := by omega
  have hp := current_prefix_cells (k:=a+3) hf hm hv (by omega) (by change t<a+6; omega)
  change (2*a+7)*(a+6)+holes D V (a+4) v≤N+c*t at hp
  obtain ⟨hf0,hcE,htE,hH⟩ := second_cell_saturation hNf htf hcf hp
  refine ⟨?_,htE,hcE,hH,?_,?_⟩ <;> nlinarith

#print axioms zero_root_first_table
#print axioms R2_equality_table
end LeanCH.BR.DotTwoPassShellTransport


namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenThirdStrip
open Classical

/-- The tight-R upper-order branch is impossible, by two actual saturated
rectangles and common-container compression. No flatness hypothesis is used. -/
theorem third_strip_zero_root_false {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ x ∈ V, a+6≤(outN D V x).card)
    (hn : V.card=(2*a+7)*(a+6)) (hu : u ∈ V)
    (hz : (ball D V u (a+3)).card=(a+6)*(a+3)) : False := by
  obtain ⟨ht,hc,hH,hprev,hU⟩ := zero_root_first_table hf hm hu hz
  let C := fullColumns D V (a+2) u
  let K := V \ (ball D V u (a+2)).erase u
  have hCV : C ⊆ V := fun _ hx => shell_subset (Finset.mem_filter.mp hx).1
  have hcard : 6≤C.card := by
    have hb := full_columns_bound (D:=D) (V:=V) (R:=a+2) (u:=u)
    change (shell D V (a+2) u).card≤C.card+holes D V (a+2) u at hb
    omega
  have hK : K.card=(a+6)*(a+5) := by
    have he := Finset.card_sdiff_add_card_eq_card
      ((Finset.erase_subset u (ball D V u (a+2))).trans ball_subset)
    change K.card+((ball D V u (a+2)).erase u).card=V.card at he
    nlinarith
  have hballs : ∀ h ∈ C, ball D V h (a+5) ⊆ K := by
    apply full_bank_avoids (k:=a+1) hf hu (by omega)
    intro y hy
    have he := Finset.card_erase_of_mem
      (self_mem_ball hu : u ∈ ball D V u (a+1))
    have hl := inner_growth hf hm (ball_subset (Finset.mem_of_mem_erase hy))
      (a+1) (by omega) (by omega)
    omega
  have hCK : C ⊆ K := fun h hh => hballs h hh (self_mem_ball (hCV hh))
  have heq : ∃ v ∈ C, (ball D V v (a+5)).card+3=(a+6)*(a+5) := by
    by_contra hnone
    push Not at hnone
    obtain ⟨C0,hsub,hcard0⟩ := Finset.exists_subset_card_eq hcard
    have hmiss (v) (hv : v ∈ C0) : (K \ ball D V v (a+5)).card≤2 := by
      have he := Finset.card_sdiff_add_card_eq_card (hballs v (hsub hv))
      have hl := radius_R2_growth hf hm (hCV (hsub hv))
      have hne := hnone v (hsub hv)
      omega
    exact omission_two_six_false hf (by omega) (by omega)
      (hsub.trans hCV) (hsub.trans hCK) hcard0
      (fun v hv => hballs v (hsub hv)) hmiss
  obtain ⟨v,hv,hev⟩ := heq
  have hvV := hCV hv
  obtain ⟨hR1,ht2,hc2,hH2,hR,hU2⟩ := R2_equality_table hf hm hvV hev
  let C2 := fullColumns D V (a+4) v
  let K2 := V \ (ball D V v (a+4)).erase v
  have hC2V : C2 ⊆ V := fun _ hx => shell_subset (Finset.mem_filter.mp hx).1
  have hcard2 : 4≤C2.card := by
    have hb := full_columns_bound (D:=D) (V:=V) (R:=a+4) (u:=v)
    change (shell D V (a+4) v).card≤C2.card+holes D V (a+4) v at hb
    omega
  have hK2 : K2.card=(a+6)*(a+3)+2 := by
    have he := Finset.card_sdiff_add_card_eq_card
      ((Finset.erase_subset v (ball D V v (a+4))).trans ball_subset)
    change K2.card+((ball D V v (a+4)).erase v).card=V.card at he
    nlinarith
  have hballs2 : ∀ h ∈ C2, ball D V h (a+3) ⊆ K2 := by
    apply full_bank_avoids (k:=a+3) hf hvV (by omega)
    intro y hy
    have he := Finset.card_erase_of_mem
      (self_mem_ball hvV : v ∈ ball D V v (a+3))
    have hl := radius_R_growth hf hm (ball_subset (Finset.mem_of_mem_erase hy))
    have hb : 0<(a+6)*(a+3) := by positivity
    omega
  have hC2K : C2 ⊆ K2 := fun h hh => hballs2 h hh (self_mem_ball (hC2V hh))
  obtain ⟨C0,hsub,hcard0⟩ := Finset.exists_subset_card_eq hcard2
  apply omission_two_four_false hf (by omega) (by omega)
    (hsub.trans hC2V) (hsub.trans hC2K) hcard0
    (fun h hh => hballs2 h (hsub hh))
  intro h hh
  have he := Finset.card_sdiff_add_card_eq_card (hballs2 h (hsub hh))
  have hl := radius_R_growth hf hm (hC2V (hsub hh))
  omega

theorem positive_R_excess {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ x ∈ V, a+6≤(outN D V x).card)
    (hn : V.card=(2*a+7)*(a+6)) :
    ∀ u ∈ V, (a+6)*(a+3)+1≤(ball D V u (a+3)).card := by
  intro u hu
  have hl := radius_R_growth hf hm hu
  have hne := third_strip_zero_root_false ha hf hm hn hu
  by_contra! hh
  exact hne (by omega)

#print axioms third_strip_zero_root_false
#print axioms positive_R_excess
end LeanCH.BR.DotTwoPassShellTransport


namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenThirdStrip
open Classical

private theorem positive_cell_saturation {a N c t e H : ℕ}
    (hN : N=(a+6)*(a+3)+e) (ht : t+e=a+4) (hc : c≤a+6+e)
    (hp : (2*a+7)*(a+6)+H≤N+c*t) :
    e=0 ∧ c=a+6 ∧ t=a+4 ∧ H=0 := by
  have hmul := Nat.mul_le_mul_right t hc
  have he : e=0 := by nlinarith [Nat.zero_le (e*e)]
  subst e
  have het : t=a+4 := by omega
  subst t
  have hec : c=a+6 := by nlinarith
  subst c
  exact ⟨rfl,rfl,rfl,by nlinarith⟩

/-- Source-wide positive R excess excludes the deficient R+1 ball. -/
theorem outer_positive_lower {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ x ∈ V, a+6≤(outN D V x).card)
    (hn : V.card=(2*a+7)*(a+6)) :
    ∀ u ∈ V, (a+6)*(a+4)≤(ball D V u (a+4)).card := by
  intro u hu
  have hlow := radius_R1_growth hf hm hu
  by_contra! hfail
  have hout : (ball D V u (a+4)).card+1=(a+6)*(a+4) := by omega
  have hr := positive_R_excess ha hf hm hn u hu
  obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hr
  let t := (shell D V (a+3) u).card
  let c := (layer D V (a+3) u).card
  let N := ((ball D V u (a+3)).erase u).card
  have htadd : t+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hcadd : c+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hNadd : N+1=(ball D V u (a+3)).card := by
    have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+3))
    have hp : 0<(ball D V u (a+3)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    dsimp [N]
    omega
  have hinner := inner_growth hf hm hu (a+2) (by omega) (by omega)
  have hN : N=(a+6)*(a+3)+e := by omega
  have ht : t+e=a+4 := by nlinarith
  have hc : c≤a+6+e := by nlinarith
  have hp := current_prefix_cells (k:=a+2) hf hm hu (by omega) (by change t<a+6; omega)
  change (2*a+7)*(a+6)+holes D V (a+3) u≤N+c*t at hp
  obtain ⟨he0,hcE,htE,hH⟩ := positive_cell_saturation hN ht hc hp
  have hsmall : (ball D V u (a+2)).card=(a+6)*(a+2)+1 := by nlinarith
  have hU : N=(a+6)*(a+3) := by omega
  let C := fullColumns D V (a+3) u
  let K := V \ (ball D V u (a+3)).erase u
  have hCV : C ⊆ V := fun _ hx => shell_subset (Finset.mem_filter.mp hx).1
  have hcard : 3≤C.card := by
    have hb := full_columns_bound (D:=D) (V:=V) (R:=a+3) (u:=u)
    change t≤C.card+holes D V (a+3) u at hb
    omega
  have hK : K.card=(a+6)*(a+4) := by
    have hh := Finset.card_sdiff_add_card_eq_card
      ((Finset.erase_subset u (ball D V u (a+3))).trans ball_subset)
    change K.card+N=V.card at hh
    nlinarith
  have hballs : ∀ h ∈ C, ball D V h (a+4) ⊆ K := by
    apply full_bank_avoids (k:=a+2) hf hu (by omega)
    intro y hy
    have he := Finset.card_erase_of_mem
      (self_mem_ball hu : u ∈ ball D V u (a+2))
    have hl := inner_growth hf hm (ball_subset (Finset.mem_of_mem_erase hy))
      (a+2) (by omega) (by omega)
    omega
  obtain ⟨C3,hsub,h3⟩ := Finset.exists_subset_card_eq hcard
  have hC3V : C3 ⊆ V := hsub.trans hCV
  have hC3K : C3 ⊆ K := fun h hh => hballs h (hsub hh) (self_mem_ball (hC3V hh))
  apply near_full_container_false hf (by omega : (a+4)+2≤2*a+7) hC3V hC3K
    (fun h hh => hballs h (hsub hh)) ?_ (by omega) (by omega)
  intro h hh
  have he := Finset.card_sdiff_add_card_eq_card (hballs h (hsub hh))
  have hl := radius_R1_growth hf hm (hC3V hh)
  omega

/-- The original upper-order source has an entrywise saturated complementary
reach tensor, not merely a scalar equality. -/
theorem source_middle_packet {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ x ∈ V, a+6≤(outN D V x).card)
    (hn : V.card=(2*a+7)*(a+6)) :
    (∀ u ∈ V, (ball D V u (a+3)).card=(a+6)*(a+3)+1) ∧
    (∀ u ∈ V, (ball D V u (a+4)).card=(a+6)*(a+4)) ∧
    (∀ u ∈ V, ∀ v ∈ V, u≠v →
      (v ∈ ball D V u (a+3) ↔ u ∉ ball D V v (a+4))) := by
  have h1 := positive_R_excess ha hf hm hn
  have h2 := outer_positive_lower ha hf hm hn
  have hsum : ((a+6)*(a+3)+1)+(a+6)*(a+4)=V.card+1 := by nlinarith
  have hrad : (a+3)+(a+4)≤2*a+7 := by omega
  have hc := two_balls_boundary_cards hf hrad h1 h2 hsum
  refine ⟨fun u hu => (hc u hu).1, fun u hu => (hc u hu).2.1, ?_⟩
  intro u hu v hv hne
  have he := Finset.ext_iff.mp
    (two_balls_boundary_complement hf (by omega : (a+4)+(a+3)≤2*a+7)
      h2 h1 (by omega) hv) u
  simpa only [reverseBall,Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff,
    Finset.mem_singleton,hu,true_and,hne,or_false] using he

#print axioms outer_positive_lower
#print axioms source_middle_packet
end LeanCH.BR.DotTwoPassShellTransport


namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenThirdStrip
open Classical

/-- Full columns share at most one bad origin when their punctured-inner
trap is exactly a global lower ball size. The exceptional label is common
to the entire bank, not chosen independently for each column. -/
theorem full_columns_common_exception_false
    {D : CH.Digraph} {V : Finset ℕ} {q k L u N : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hret : (k+1)+L≤q) (hnear : L+2≤q) (hq3 : 3≤q)
    (hinner : ∀ y ∈ V,
      ((ball D V u k).erase u).card≤(ball D V y k).card)
    (houter : ∀ y ∈ V, N≤(ball D V y L).card)
    (hK : (V \ (ball D V u (k+1)).erase u).card=N)
    (hcard : 3≤(fullColumns D V (k+1) u).card) : False := by
  let C := fullColumns D V (k+1) u
  let U := (ball D V u (k+1)).erase u
  let A := (ball D V u k).erase u
  let Y := U.filter (fun y => ∃ h ∈ C, h ∉ ball D V y (k+1))
  have hCV : C ⊆ V := fun _ hh => shell_subset (Finset.mem_filter.mp hh).1
  have hYball (y) (hy : y ∈ Y) : ball D V y k=A := by
    obtain ⟨hyU,h,hh,hbad⟩ := Finset.mem_filter.mp hy
    have hyV : y ∈ V := ball_subset (Finset.mem_of_mem_erase hyU)
    have hb := full_column_bad_ball hf hu (by omega) hh hyU hbad
    exact Finset.eq_of_subset_of_card_le hb (hinner y hyV)
  have hYcard : Y.card≤1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    have hyV : y ∈ V := ball_subset
      (Finset.mem_of_mem_erase (Finset.mem_filter.mp hy).1)
    have hzV : z ∈ V := ball_subset
      (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1)
    exact ball_root_injective_short hf (by omega) hyV hzV
      ((hYball y hy).trans (hYball z hz).symm)
  let K := (V \ U) ∪ Y
  have hKsize : K.card≤N+1 := by
    have hh := Finset.card_union_le (V \ U) Y
    change (V \ U).card=N at hK
    dsimp [K]
    omega
  have hballs (h) (hh : h ∈ C) : ball D V h L ⊆ K := by
    intro z hz
    have hzV : z ∈ V := ball_subset hz
    have hhT := (Finset.mem_filter.mp hh).1
    have hhV := hCV hh
    by_cases hzU : z ∈ U
    · apply Finset.mem_union.mpr
      right
      by_contra hn
      have hforw : h ∈ ball D V z (k+1) := by
        by_contra hb
        exact hn (Finset.mem_filter.mpr ⟨hzU,h,hh,hb⟩)
      have hne : z≠h := by
        intro he
        subst z
        exact (Finset.mem_sdiff.mp hhT).2 (Finset.mem_of_mem_erase hzU)
      have hc := reach_tensor_return_capacity hf hret hzV hhV
      simp [reachTensor,hforw,hz,hne] at hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hzV,hzU⟩))
  obtain ⟨C3,hsub,h3⟩ := Finset.exists_subset_card_eq hcard
  have hC3V : C3 ⊆ V := hsub.trans hCV
  have hC3K : C3 ⊆ K := fun h hh => hballs h (hsub hh) (self_mem_ball (hC3V hh))
  apply near_full_container_false hf hnear hC3V hC3K
    (fun h hh => hballs h (hsub hh)) ?_ (by omega) (by omega)
  intro h hh
  have he := Finset.card_sdiff_add_card_eq_card (hballs h (hsub hh))
  have hl := houter h (hC3V hh)
  omega

/-- The inner-flat equality follows from the original source and the
already-derived middle packet, with a single shared exceptional origin. -/
theorem source_inner_packet {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ x ∈ V, a+6≤(outN D V x).card)
    (hn : V.card=(2*a+7)*(a+6)) :
    ∀ u ∈ V, (ball D V u (a+2)).card=(a+6)*(a+2)+1 := by
  obtain ⟨hR,hR1,hcomp⟩ := source_middle_packet ha hf hm hn
  intro u hu
  let c := (layer D V (a+3) u).card
  let t := (shell D V (a+3) u).card
  let N := ((ball D V u (a+3)).erase u).card
  have hRu := hR u hu
  have hR1u := hR1 u hu
  have htadd : t+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hcadd : c+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hinner := inner_growth hf hm hu (a+2) (by omega) (by omega)
  have hc : c≤a+6 := by nlinarith
  have ht : t=a+5 := by nlinarith
  have hN : N=(a+6)*(a+3) := by
    have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+3))
    dsimp [N]
    omega
  have hp := current_prefix_cells (k:=a+2) hf hm hu (by omega) (by change t<a+6; omega)
  change (2*a+7)*(a+6)+holes D V (a+3) u≤N+c*t at hp
  have hcE : c=a+6 := by
    by_contra hne
    have hcl : c≤a+5 := by omega
    have hmul := Nat.mul_le_mul_right t hcl
    have hH : holes D V (a+3) u≤1 := by nlinarith
    have hcsmall : c=a+5 := by
      by_contra hne
      have hc2 : c≤a+4 := by omega
      have hmul2 := Nat.mul_le_mul_right t hc2
      nlinarith
    have hA : ((ball D V u (a+2)).erase u).card=(a+6)*(a+2)+1 := by
      have he := Finset.card_erase_of_mem
        (self_mem_ball hu : u ∈ ball D V u (a+2))
      have hb : (ball D V u (a+2)).card=(a+6)*(a+2)+2 := by nlinarith
      omega
    have hK : (V \ (ball D V u (a+3)).erase u).card=(a+6)*(a+4) := by
      have he := Finset.card_sdiff_add_card_eq_card
        ((Finset.erase_subset u (ball D V u (a+3))).trans ball_subset)
      change (V \ (ball D V u (a+3)).erase u).card+N=V.card at he
      nlinarith
    have hcard : 3≤(fullColumns D V (a+3) u).card := by
      have hb := full_columns_bound (D:=D) (V:=V) (R:=a+3) (u:=u)
      change t≤(fullColumns D V (a+3) u).card+holes D V (a+3) u at hb
      omega
    exact full_columns_common_exception_false (k:=a+2) (L:=a+4) hf hu (by omega)
      (by omega) (by omega) (fun y hy => by
        rw [hA]
        exact inner_growth hf hm hy (a+2) (by omega) (by omega))
      (fun y hy => (hR1 y hy).ge) hK hcard
  nlinarith

/-- Source-wide upper third-strip closure for s=a+6 >=7. All actual
source-to-flat adapters and the two-pass contradiction are included. -/
theorem third_strip_upper_false {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ x ∈ V, a+6≤(outN D V x).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+7)*(a+6)) : False := by
  obtain ⟨hR,hR1,hcomp⟩ := source_middle_packet ha hf hm hn
  exact third_strip_flat_false ha hf hm hne hn
    (source_inner_packet ha hf hm hn) hR hR1 hcomp

#print axioms full_columns_common_exception_false
#print axioms source_inner_packet
#print axioms third_strip_upper_false
end LeanCH.BR.DotTwoPassShellTransport


namespace LeanCH.BR.DotTwoPassShellTransport
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenThirdStrip

/-- Arbitrary finite nonempty hosts, not only one labelled endpoint. -/
theorem order_third_strip_closed {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+7))
    (hm : ∀ x ∈ V, a+6≤(outN D V x).card) (hne : V.Nonempty) :
    (2*a+7)*(a+6)<V.card := by
  have hl := order_to_top hf hm hne
  by_contra! hn
  exact third_strip_upper_false ha hf hm hne (by omega)

/-- User-facing third-strip statement, proved from the actual source
without flatness, exact outdegree, or a supplied rectangle certificate. -/
theorem cycle_third_strip_closed {s q n : ℕ} {D : CH.Digraph}
    (hs : 7≤s) (hq : q=2*s-5) (hn : 0<n) (hnq : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a, s=a+6 := ⟨s-6,by omega⟩
  subst s
  have hq' : q=2*a+7 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := order_third_strip_closed (by omega : 1≤a) (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at ho
  omega

#print axioms order_third_strip_closed
#print axioms cycle_third_strip_closed
end LeanCH.BR.DotTwoPassShellTransport

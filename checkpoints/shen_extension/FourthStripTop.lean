import checkpoints.shen_extension.FourthStripFlat

/-!
# First reductions at the top order n = qs of the cutoff q = 2s-6 (s ≥ 8)

For s ≥ 8 every q-free host of minimum out-degree s has at least qs vertices
(`order_to_top`).  That same-degree bound has zero slack on the minimal prefixes, so
their arc tables are complete, and a sink of the last layer must send all its arcs
to the next layer.  This gives, for every host,

  |B_(R-1)| = s(R-1)  ⇒  |L_R| ≥ s,          `inner_min_next`
  |B_(R+1)| ≥ s(R+1)-2,                       `top_R1_growth`

and for hosts of order at most qs,

  |B_R| ≥ sR,                                 `top_R_growth`
  |B_(R-1)| ≥ s(R-1)+1  ⇒  |B_(R+1)| ≥ s(R+1)-1.   `top_R1_of_inner`
-/
namespace LeanCH.BR.ShenFourthStrip
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- A same-degree prefix budget with no slack: the spare term vanishes, the last layer has
its maximal size, and every row points to every vertex of the next layer. -/
theorem tight_table {q s L k u cmax w : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (hu : u ∈ V) (hs : 1≤s)
    (hlower : ∀ (F : CH.Digraph) (W : Finset ℕ), QFree F W q →
      (∀ v ∈ W, s≤(outN F W v).card) → W.Nonempty → L≤W.card)
    (hk : k+2≤q) (ht : (ball D V u (k+2) \ ball D V u (k+1)).card<s)
    (hc : (ball D V u (k+1) \ ball D V u k).card≤cmax)
    (hbud : ((ball D V u (k+1)).erase u).card+
      cmax*(ball D V u (k+2) \ ball D V u (k+1)).card+w≤L) :
    w=0 ∧
    (1≤(ball D V u (k+2) \ ball D V u (k+1)).card →
      (ball D V u (k+1) \ ball D V u k).card=cmax) ∧
    ∀ z ∈ ball D V u (k+1) \ ball D V u k,
      ∀ h ∈ ball D V u (k+2) \ ball D V u (k+1), D z h = true := by
  have hret := minOut_prefix_erase (d:=1) hf hu (by omega : (k+1)+1≤q) hm
    (by change 1+(ball D V u (k+2) \ ball D V u (k+1)).card≤s; omega)
  have cap := PrefixTensor.same_degree_missing_capacity hf hm hu hs hlower hk hret
  have hmul := Nat.mul_le_mul_right (ball D V u (k+2) \ ball D V u (k+1)).card hc
  have hw : w=0 := by omega
  have hsum : (∑ v ∈ ball D V u (k+1) \ ball D V u k,
      ((ball D V u (k+2) \ ball D V u (k+1)) \
        outN D (ball D V u (k+2) \ ball D V u (k+1)) v).card)=0 := by omega
  refine ⟨hw,?_,?_⟩
  · intro ht1
    by_contra hne
    have hstep : (ball D V u (k+1) \ ball D V u k).card+1≤cmax := by omega
    have hmul2 := Nat.mul_le_mul_right (ball D V u (k+2) \ ball D V u (k+1)).card hstep
    have hexp : ((ball D V u (k+1) \ ball D V u k).card+1)*
        (ball D V u (k+2) \ ball D V u (k+1)).card=
        (ball D V u (k+1) \ ball D V u k).card*(ball D V u (k+2) \ ball D V u (k+1)).card+
          (ball D V u (k+2) \ ball D V u (k+1)).card := by ring
    omega
  · intro z hz h hh
    have hz0 := (Finset.sum_eq_zero_iff.mp hsum) z hz
    have hempty := Finset.card_eq_zero.mp hz0
    by_contra hnd
    have hmem : h ∈ (ball D V u (k+2) \ ball D V u (k+1)) \
        outN D (ball D V u (k+2) \ ball D V u (k+1)) z :=
      Finset.mem_sdiff.mpr ⟨hh,fun ho => hnd (mem_outN.mp ho).2⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty h hmem

/-- If every vertex of the punctured k-ball reaches every vertex of layer k+1 within k
steps, a sink of that layer sends all its arcs into layer k+2. -/
theorem sink_next_layer {q s k v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hm : ∀ w ∈ V, s≤(outN D V w).card) (hv : v ∈ V) (hk : k+2≤q)
    (hTq : (ball D V v (k+1) \ ball D V v k).card≤q)
    (hTne : (ball D V v (k+1) \ ball D V v k).Nonempty)
    (hreach : ∀ y ∈ (ball D V v k).erase v, ∀ h ∈ ball D V v (k+1) \ ball D V v k,
      h ∈ ball D V y k) :
    s≤(ball D V v (k+2) \ ball D V v (k+1)).card := by
  have hTV : ball D V v (k+1) \ ball D V v k ⊆ V :=
    fun _ h => ball_subset (Finset.mem_sdiff.mp h).1
  obtain ⟨z,hz,hsink⟩ := exists_sink (hf.mono_set hTV) hTne hTq
  obtain ⟨hz1,hz0⟩ := Finset.mem_sdiff.mp hz
  have hsub : outN D V z ⊆ ball D V v (k+2) \ ball D V v (k+1) := by
    intro w hw
    obtain ⟨hwV,hzw⟩ := mem_outN.mp hw
    refine Finset.mem_sdiff.mpr ⟨ball_step hz1 hwV hzw,fun hw1 => ?_⟩
    by_cases hwk : w ∈ ball D V v k
    · have hwv : w≠v := by
        intro he
        subst he
        exact no_back_arc hf hv hz1 (by omega) hzw
      have hzr := hreach w (Finset.mem_erase.mpr ⟨hwv,hwk⟩) z hz
      have hne : w≠z := by
        intro he
        subst he
        exact hz0 hwk
      exact return_false hf (by omega : k+1≤q) hne hzr
        (mem_ball.mpr ⟨hwV,1,le_rfl,.step hwV hzw (.refl w)⟩)
    · exact hsink w (Finset.mem_sdiff.mpr ⟨hw1,hwk⟩) hzw
  exact (hm z (hTV hz)).trans (Finset.card_le_card hsub)

/-- The two-omission form of `exceptional_bank_false`. -/
theorem exceptional_bank2_false {D : CH.Digraph} {V U C Z : Finset ℕ} {q r L k0 : ℕ}
    (hf : QFree D V q) (hUV : U ⊆ V) (hCK : C ⊆ V \ U)
    (hk0 : k0+1≤q) (hrL : r+L≤q) (hL : L+3≤q) (hq8 : 8≤q)
    (hY : ∀ y ∈ U, (∃ h ∈ C, h ∉ ball D V y r) → ball D V y k0 = Z)
    (hsize : ∀ h ∈ C, (V \ U).card≤(ball D V h L).card+1)
    (hC4 : 4≤C.card) : False := by
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
  have hmiss (h) (hh : h ∈ C) : (K \ ball D V h L).card≤2 := by
    have hc := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    have hs := hsize h hh
    omega
  exact two_omission_container_false hf hL hq8 hCV hCK2 hballs hmiss hC4

/-- A root whose (R-1)-ball has the minimum size s(R-1) has at least s vertices at
distance R. -/
theorem inner_min_next {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (ha : 1≤a) (hx : (ball D V v (a+3)).card=(a+7)*(a+3)) :
    a+7≤(ball D V v (a+4) \ ball D V v (a+3)).card := by
  have hprev := inner_growth hf hm hv (a+2) (by omega) (by omega)
  have hinner := inner_growth hf hm hv (a+1) (by omega) (by omega)
  have hTs : (ball D V v (a+3) \ ball D V v (a+2)).card+(ball D V v (a+2)).card=
      (ball D V v (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hSs : (ball D V v (a+2) \ ball D V v (a+1)).card+(ball D V v (a+1)).card=
      (ball D V v (a+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hUc : ((ball D V v (a+2)).erase v).card+1=(ball D V v (a+2)).card := by
    have he := Finset.card_erase_of_mem (s:=ball D V v (a+2)) (self_mem_ball hv)
    have hp : 0<(ball D V v (a+2)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    omega
  have hexp : (a+7)*(a+3)=(a+7)*(a+2)+(a+7) := by ring
  have hexq : (a+7)*(a+2)=(a+7)*(a+1)+(a+7) := by ring
  obtain ⟨p,hp⟩ : ∃ p, (ball D V v (a+2)).card=(a+7)*(a+2)+1+p :=
    ⟨(ball D V v (a+2)).card-((a+7)*(a+2)+1),by omega⟩
  have htp : (ball D V v (a+3) \ ball D V v (a+2)).card+p=a+6 := by omega
  have hc : (ball D V v (a+2) \ ball D V v (a+1)).card≤a+7+p := by omega
  have hbud : ((ball D V v (a+2)).erase v).card+
      (a+7+p)*(ball D V v (a+3) \ ball D V v (a+2)).card+p*p≤(2*a+8)*(a+7) := by
    have hprod := congrArg (fun z : ℕ => (a+7+p)*z) htp
    have hN : ((ball D V v (a+2)).erase v).card=(a+7)*(a+2)+p := by omega
    nlinarith only [hN,htp,hprod]
  obtain ⟨hw,hSc,hfull⟩ := tight_table (L:=(2*a+8)*(a+7)) (k:=a+1) hf hm hv
    (by omega : 1≤a+7) (fun F W hf1 hm1 hn1 => order_to_top hf1 hm1 hn1 ha)
    (by omega : (a+1)+2≤2*a+8)
    (by change (ball D V v (a+3) \ ball D V v (a+2)).card<a+7; omega) hc hbud
  have hp0 : p=0 := by
    rcases Nat.eq_zero_or_pos p with h|h
    · exact h
    · have := Nat.mul_pos h h
      omega
  subst hp0
  have hSc2 : (ball D V v (a+2) \ ball D V v (a+1)).card=a+7 :=
    hSc (by change 1≤(ball D V v (a+3) \ ball D V v (a+2)).card; omega)
  have hexact : (ball D V v (a+1)).card=(a+7)*(a+1)+1 := by omega
  have hsmall : ((ball D V v (a+1)).erase v).card=(a+7)*(a+1) := by
    have he := Finset.card_erase_of_mem (s:=ball D V v (a+1)) (self_mem_ball hv)
    rw [hexact] at he
    omega
  have hnext := sink_next_layer (k:=a+2) hf hm hv (by omega : (a+2)+2≤2*a+8)
    (by change (ball D V v (a+3) \ ball D V v (a+2)).card≤2*a+8; omega)
    (Finset.card_pos.mp
      (by change 0<(ball D V v (a+3) \ ball D V v (a+2)).card; omega))
    (by
      intro y hy h hh
      have hyV : y ∈ V := ball_subset (Finset.mem_of_mem_erase hy)
      have hlarge := inner_growth hf hm hyV (a+1) (by omega) (by omega)
      obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hv (by omega : (a+1)+1≤2*a+8) hy
        (by omega)
      exact ball_step hyz (ball_subset (Finset.mem_sdiff.mp hh).1) (hfull z hz h hh))
  exact hnext

/-- Every (R+1)-ball has at least s(R+1)-2 vertices, in every host. -/
theorem top_R1_growth {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (ha : 1≤a) : (a+7)*(a+5)≤(ball D V v (a+5)).card+2 := by
  by_contra! hbad
  have hlow := radius_R1_growth hf hm hv
  have hR := radius_R_growth hf hm hv
  have hRm := radius_Rm1_growth hf hm hv
  have hT : (ball D V v (a+5) \ ball D V v (a+4)).card+(ball D V v (a+4)).card=
      (ball D V v (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : (ball D V v (a+4) \ ball D V v (a+3)).card+(ball D V v (a+3)).card=
      (ball D V v (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hU : ((ball D V v (a+4)).erase v).card+1=(ball D V v (a+4)).card := by
    have he := Finset.card_erase_of_mem (s:=ball D V v (a+4)) (self_mem_ball hv)
    have hp : 0<(ball D V v (a+4)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    omega
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  obtain ⟨e,he⟩ : ∃ e, (ball D V v (a+4)).card+1=(a+7)*(a+4)+e :=
    ⟨(ball D V v (a+4)).card+1-(a+7)*(a+4),by omega⟩
  have hte : (ball D V v (a+5) \ ball D V v (a+4)).card+e=a+5 := by omega
  have hc : (ball D V v (a+4) \ ball D V v (a+3)).card≤a+6+e := by omega
  have hbud : ((ball D V v (a+4)).erase v).card+
      (a+6+e)*(ball D V v (a+5) \ ball D V v (a+4)).card+e*e≤(2*a+8)*(a+7) := by
    have hprod := congrArg (fun z : ℕ => (a+6+e)*z) hte
    have hN : ((ball D V v (a+4)).erase v).card+2=(a+7)*(a+4)+e := by omega
    nlinarith only [hN,hte,hprod]
  obtain ⟨hw,hSc,_⟩ := tight_table (L:=(2*a+8)*(a+7)) (k:=a+3) hf hm hv
    (by omega : 1≤a+7) (fun F W hf1 hm1 hn1 => order_to_top hf1 hm1 hn1 ha)
    (by omega : (a+3)+2≤2*a+8)
    (by change (ball D V v (a+5) \ ball D V v (a+4)).card<a+7; omega) hc hbud
  have he0 : e=0 := by
    rcases Nat.eq_zero_or_pos e with h|h
    · exact h
    · have := Nat.mul_pos h h
      omega
  subst he0
  have hSc2 : (ball D V v (a+4) \ ball D V v (a+3)).card=a+6 :=
    hSc (by change 1≤(ball D V v (a+5) \ ball D V v (a+4)).card; omega)
  have hnext := inner_min_next hf hm hv ha (by omega)
  omega

/-- In a host of order at most qs every R-ball has at least sR vertices. -/
theorem top_R_growth {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (hn : V.card≤(2*a+8)*(a+7)) (ha : 1≤a) :
    (a+7)*(a+4)≤(ball D V v (a+4)).card := by
  by_contra! hbad
  have hR := radius_R_growth hf hm hv
  have hRm := radius_Rm1_growth hf hm hv
  have hprev := inner_growth hf hm hv (a+2) (by omega) (by omega)
  have hT : (ball D V v (a+4) \ ball D V v (a+3)).card+(ball D V v (a+3)).card=
      (ball D V v (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : (ball D V v (a+3) \ ball D V v (a+2)).card+(ball D V v (a+2)).card=
      (ball D V v (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hU : ((ball D V v (a+3)).erase v).card+1=(ball D V v (a+3)).card := by
    have he := Finset.card_erase_of_mem (s:=ball D V v (a+3)) (self_mem_ball hv)
    have hp : 0<(ball D V v (a+3)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    omega
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hexr : (a+7)*(a+3)=(a+7)*(a+2)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  obtain ⟨x,hx⟩ : ∃ x, (ball D V v (a+3)).card=(a+7)*(a+3)+x :=
    ⟨(ball D V v (a+3)).card-(a+7)*(a+3),by omega⟩
  have hx1 : 1≤x := by
    by_contra h0
    have hx0 : x=0 := by omega
    subst hx0
    have hnext := inner_min_next hf hm hv ha (by omega)
    omega
  have htx : (ball D V v (a+4) \ ball D V v (a+3)).card+x=a+6 := by omega
  have hc : (ball D V v (a+3) \ ball D V v (a+2)).card≤a+6+x := by omega
  have hsq : x≤x*x := Nat.le_mul_self x
  have hbud : ((ball D V v (a+3)).erase v).card+
      (a+6+x)*(ball D V v (a+4) \ ball D V v (a+3)).card+(x*x-x)≤(2*a+8)*(a+7) := by
    have hprod := congrArg (fun z : ℕ => (a+6+x)*z) htx
    have hN : ((ball D V v (a+3)).erase v).card+1=(a+7)*(a+3)+x := by omega
    have key : ((ball D V v (a+3)).erase v).card+
        (a+6+x)*(ball D V v (a+4) \ ball D V v (a+3)).card+x*x≤(2*a+8)*(a+7)+x := by
      nlinarith only [hN,htx,hprod]
    omega
  obtain ⟨hw,hSc,hfull⟩ := tight_table (L:=(2*a+8)*(a+7)) (k:=a+2) hf hm hv
    (by omega : 1≤a+7) (fun F W hf1 hm1 hn1 => order_to_top hf1 hm1 hn1 ha)
    (by omega : (a+2)+2≤2*a+8)
    (by change (ball D V v (a+4) \ ball D V v (a+3)).card<a+7; omega) hc hbud
  have hxe : x=1 := by
    by_contra hne
    have h2 : 2≤x := by omega
    have := Nat.mul_le_mul_right x h2
    omega
  subst hxe
  have hSc2 : (ball D V v (a+3) \ ball D V v (a+2)).card=a+7 :=
    hSc (by change 1≤(ball D V v (a+4) \ ball D V v (a+3)).card; omega)
  let U := (ball D V v (a+3)).erase v
  let T := ball D V v (a+4) \ ball D V v (a+3)
  have hUV : U ⊆ V := (Finset.erase_subset v _).trans ball_subset
  have hCK : T ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hnb⟩ := Finset.mem_sdiff.mp hh
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hnb (Finset.mem_of_mem_erase hU)⟩
  have hsmall : ((ball D V v (a+2)).erase v).card+1=(ball D V v (a+2)).card := by
    have he := Finset.card_erase_of_mem (s:=ball D V v (a+2)) (self_mem_ball hv)
    have hp : 0<(ball D V v (a+2)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    omega
  have hreach : ∀ h ∈ T, ∀ y ∈ U, h ∈ ball D V y (a+3) := by
    intro h hh y hy
    have hlarge := inner_growth hf hm (hUV hy) (a+2) (by omega) (by omega)
    obtain ⟨z,hz,hyz⟩ := PrefixTensor.hits_layer hf hv (by omega : (a+2)+1≤2*a+8) hy
      (by omega)
    exact ball_step hyz (ball_subset (Finset.mem_sdiff.mp hh).1) (hfull z hz h hh)
  have hballs := ShenThirdStrip.bank_avoids (k:=a+5) hf hCK
    (by omega : (a+5)+(a+3)≤2*a+8) hreach
  let K := V \ U
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hUc : U.card+1=(ball D V v (a+3)).card := hU
  have hmiss (h) (hh : h ∈ T) : (K \ ball D V h (a+5)).card≤2 := by
    have hg := top_R1_growth hf hm (Finset.mem_sdiff.mp (hCK hh)).1 ha
    have he := Finset.card_sdiff_add_card_eq_card (hballs h hh)
    change (K \ ball D V h (a+5)).card+(ball D V h (a+5)).card=K.card at he
    omega
  have hT4 : 4≤T.card := by
    change 4≤(ball D V v (a+4) \ ball D V v (a+3)).card
    omega
  exact two_omission_container_false hf (by omega : (a+5)+3≤2*a+8) (by omega)
    (fun _ hh => (Finset.mem_sdiff.mp (hCK hh)).1) hCK hballs hmiss hT4

private theorem three_le_sq_add_two (e : ℕ) : 3*e≤e*e+2 := by
  rcases Nat.lt_or_ge e 3 with h|h
  · have h3 : e=0 ∨ e=1 ∨ e=2 := by omega
    rcases h3 with rfl|rfl|rfl <;> decide
  · have := Nat.mul_le_mul_right e h
    omega

/-- In a host of order at most qs, a root with |B_(R-1)| ≥ s(R-1)+1 has
|B_(R+1)| ≥ s(R+1)-1. -/
theorem top_R1_of_inner {a v : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+8)) (hm : ∀ w ∈ V, a+7≤(outN D V w).card) (hv : v ∈ V)
    (hn : V.card≤(2*a+8)*(a+7)) (ha : 1≤a)
    (hx : (a+7)*(a+3)+1≤(ball D V v (a+3)).card) :
    (a+7)*(a+5)≤(ball D V v (a+5)).card+1 := by
  by_contra! hbad
  have hlow := top_R1_growth hf hm hv ha
  have hRall := fun w hw => top_R_growth hf hm (v:=w) hw hn ha
  have hRv := hRall v hv
  let B := ball D V v (a+4)
  let U := B.erase v
  let S := B \ ball D V v (a+3)
  let T := ball D V v (a+5) \ B
  have hB : U.card+1=B.card := by
    have he := Finset.card_erase_of_mem (s:=B) (self_mem_ball hv)
    have hp : 0<B.card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    change U.card=B.card-1 at he
    omega
  have hT : T.card+B.card=(ball D V v (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hS : S.card+(ball D V v (a+3)).card=B.card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hexp : (a+7)*(a+5)=(a+7)*(a+4)+(a+7) := by ring
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  obtain ⟨e,he⟩ : ∃ e, B.card+1=(a+7)*(a+4)+e :=
    ⟨B.card+1-(a+7)*(a+4),by change (a+7)*(a+4)≤B.card at hRv; omega⟩
  have he1 : 1≤e := by change (a+7)*(a+4)≤B.card at hRv; omega
  have hte : T.card+e=a+6 := by omega
  have hc : S.card≤a+5+e := by omega
  have hN : U.card+2=(a+7)*(a+4)+e := by omega
  have budget : U.card+(a+5+e)*T.card+(a+4)≤(2*a+8)*(a+7)+T.card := by
    have hprod := congrArg (fun z : ℕ => (a+5+e)*z) hte
    have hsq := three_le_sq_add_two e
    nlinarith only [hN,hte,hprod,hsq]
  have hrect := same_rectangle (L:=(2*a+8)*(a+7)) hf hm hv (by omega : 1≤a+7)
    (fun F W hf1 hm1 hn1 => order_to_top hf1 hm1 hn1 ha)
    (by omega : (a+3)+2≤2*a+8) (by change T.card<a+7; omega) hc budget (by omega : 1≤a+4)
  have hSc : S.card=a+5+e := hrect.1
  let C := T.filter (fun h => ∀ w ∈ S, D w h=true)
  have hC : a+4≤C.card := by
    have hCe : C = (ball D V v ((a+3)+2) \ ball D V v ((a+3)+1)).filter
        (fun h => ∀ w ∈ ball D V v ((a+3)+1) \ ball D V v (a+3), D w h=true) := by
      ext h
      simp only [C,Finset.mem_filter]
      rfl
    rw [hCe]
    exact hrect.2
  have hUV : U ⊆ V := (Finset.erase_subset v B).trans ball_subset
  have hCT : C ⊆ T := Finset.filter_subset _ _
  have hCK : C ⊆ V \ U := by
    intro h hh
    obtain ⟨hb,hnb⟩ := Finset.mem_sdiff.mp (hCT hh)
    exact Finset.mem_sdiff.mpr ⟨ball_subset hb,fun hU => hnb (Finset.mem_of_mem_erase hU)⟩
  have hK : (V \ U).card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  have hsmall : ((ball D V v (a+3)).erase v).card+1=(ball D V v (a+3)).card := by
    have hee := Finset.card_erase_of_mem (s:=ball D V v (a+3)) (self_mem_ball hv)
    have hp : 0<(ball D V v (a+3)).card := Finset.card_pos.mpr ⟨v,self_mem_ball hv⟩
    omega
  refine exceptional_bank2_false (U:=U) (C:=C) (Z:=(ball D V v (a+3)).erase v)
    (r:=a+4) (L:=a+4) (k0:=a+3) hf hUV hCK (by omega) (by omega) (by omega) (by omega)
    ?_ ?_ (by omega)
  · rintro y hy ⟨h,hh,hbad2⟩
    have hhV : h ∈ V := (Finset.mem_sdiff.mp (hCK hh)).1
    have hsub := full_bad_ball (k:=a+3) hf hv (by omega) hhV
      (fun z hz => (Finset.mem_filter.mp hh).2 z hz) hy hbad2
    have hlarge := radius_Rm1_growth hf hm (hUV hy)
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · intro h hh
    have hhV : h ∈ V := (Finset.mem_sdiff.mp (hCK hh)).1
    have hRh := hRall h hhV
    omega

#print axioms tight_table
#print axioms sink_next_layer
#print axioms exceptional_bank2_false
#print axioms inner_min_next
#print axioms top_R1_growth
#print axioms top_R_growth
#print axioms top_R1_of_inner
end LeanCH.BR.ShenFourthStrip

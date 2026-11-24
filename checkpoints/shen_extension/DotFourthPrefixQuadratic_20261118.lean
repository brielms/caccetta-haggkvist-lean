import checkpoints.shen_extension.DotClonePairCompletion_20261118
import checkpoints.shen_extension.FourthStripFlat

/-! Actual-prefix application of the joint completion-pair carrier.
The source growth/minimum-root supplier is kept in a separate module. -/
namespace LeanCH.BR.DotFourthPrefixQuadratic
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open DotTwoPassShellTransport DotClonePairCompletion
open Classical

/-- Physical degree gaps and missing cells coexist in ONE punctured prefix. -/
theorem prefix_gap_budget {q s k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V,s≤(outN D V v).card)
    (hu : u ∈ V) (hs : 1≤s) (hk : k+2≤q)
    (ht : (shell D V (k+1) u).card<s) :
    let U := (ball D V u (k+1)).erase u
    let S := layer D V (k+1) u
    let T := shell D V (k+1) u
    let g := fun v => s-(outN D U v).card
    U.Nonempty ∧ (∀ v ∈ U,1≤(outN D U v).card) ∧ S ⊆ U ∧
      (∀ v ∈ U \ S,g v=0) ∧
      (∑ v ∈ U,g v)+holes D V (k+1) u≤S.card*T.card := by
  let U := (ball D V u (k+1)).erase u
  let S := layer D V (k+1) u
  let T := shell D V (k+1) u
  let g := fun v => s-(outN D U v).card
  let miss := fun v => (T \ outN D T v).card
  change U.Nonempty ∧ (∀ v ∈ U,1≤(outN D U v).card) ∧ S ⊆ U ∧
    (∀ v ∈ U \ S,g v=0) ∧ (∑ v ∈ U,g v)+holes D V (k+1) u≤S.card*T.card
  have hSU : S ⊆ U := by
    intro v hv
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_erase.mpr ⟨?_,hb⟩
    intro he
    subst v
    exact hn (self_mem_ball hu)
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hret : ∀ v ∈ U,1≤(outN D U v).card := by
    apply minOut_prefix_erase (d:=1) hf hu (by omega) hm
    change 1+T.card≤s
    change T.card<s at ht
    omega
  have hne : U.Nonempty := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by have := hm u hu; omega :
      0<(outN D V u).card)
    obtain ⟨hvV,huv⟩ := mem_outN.mp hv
    refine ⟨v,Finset.mem_erase.mpr ⟨?_,?_⟩⟩
    · intro he
      subst v
      exact loopfree hf (by omega) hu huv
    · exact ball_mono_radius (by omega : 1≤k+1)
        (mem_ball.mpr ⟨hvV,1,by omega,.step hvV huv (.refl v)⟩)
  have hz (v) (hv : v ∈ U \ S) : g v=0 := by
    obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hv
    have hi : v ∈ ball D V u k := by
      by_contra hh
      apply hn
      change v ∈ ball D V u (k+1) \ ball D V u ((k+1)-1)
      simpa only [Nat.add_sub_cancel] using
        Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv,hh⟩
    have h := (hm v (ball_subset hi)).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by omega) hi))
    change s≤(outN D U v).card at h
    dsimp only [g]
    omega
  have hzero := Finset.sum_eq_zero hz
  have hsum := Finset.sum_sdiff hSU (f:=g)
  have cap (v) (hv : v ∈ S) : g v+miss v≤T.card := by
    have hsub := outN_prefix_loss hf hu (by omega : (k+1)+1≤q) (hSU hv)
    have hsub' : outN D V v ⊆ outN D U v ∪ outN D T v := by
      intro w hw
      obtain hh|hh := Finset.mem_union.mp (hsub hw)
      · exact Finset.mem_union_left _ hh
      · exact Finset.mem_union_right _ (mem_outN.mpr ⟨hh,(mem_outN.mp hw).2⟩)
    have hcount := (hm v (hUV (hSU hv))).trans
      ((Finset.card_le_card hsub').trans (Finset.card_union_le _ _))
    have hmiss : miss v+(outN D T v).card=T.card :=
      Finset.card_sdiff_add_card_eq_card (fun _ hw => (mem_outN.mp hw).1)
    dsimp only [g]
    omega
  have hcap := Finset.sum_le_sum cap
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at hcap
  refine ⟨hne,hret,hSU,hz,?_⟩
  change (∑ v ∈ U,g v)+(∑ v ∈ S,miss v)≤S.card*T.card
  omega

/-- Full columns impose a lower bound on ACTUAL holes, before completing
the prefix. Coincident suppliers are not counted as distinct. -/
theorem minimum_table_holes {a e u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (he : e≤1) (hf : QFree D V (2*a+8))
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V)
    (hR : (ball D V u (a+4)).card=(a+7)*(a+4))
    (hprev : (ball D V u (a+3)).card=(a+7)*(a+3)+1+e)
    (hinner : (ball D V u (a+2)).card=(a+7)*(a+2)+1)
    (hsmall : ∀ y ∈ V,(a+7)*(a+2)+1≤(ball D V y (a+2)).card)
    (houter : ∀ y ∈ V,(a+7)*(a+5)≤(ball D V y (a+5)).card+1) :
    a+7≤holes D V (a+3) u+3 := by
  let C := fullColumns D V (a+3) u
  let K := V \ (ball D V u (a+3)).erase u
  have hCV : C ⊆ V := fun _ hh => shell_subset (Finset.mem_filter.mp hh).1
  have hU : ((ball D V u (a+3)).erase u).card=(a+7)*(a+3)+e := by
    have hh := Finset.card_erase_of_mem
      (self_mem_ball hu : u ∈ ball D V u (a+3))
    omega
  have hK : K.card+e=(a+7)*(a+5) := by
    have hh := Finset.card_sdiff_add_card_eq_card
      ((Finset.erase_subset u (ball D V u (a+3))).trans ball_subset)
    change K.card+((ball D V u (a+3)).erase u).card=V.card at hh
    nlinarith
  have hT : (shell D V (a+3) u).card+e=a+6 := by
    have hh := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by omega : a+3≤a+4))
    change (shell D V (a+3) u).card+(ball D V u (a+3)).card =
      (ball D V u (a+4)).card at hh
    nlinarith
  have hballs : ∀ h ∈ C,ball D V h (a+5) ⊆ K := by
    apply full_bank_avoids (k:=a+2) hf hu (by omega)
    intro y hy
    have hh := Finset.card_erase_of_mem
      (self_mem_ball hu : u ∈ ball D V u (a+2))
    have hl := hsmall y (ball_subset (Finset.mem_of_mem_erase hy))
    omega
  have hCbound : C.card+e≤2 := by
    rcases (by omega : e=0 ∨ e=1) with rfl|rfl
    · by_contra! hh
      have hc : 3≤C.card := by omega
      obtain ⟨C3,hsub,h3⟩ := Finset.exists_subset_card_eq hc
      have hC3V : C3 ⊆ V := hsub.trans hCV
      have hC3K : C3 ⊆ K := fun h hh => hballs h (hsub hh) (self_mem_ball (hC3V hh))
      apply near_full_container_false hf (by omega : (a+5)+2≤2*a+8) hC3V hC3K
        (fun h hh => hballs h (hsub hh)) ?_ (by omega) (by omega)
      intro h hh
      have hc := Finset.card_sdiff_add_card_eq_card (hballs h (hsub hh))
      have hl := houter h (hC3V hh)
      omega
    · have hc : C.card≤1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        have hxe : ball D V x (a+5)=K :=
          Finset.eq_of_subset_of_card_le (hballs x hx) (by
            have hl := houter x (hCV hx)
            omega)
        have hye : ball D V y (a+5)=K :=
          Finset.eq_of_subset_of_card_le (hballs y hy) (by
            have hl := houter y (hCV hy)
            omega)
        exact ball_root_injective_short hf (by omega) (hCV hx) (hCV hy)
          (hxe.trans hye.symm)
      omega
  have hb := full_columns_bound (D:=D) (V:=V) (R:=a+3) (u:=u)
  change (shell D V (a+3) u).card≤C.card+holes D V (a+3) u at hb
  omega

#print axioms prefix_gap_budget
#print axioms minimum_table_holes
end LeanCH.BR.DotFourthPrefixQuadratic


namespace LeanCH.BR.DotFourthPrefixQuadratic
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open DotTwoPassShellTransport DotClonePairCompletion
open Classical

/-- The actual minimum-root packet is impossible for s>=12. Completion
uses ONLY the order-independent native radius floor, never capped growth. -/
theorem minimum_table_false {a e u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (he : e≤1) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V,a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V)
    (hR : (ball D V u (a+4)).card=(a+7)*(a+4))
    (hprev : (ball D V u (a+3)).card=(a+7)*(a+3)+1+e)
    (hinner : (ball D V u (a+2)).card=(a+7)*(a+2)+1)
    (houter : ∀ y ∈ V,(a+7)*(a+5)≤(ball D V y (a+5)).card+1) : False := by
  have hsmall (y) (hy : y ∈ V) :
      (a+7)*(a+2)+1≤(ball D V y (a+2)).card :=
    ShenFourthStrip.inner_growth hf hm hy (a+2) (by omega) (by omega)
  have hH := minimum_table_holes ha he hf hn hu hR hprev hinner hsmall houter
  let U := (ball D V u (a+3)).erase u
  let S := layer D V (a+3) u
  let T := shell D V (a+3) u
  let g := fun v => (a+7)-(outN D U v).card
  let dsum := ∑ v ∈ U,g v
  let Q := ∑ v ∈ U,g v*(g v+1)
  let K := U.card+dsum
  have hKdef : K=U.card+dsum := rfl
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hU : U.card=(a+7)*(a+3)+e := by
    have hh := Finset.card_erase_of_mem
      (self_mem_ball hu : u ∈ ball D V u (a+3))
    dsimp only [U]
    omega
  have hS : S.card=a+7+e := by
    have hh : S.card+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
      Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
    nlinarith
  have hT : T.card+e=a+6 := by
    have hh : T.card+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
      Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
    nlinarith
  have ht : (shell D V ((a+2)+1) u).card<a+7 := by change T.card<a+7; omega
  obtain ⟨hne,hret,hSU,hzero,hbudget⟩ :=
    prefix_gap_budget (k:=a+2) hf hm hu (by omega) (by omega) ht
  change U.Nonempty at hne
  change (∀ v ∈ U,1≤(outN D U v).card) at hret
  change S ⊆ U at hSU
  change (∀ v ∈ U \ S,g v=0) at hzero
  change dsum+holes D V (a+3) u≤S.card*T.card at hbudget
  have hDsupport : (∑ v ∈ S,g v)=∑ v ∈ U,g v :=
    Finset.sum_subset hSU (fun v hv hn => hzero v (Finset.mem_sdiff.mpr ⟨hv,hn⟩))
  have hQsupport : (∑ v ∈ S,g v*(g v+1))=∑ v ∈ U,g v*(g v+1) :=
    Finset.sum_subset hSU (by
      intro v hv hn
      rw [hzero v (Finset.mem_sdiff.mpr ⟨hv,hn⟩)]
      simp)
  have hcauchy := gap_cauchy S g
  rw [hDsupport,hQsupport] at hcauchy
  change dsum^2+S.card*dsum≤S.card*Q at hcauchy
  have horder := deficiency_bound_of_size (d:=a+7)
    (fun F W hf' hm' hn' => ShenFourthStrip.order_to_top hf' hm' hn' (by omega : 1≤a))
    (hf.mono_set hUV) hret hne
  change (2*a+8)*(a+7)≤K at horder
  have hquad := deficiency_quadratic_bound (d:=a+7) (r:=a+4)
    (B:=(a+7)*(a+4)-1) (by omega : (a+4)+(a+4)≤2*a+8)
    (fun F W hf' hm' hn' x hx => by
      have hg := ShenFourthStrip.radius_R_growth hf' hm' hx
      omega)
    (hf.mono_set hUV) hret hne
  change Q+2*K*((a+7)*(a+4)-1)≤K*(K+1) at hquad
  have hbpos : 0<(a+7)*(a+4) := by positivity
  have hpair := quadratic_native_form (by omega : 1≤(a+7)*(a+4)) hquad
  rcases (by omega : e=0 ∨ e=1) with he0|he1
  · have hc0 : S.card=a+7 := by omega
    have ht0 : T.card=a+6 := by omega
    have hU0 : U.card=(a+7)*(a+3) := by omega
    rw [hc0,ht0] at hbudget
    rw [hc0] at hcauchy
    apply quadratic_case_zero (s:=a+7) (D:=dsum) (K:=K) (Q:=Q) (by omega)
    · rw [show a+7-2=a+5 by omega]
      nlinarith only [horder,hKdef,hU0]
    · rw [show a+7-3=a+4 by omega]
      nlinarith only [hbudget,hH,hKdef,hU0]
    · simpa only [show a+7-3=a+4 by omega] using hpair
    · exact hcauchy
  · have hc1 : S.card=(a+7)+1 := by omega
    have ht1 : T.card=a+5 := by omega
    have hU1 : U.card=(a+7)*(a+3)+1 := by omega
    rw [hc1,ht1] at hbudget
    rw [hc1] at hcauchy
    apply quadratic_case_one (s:=a+7) (D:=dsum) (K:=K) (Q:=Q) (by omega)
    · nlinarith only [horder,hKdef,hU1]
    · rw [show a+7-3=a+4 by omega]
      nlinarith only [hbudget,hH,hKdef,hU1]
    · simpa only [show a+7-3=a+4 by omega] using hpair
    · exact hcauchy

#print axioms minimum_table_false
end LeanCH.BR.DotFourthPrefixQuadratic

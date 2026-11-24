import checkpoints.shen_extension.DotTwoPassShellTransport_20261117
import checkpoints.shen_extension.FourthStripTop
import Mathlib.Order.Interval.Finset.Nat

set_option maxHeartbeats 2000000
namespace LeanCH.BR.DotFourthSourceAdapters
open BRq2 BRq3 BR45 ShenFirstStrip
open Classical

private theorem segment {D : CH.Digraph} {V : Finset ℕ} {m : ℕ} {f : ℕ → ℕ}
    (edge : ∀ i, i<m → f (i+1)∈V ∧ D (f i) (f (i+1))=true) (i l : ℕ) (h : i+l≤m) :
    Walk D V (f i) (f (i+l)) l := by
  induction l with
  | zero => simpa using (Walk.refl (D:=D) (W:=V) (f i))
  | succ l ih =>
    obtain ⟨hv,he⟩ := edge (i+l) (by omega)
    exact (ih (by omega)).snoc hv he

/-- The actual number of omissions at the target bounds the length of every
source walk of length at most k, provided its final predecessors lie in the
source container and their return budget fits the cutoff. -/
theorem walk_length_le_target_omissions {D : CH.Digraph} {V K : Finset ℕ} {q i j x y m e : ℕ}
    (hf : QFree D V q) (hx : x∈V) (hK : ball D V x i ⊆ K)
    (hm : m≤i) (hmq : m≤q) (w : Walk D V x y m) (hreturn : j+e+1≤q)
    (hmiss : (K \ ball D V y j).card≤e) : m≤e := by
  by_contra! hlong
  obtain ⟨f,hx0,hyM,edge⟩ := w.toFun
  let I := Finset.Ico (m-(e+1)) m
  have bounds {i} (hi : i∈I) : m-(e+1)≤i ∧ i<m := Finset.mem_Ico.mp hi
  have diff (i j : ℕ) (hlt : i<j) (hj : j≤m) : f i≠f j := by
    intro he
    have h := segment edge i (j-i) (by omega)
    rw [show i+(j-i)=j by omega,← he] at h
    exact hf _ (j-i) (by omega) (by omega) h
  have inj : Set.InjOn f (I : Set ℕ) := by
    intro i hi j hj he
    rcases lt_trichotomy i j with h|h|h
    · exact (diff i j h (bounds hj).2.le he).elim
    · exact h
    · exact (diff j i h (bounds hi).2.le he.symm).elim
  have sub : I.image f ⊆ K \ ball D V y j := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hlo,hhi⟩ := bounds hi
    have wp := segment edge 0 i (by omega)
    simp only [Nat.zero_add,hx0] at wp
    have hv : f i∈V := wp.end_mem_or.elim (fun he => he ▸ hx) id
    refine Finset.mem_sdiff.mpr ⟨hK (mem_ball.mpr ⟨hv,i,by omega,wp⟩),?_⟩
    intro hb
    obtain ⟨_,r,hr,wr⟩ := mem_ball.mp hb
    have ws := segment edge i (m-i) (by omega)
    rw [show i+(m-i)=m by omega,hyM] at ws
    exact hf y (r+(m-i)) (by omega) (by omega) (wr.append ws)
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj] at hc
  have hcard : I.card=e+1 := by dsimp [I]; rw [Nat.card_Ico]; omega
  omega

theorem walk_length_le_omissions {D : CH.Digraph} {V K : Finset ℕ} {q k x y m e : ℕ}
    (hf : QFree D V q) (hx : x∈V) (hK : ball D V x k ⊆ K)
    (hm : m≤k) (w : Walk D V x y m) (hreturn : k+e+1≤q)
    (hmiss : (K \ ball D V y k).card≤e) : m≤e :=
  walk_length_le_target_omissions hf hx hK hm (by omega) w hreturn hmiss

/-- Select e+2 roots. Each reaches another root, and every such step lifts
to at most e original arcs. The finite sink theorem gives the contradiction. -/
theorem container_false {D : CH.Digraph} {V C K : Finset ℕ} {q k e : ℕ}
    (hf : QFree D V q) (hCV : C⊆V) (hCK : C⊆K)
    (hballs : ∀ h∈C, ball D V h k⊆K)
    (hmiss : ∀ h∈C, (K \ ball D V h k).card≤e)
    (hc : e+2≤C.card) (hreturn : k+e+1≤q) (hcycle : e*(e+2)≤q) : False := by
  obtain ⟨A,hAC,hA⟩ := Finset.exists_subset_card_eq hc
  let E : CH.Digraph := fun x y => decide (x≠y ∧ y∈ball D V x k)
  have hfE : QFree E A (e+2) := by
    apply DotTwoPassShellTransport.qfree_of_bounded_arc_lift hf hcycle
    intro x hx y hy hxy
    obtain ⟨hne,hb⟩ := of_decide_eq_true hxy
    obtain ⟨_,m,hm,wm⟩ := mem_ball.mp hb
    refine ⟨m,?_,walk_length_le_omissions hf (hCV (hAC hx)) (hballs x (hAC hx))
      hm wm hreturn (hmiss y (hAC hy)),wm⟩
    cases m with
    | zero => cases wm; exact (hne rfl).elim
    | succ m => omega
  obtain ⟨x,hx,hsink⟩ := exists_sink hfE (Finset.card_pos.mp (by omega)) hA.le
  have sub : A⊆insert x (K \ ball D V x k) := by
    intro y hy
    by_cases he : y=x
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hCK (hAC hy),
        fun hb => hsink y hy (by simp [E,Ne.symm he,hb])⟩))
  have hh := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  have := hmiss x (hAC hx)
  omega

#print axioms walk_length_le_omissions
#print axioms container_false

end LeanCH.BR.DotFourthSourceAdapters


set_option maxHeartbeats 2000000
namespace LeanCH.BR.DotFourthSourceAdapters
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenFourthStrip DotTwoPassShellTransport
open Classical

theorem prefix_cells {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hu : u ∈ V) (hk : k+2≤2*a+8)
    (ht : (shell D V (k+1) u).card<a+7) :
    (2*a+8)*(a+7)+holes D V (k+1) u ≤
      ((ball D V u (k+1)).erase u).card+
        (layer D V (k+1) u).card*(shell D V (k+1) u).card := by
  have hret := minOut_prefix_erase (d:=1) hf hu (by omega : (k+1)+1≤2*a+8) hm
    (by change 1+(shell D V (k+1) u).card≤a+7; omega)
  have hh := PrefixTensor.same_degree_missing_capacity hf hm hu (by omega : 1≤a+7)
    (fun F W hF hM hN => ShenFourthStrip.order_to_top hF hM hN ha) hk hret
  simpa only [holes,layer,shell,Nat.add_sub_cancel] using hh

theorem top_R2_strong {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V) :
    (a+7)*(a+6)≤(ball D V u (a+6)).card+3 := by
  have hR := top_R_growth hf hm hu hn.le (by omega)
  have hR1 := top_R1_growth hf hm hu (by omega)
  let t := (shell D V (a+5) u).card
  let c := (layer D V (a+5) u).card
  let N := ((ball D V u (a+5)).erase u).card
  have htadd : t+(ball D V u (a+5)).card=(ball D V u (a+6)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hcadd : c+(ball D V u (a+4)).card=(ball D V u (a+5)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hNadd : N+1=(ball D V u (a+5)).card := by
    have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+5))
    have hp : 0<(ball D V u (a+5)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    dsimp [N]
    omega
  obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hR1
  by_contra! hbad
  have hte : t+e≤a+5 := by nlinarith
  have hce : c≤a+5+e := by nlinarith
  have hNe : N+3=(a+7)*(a+5)+e := by omega
  have hp := prefix_cells (k:=a+4) (by omega) hf hm hu (by omega)
    (by change t<a+7; omega)
  change (2*a+8)*(a+7)+holes D V (a+5) u≤N+c*t at hp
  have hmul := Nat.mul_le_mul_right t hce
  have hexact : t+e=a+5 := by
    by_contra hne
    have ht2 : t+e≤a+4 := by omega
    have hp2 := Nat.mul_le_mul_left (a+5+e) ht2
    nlinarith [Nat.zero_le (e*e)]
  have he01 : e≤1 := by
    have hp2 := congrArg (fun z : ℕ => (a+5+e)*z) hexact
    by_contra! he2
    have hh := Nat.mul_le_mul_left e he2
    nlinarith only [hp,hmul,hNe,hp2,hh,he2]
  have hH : holes D V (a+5) u≤1 := by
    have hp2 := congrArg (fun z : ℕ => (a+5+e)*z) hexact
    have ee : e*e=e := by
      rcases (by omega : e=0 ∨ e=1) with he0|he1
      · simp [he0]
      · simp [he1]
    nlinarith only [hp,hmul,hNe,hp2,ee]
  have hcE : c=a+5+e := by
    by_contra hne
    have hc2 : c+1≤a+5+e := by omega
    have hp2 := Nat.mul_le_mul_right t hc2
    have hp3 := congrArg (fun z : ℕ => (a+5+e)*z) hexact
    have ee : e*e=e := by
      rcases (by omega : e=0 ∨ e=1) with he0|he1
      · simp [he0]
      · simp [he1]
    nlinarith only [hp,hNe,hp2,hp3,ee,hexact,he01,ha]
  have hRE : (ball D V u (a+4)).card=(a+7)*(a+4) := by nlinarith
  let C := fullColumns D V (a+5) u
  let K := V \ (ball D V u (a+5)).erase u
  have hCV : C ⊆ V := fun _ hh => shell_subset (Finset.mem_filter.mp hh).1
  have hcard : 5≤C.card := by
    have hb := full_columns_bound (D:=D) (V:=V) (R:=a+5) (u:=u)
    change t≤C.card+holes D V (a+5) u at hb
    omega
  have hK : K.card+e=(a+7)*(a+3)+3 := by
    have hh := Finset.card_sdiff_add_card_eq_card
      ((Finset.erase_subset u (ball D V u (a+5))).trans ball_subset)
    change K.card+N=V.card at hh
    nlinarith
  have hballs : ∀ h ∈ C, ball D V h (a+3) ⊆ K := by
    apply full_bank_avoids (k:=a+4) hf hu (by omega)
    intro y hy
    have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+4))
    have hl := top_R_growth hf hm (ball_subset (Finset.mem_of_mem_erase hy)) hn.le (by omega)
    have hb : 0<(a+7)*(a+4) := by positivity
    omega
  have hCK : C ⊆ K := fun h hh => hballs h hh (self_mem_ball (hCV hh))
  apply container_false (e:=3) hf hCV hCK hballs ?_ hcard (by omega) (by omega)
  intro h hh
  have hc := Finset.card_sdiff_add_card_eq_card (hballs h hh)
  have hl := radius_Rm1_growth hf hm (hCV hh)
  omega

#print axioms prefix_cells
#print axioms top_R2_strong
end LeanCH.BR.DotFourthSourceAdapters


set_option maxHeartbeats 2000000
namespace LeanCH.BR.DotFourthSourceAdapters
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenFourthStrip DotTwoPassShellTransport
open Classical

theorem top_inner_strong {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V) :
    (a+7)*(a+3)+1≤(ball D V u (a+3)).card := by
  have hlow := radius_Rm1_growth hf hm hu
  by_contra! hbad
  have hz : (ball D V u (a+3)).card=(a+7)*(a+3) := by omega
  let t := (shell D V (a+2) u).card
  let c := (layer D V (a+2) u).card
  let N := ((ball D V u (a+2)).erase u).card
  have htadd : t+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hcadd : c+(ball D V u (a+1)).card=(ball D V u (a+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hNadd : N+1=(ball D V u (a+2)).card := by
    have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+2))
    have hp : 0<(ball D V u (a+2)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    dsimp [N]
    omega
  have hi := ShenFourthStrip.inner_growth hf hm hu (a+2) (by omega) (by omega)
  have hi2 := ShenFourthStrip.inner_growth hf hm hu (a+1) (by omega) (by omega)
  have ht : t≤a+6 := by nlinarith
  have hc : c+t+1≤2*(a+7) := by nlinarith
  have hp := prefix_cells (k:=a+1) (by omega) hf hm hu (by omega)
    (by change t<a+7; omega)
  change (2*a+8)*(a+7)+holes D V (a+2) u≤N+c*t at hp
  have hmul := Nat.mul_le_mul_right t hc
  have htE : t=a+6 := by
    by_contra hne
    have htl : t≤a+5 := by omega
    have hs : 0≤((a:ℤ)+6-t)*((a:ℤ)+5-t) := mul_nonneg (by omega) (by omega)
    zify at htadd hc ht hp hmul htl hNadd hz
    nlinarith
  have hcE : c=a+7 := by nlinarith
  have hH : holes D V (a+2) u=0 := by nlinarith
  have hsmall : (ball D V u (a+1)).card=(a+7)*(a+1)+1 := by nlinarith
  have hU : N=(a+7)*(a+2) := by nlinarith
  let C := fullColumns D V (a+2) u
  let K := V \ (ball D V u (a+2)).erase u
  have hCV : C ⊆ V := fun _ hh => shell_subset (Finset.mem_filter.mp hh).1
  have hcard : 5≤C.card := by
    have hb := full_columns_bound (D:=D) (V:=V) (R:=a+2) (u:=u)
    change t≤C.card+holes D V (a+2) u at hb
    omega
  have hK : K.card=(a+7)*(a+6) := by
    have hh := Finset.card_sdiff_add_card_eq_card
      ((Finset.erase_subset u (ball D V u (a+2))).trans ball_subset)
    change K.card+N=V.card at hh
    nlinarith only [hh,hU,hn]
  have hballs : ∀ h ∈ C, ball D V h (a+6) ⊆ K := by
    apply full_bank_avoids (k:=a+1) hf hu (by omega)
    intro y hy
    have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+1))
    have hl := ShenFourthStrip.inner_growth hf hm
      (ball_subset (Finset.mem_of_mem_erase hy)) (a+1) (by omega) (by omega)
    omega
  have hCK : C ⊆ K := fun h hh => hballs h hh (self_mem_ball (hCV hh))
  apply container_false (e:=3) hf hCV hCK hballs ?_ hcard (by omega) (by omega)
  intro h hh
  have hc := Finset.card_sdiff_add_card_eq_card (hballs h hh)
  have hl := top_R2_strong ha hf hm hn (hCV hh)
  omega

theorem top_outer_strong {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V) :
    (a+7)*(a+5)≤(ball D V u (a+5)).card+1 :=
  top_R1_of_inner hf hm hu hn.le (by omega) (top_inner_strong ha hf hm hn hu)

theorem exists_minimum_root {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+8)*(a+7)) :
    ∃ u ∈ V, (ball D V u (a+4)).card=(a+7)*(a+4) := by
  by_contra hnone
  push Not at hnone
  have hballs (u) (hu : u ∈ V) : (a+7)*(a+4)+1≤(ball D V u (a+4)).card := by
    have hl := top_R_growth hf hm hu hn.le (by omega)
    have he := hnone u hu
    omega
  have hc := card_ge_of_two_balls hf (by omega : (a+4)+(a+4)≤2*a+8) hballs hballs hne
  nlinarith

#print axioms top_inner_strong
#print axioms top_outer_strong
#print axioms exists_minimum_root
end LeanCH.BR.DotFourthSourceAdapters


namespace LeanCH.BR.DotFourthSourceAdapters
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenFourthStrip DotTwoPassShellTransport
open Classical

theorem minimum_root_table {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V)
    (hR : (ball D V u (a+4)).card=(a+7)*(a+4)) :
    ∃ e : ℕ, e≤1 ∧
      (ball D V u (a+3)).card=(a+7)*(a+3)+1+e ∧
      (ball D V u (a+2)).card=(a+7)*(a+2)+1 := by
  have hprev := top_inner_strong ha hf hm hn hu
  obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hprev
  let t := (shell D V (a+3) u).card
  let c := (layer D V (a+3) u).card
  let N := ((ball D V u (a+3)).erase u).card
  let H := holes D V (a+3) u
  have htadd : t+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hcadd : c+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hNadd : N+1=(ball D V u (a+3)).card := by
    have hh := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+3))
    have hp : 0<(ball D V u (a+3)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    dsimp [N]
    omega
  have hi := ShenFourthStrip.inner_growth hf hm hu (a+2) (by omega) (by omega)
  have ht : t+e=a+6 := by nlinarith only [htadd,hR,he]
  have hc : c≤a+7+e := by nlinarith only [hcadd,hi,he]
  have hN : N=(a+7)*(a+3)+e := by omega
  have hp := prefix_cells (k:=a+2) (by omega) hf hm hu (by omega)
    (by change t<a+7; omega)
  change (2*a+8)*(a+7)+H≤N+c*t at hp
  have hprod := congrArg (fun z : ℕ => (a+7+e)*z) ht
  have hbudget (d : ℕ) (hd : c+d≤a+7+e) : H+e*e+d*t≤a+7 := by
    have hmul := Nat.mul_le_mul_right t hd
    nlinarith only [hp,hN,hprod,hmul]
  have hH := hbudget 0 (by omega)
  have he01 : e≤1 := by
    by_contra! he2
    have hsq : e+2≤e*e := by
      have hh := Nat.mul_le_mul_left e he2
      omega
    have hcE : c=a+7+e := by
      by_contra hne
      have hh := hbudget 1 (by omega)
      nlinarith only [hh,ht,hsq]
    have hsmall : (ball D V u (a+2)).card=(a+7)*(a+2)+1 := by
      nlinarith only [hcadd,he,hcE]
    let C := fullColumns D V (a+3) u
    let K := V \ (ball D V u (a+3)).erase u
    have hCV : C ⊆ V := fun _ hh => shell_subset (Finset.mem_filter.mp hh).1
    have hC : C.Nonempty := by
      have hb := full_columns_bound (D:=D) (V:=V) (R:=a+3) (u:=u)
      change t≤C.card+H at hb
      exact Finset.card_pos.mp (by nlinarith only [hb,hH,hsq,ht])
    have hK : K.card+e=(a+7)*(a+5) := by
      have hh := Finset.card_sdiff_add_card_eq_card
        ((Finset.erase_subset u (ball D V u (a+3))).trans ball_subset)
      change K.card+N=V.card at hh
      nlinarith only [hh,hN,hn]
    have hballs : ∀ h ∈ C, ball D V h (a+5) ⊆ K := by
      apply full_bank_avoids (k:=a+2) hf hu (by omega)
      intro y hy
      have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+2))
      have hl := ShenFourthStrip.inner_growth hf hm
        (ball_subset (Finset.mem_of_mem_erase hy)) (a+2) (by omega) (by omega)
      omega
    obtain ⟨h,hh⟩ := hC
    have hcap := Finset.card_le_card (hballs h hh)
    have hlow := top_outer_strong ha hf hm hn (hCV hh)
    omega
  have hcE : c=a+7+e := by
    by_contra hne
    have hc1 : c+1≤a+7+e := by omega
    have hb1 := hbudget 1 hc1
    have hee : e*e=e := by
      rcases (by omega : e=0 ∨ e=1) with he0|he1
      · simp [he0]
      · simp [he1]
    have hH1 : H≤1 := by nlinarith only [hb1,ht,hee]
    have hc1E : c+1=a+7+e := by
      by_contra hneq
      have hb2 := hbudget 2 (by omega)
      nlinarith only [hb2,ht,hee,he01,ha]
    have hsmall : (ball D V u (a+2)).card=(a+7)*(a+2)+2 := by
      nlinarith only [hcadd,he,hc1E]
    let C := fullColumns D V (a+3) u
    let U := (ball D V u (a+3)).erase u
    let A := (ball D V u (a+2)).erase u
    have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hCK : C ⊆ V \ U := by
      intro h hh
      have hT := (Finset.mem_filter.mp hh).1
      exact Finset.mem_sdiff.mpr ⟨shell_subset hT,fun hU =>
        (Finset.mem_sdiff.mp hT).2 (Finset.mem_of_mem_erase hU)⟩
    have hC4 : 4≤C.card := by
      have hb := full_columns_bound (D:=D) (V:=V) (R:=a+3) (u:=u)
      change t≤C.card+H at hb
      omega
    have hA : A.card=(a+7)*(a+2)+1 := by
      have he := Finset.card_erase_of_mem (self_mem_ball hu : u ∈ ball D V u (a+2))
      dsimp [A]
      omega
    have hY (y) (hy : y ∈ U) (hb : ∃ h ∈ C, h ∉ ball D V y (a+3)) :
        ball D V y (a+2)=A := by
      obtain ⟨h,hh,hbad⟩ := hb
      have htrap := full_column_bad_ball (k:=a+2) hf hu (by omega) hh hy hbad
      apply Finset.eq_of_subset_of_card_le htrap
      rw [hA]
      exact ShenFourthStrip.inner_growth hf hm (hUV hy) (a+2) (by omega) (by omega)
    have hK : (V \ U).card+e=(a+7)*(a+5) := by
      have hh := Finset.card_sdiff_add_card_eq_card hUV
      change (V \ U).card+N=V.card at hh
      nlinarith only [hh,hN,hn]
    apply exceptional_bank2_false (r:=a+3) (L:=a+5) (k0:=a+2)
      hf hUV hCK (by omega) (by omega) (by omega) (by omega) hY ?_ hC4
    intro h hh
    have hl := top_outer_strong ha hf hm hn (Finset.mem_sdiff.mp (hCK hh)).1
    omega
  refine ⟨e,he01,he,?_⟩
  nlinarith only [hcadd,he,hcE]

theorem source_minimum_packet {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 5≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+8)*(a+7)) :
    (∀ v ∈ V, (a+7)*(a+3)+1≤(ball D V v (a+3)).card) ∧
    (∀ v ∈ V, (a+7)*(a+5)≤(ball D V v (a+5)).card+1) ∧
    ∃ u ∈ V, ∃ e : ℕ, e≤1 ∧
      (ball D V u (a+4)).card=(a+7)*(a+4) ∧
      (ball D V u (a+3)).card=(a+7)*(a+3)+1+e ∧
      (ball D V u (a+2)).card=(a+7)*(a+2)+1 := by
  obtain ⟨u,hu,hR⟩ := exists_minimum_root ha hf hm hne hn
  obtain ⟨e,he,hprev,hinner⟩ := minimum_root_table ha hf hm hn hu hR
  exact ⟨fun v hv => top_inner_strong ha hf hm hn hv,
    fun v hv => top_outer_strong ha hf hm hn hv,u,hu,e,he,hR,hprev,hinner⟩

#print axioms minimum_root_table
#print axioms source_minimum_packet
end LeanCH.BR.DotFourthSourceAdapters

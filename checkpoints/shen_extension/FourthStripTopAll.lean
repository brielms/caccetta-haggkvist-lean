import checkpoints.shen_extension.DotFourthPrefixQuadratic_20261118
import checkpoints.shen_extension.DotFourthSourceAdapters_20261118

/-!
Fourth strip q = 2s-6 at the top order n = qs for EVERY degree s ≥ 9.

New generic ingredients (no degree-specific numerals):
* `universal_R_floor`: in every q-free host (any order) with minimum
  out-degree s ≥ 8, every (s-3)-ball has at least s(s-3) vertices.
  The clone completion of the punctured (s-4)-prefix of a bad root has
  order exactly qs and its pair count contradicts Cauchy.
* `three_omission_container_false`: five bank vertices whose k-balls omit at
  most three labels of a common container are impossible for q ≥ 12.
* `minimum_table_false_sharp`: the old minimum-root table, re-run with the
  sharp radius floor in the completed host; closes s ≥ 9.
-/

set_option maxHeartbeats 2000000
namespace LeanCH.BR.FourthStripTopAll
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip ShenFourthStrip
open DotTwoPassShellTransport DotClonePairCompletion DotFourthPrefixQuadratic
open DotFourthSourceAdapters
open Classical

theorem floor_arith {a b Sc Tc w dsum Q K U : ℕ} (ha : 1≤a)
    (hc : Sc≤a+6+b) (hw : Tc+b+w=a+6) (hUc : U+1=(a+7)*(a+3)+b)
    (hD : dsum≤Sc*Tc) (hK : K=U+dsum) (horder : (2*a+8)*(a+7)≤K)
    (hpair : Q+2*K*((a+7)*(a+4))≤K*(K+3))
    (hcauchy : dsum^2+Sc*dsum≤Sc*Q) : False := by
  have hST := Nat.mul_le_mul_right Tc hc
  have hw' := congrArg (fun z => (a+6+b)*z) hw
  have hid : (a+6+b)*Tc+b*b+(a+6+b)*w=(a+6)*(a+6) := by nlinarith [hw']
  have hid2 : (a+7)*(a+3)+(a+6)*(a+6)=(2*a+8)*(a+7)+1 := by ring
  have hbb : b*b+(a+6+b)*w≤b := by omega
  have hb1 : b≤1 := by
    by_contra! h
    have := Nat.mul_le_mul_left b h
    omega
  have hw0 : w=0 := by
    by_contra h
    have h1 : 1≤w := by omega
    have := Nat.mul_le_mul_left (a+6+b) h1
    omega
  subst hw0
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  rcases (by omega : b=0 ∨ b=1) with rfl|rfl
  · have hT : Tc=a+6 := by omega
    subst hT
    have hS6 : Sc≤a+6 := by omega
    have hm6 := Nat.mul_le_mul_right (a+6) hS6
    have hd : dsum=(a+6)*(a+6) := by omega
    have hK' : K=2*((a+7)*(a+4)) := by omega
    subst hK'
    have hQ : Q≤6*((a+7)*(a+4)) := by nlinarith
    have h1 := Nat.mul_le_mul hS6 hQ
    subst hd
    have hpos : 0≤Sc*((a+6)*(a+6)) := Nat.zero_le _
    obtain ⟨x,rfl⟩ : ∃ x,a=x+1 := ⟨a-1,by omega⟩
    nlinarith [Nat.zero_le (x^2),Nat.zero_le (x^3),Nat.zero_le (x^4)]
  · have hT : Tc=a+5 := by omega
    subst hT
    have hS7 : Sc≤a+7 := by omega
    have hm5 := Nat.mul_le_mul_right (a+5) hS7
    have hex : (a+7)*(a+3)+(a+7)*(a+5)=2*((a+7)*(a+4)) := by ring
    have hd : dsum=(a+7)*(a+5) := by omega
    have hK' : K=2*((a+7)*(a+4)) := by omega
    subst hK'
    have hQ : Q≤6*((a+7)*(a+4)) := by nlinarith
    have h1 := Nat.mul_le_mul hS7 hQ
    subst hd
    obtain ⟨x,rfl⟩ : ∃ x,a=x+1 := ⟨a-1,by omega⟩
    nlinarith [Nat.zero_le (x^2),Nat.zero_le (x^3),Nat.zero_le (x^4)]

/-- Universal radius floor at cutoff q = 2s-6, in hosts of EVERY order:
the inclusive (s-3)-ball has at least s(s-3) vertices (s = a+7 ≥ 8).
Proof: the clone completion of the punctured (s-4)-prefix of a bad root
has order exactly qs, and its quadratic pair count contradicts Cauchy. -/
theorem universal_R_floor {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 1≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V,a+7≤(outN D V v).card) (hu : u ∈ V) :
    (a+7)*(a+4)≤(ball D V u (a+4)).card := by
  by_contra! hbad
  have hi := ShenFourthStrip.inner_growth hf hm hu (a+2) (by omega) (by omega)
  have hRm := ShenFourthStrip.radius_Rm1_growth hf hm hu
  let U := (ball D V u (a+3)).erase u
  let S := layer D V (a+3) u
  let T := shell D V (a+3) u
  let g := fun v => (a+7)-(outN D U v).card
  let dsum := ∑ v ∈ U,g v
  let Q := ∑ v ∈ U,g v*(g v+1)
  let K := U.card+dsum
  have hKdef : K=U.card+dsum := rfl
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hU : U.card+1=(ball D V u (a+3)).card := by
    have hh := Finset.card_erase_of_mem
      (self_mem_ball hu : u ∈ ball D V u (a+3))
    have hp : 0<(ball D V u (a+3)).card := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
    dsimp only [U]
    omega
  have hS : S.card+(ball D V u (a+2)).card=(ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hT : T.card+(ball D V u (a+3)).card=(ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hexq : (a+7)*(a+4)=(a+7)*(a+3)+(a+7) := by ring
  have hexr : (a+7)*(a+3)=(a+7)*(a+2)+(a+7) := by ring
  obtain ⟨b,hb⟩ : ∃ b,(ball D V u (a+3)).card=(a+7)*(a+3)+b :=
    ⟨(ball D V u (a+3)).card-(a+7)*(a+3),by omega⟩
  have hc : S.card≤a+6+b := by omega
  obtain ⟨w,hw⟩ : ∃ w,T.card+b+w=a+6 := ⟨a+6-T.card-b,by omega⟩
  have hUc : U.card+1=(a+7)*(a+3)+b := by omega
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
    (fun F W hf' hm' hn' => ShenFourthStrip.order_to_top hf' hm' hn' ha)
    (hf.mono_set hUV) hret hne
  change (2*a+8)*(a+7)≤K at horder
  have hquad := deficiency_quadratic_bound (d:=a+7) (r:=a+4)
    (B:=(a+7)*(a+4)-1) (by omega : (a+4)+(a+4)≤2*a+8)
    (fun F W hf' hm' hn' x hx => by
      have hg := ShenFourthStrip.radius_R_growth hf' hm' hx
      omega)
    (hf.mono_set hUV) hret hne
  change Q+2*K*((a+7)*(a+4)-1)≤K*(K+1) at hquad
  have hpair := quadratic_native_form (Nat.mul_pos (by omega) (by omega) : 0<(a+7)*(a+4)) hquad
  have hD : dsum≤S.card*T.card := le_trans (Nat.le_add_right _ _) hbudget
  exact floor_arith ha hc hw hUc hD hKdef horder hpair hcauchy


/-- Five bank vertices whose k-balls share a container with at most three
omissions each cannot exist once q ≥ 12 and k+4 ≤ q.
Every 4-subset has a sink in the 3-step reach graph; the sink map is a
bijection, so every bank vertex omits only bank vertices; a sink of the
original graph on the five vertices then closes a cycle. -/
theorem three_omission_container_false {D : CH.Digraph} {V K C : Finset ℕ} {q k : ℕ}
    (hf : QFree D V q) (hk : k+4≤q) (hq : 12≤q) (hCV : C ⊆ V) (hCK : C ⊆ K)
    (hballs : ∀ h ∈ C, ball D V h k ⊆ K)
    (hmiss : ∀ h ∈ C, (K \ ball D V h k).card≤3)
    (hcard : 5≤C.card) : False := by
  obtain ⟨A,hAC,hA⟩ := Finset.exists_subset_card_eq hcard
  have hAV : A ⊆ V := hAC.trans hCV
  let E : CH.Digraph := fun x y => decide (x≠y ∧ y∈ball D V x k)
  have hE (B : Finset ℕ) (hB : B ⊆ A) : QFree E B 4 := by
    apply qfree_of_bounded_arc_lift (e:=3) hf (by omega)
    intro x hx y hy hxy
    obtain ⟨hne,hb⟩ := of_decide_eq_true hxy
    obtain ⟨_,m,hm,wm⟩ := mem_ball.mp hb
    refine ⟨m,?_,walk_length_le_omissions hf (hCV (hAC (hB hx)))
      (hballs x (hAC (hB hx))) hm wm (by omega) (hmiss y (hAC (hB hy))),wm⟩
    cases m with
    | zero => cases wm; exact (hne rfl).elim
    | succ m => omega
  -- the sink of A minus z
  have key (z) (hz : z ∈ A) : ∃ t, t ∈ A ∧ t≠z ∧
      (∀ y ∈ A, y≠z → y∈ball D V t k → y=t) ∧ z∈ball D V t k := by
    have hcard4 : (A.erase z).card=4 := by rw [Finset.card_erase_of_mem hz,hA]
    obtain ⟨t,ht,hsink⟩ := exists_sink (hE (A.erase z) (Finset.erase_subset _ _))
      (Finset.card_pos.mp (by omega)) (by omega)
    obtain ⟨htz,htA⟩ := Finset.mem_erase.mp ht
    have hno (y) (hy : y ∈ A) (hyz : y≠z) (hb : y∈ball D V t k) : y=t := by
      by_contra hyt
      exact hsink y (Finset.mem_erase.mpr ⟨hyz,hy⟩)
        (decide_eq_true ⟨Ne.symm hyt,hb⟩)
    refine ⟨t,htA,htz,hno,?_⟩
    by_contra hzb
    have hsub : A.erase t ⊆ K \ ball D V t k := by
      intro y hy
      obtain ⟨hyt,hyA⟩ := Finset.mem_erase.mp hy
      refine Finset.mem_sdiff.mpr ⟨hCK (hAC hyA),fun hb => ?_⟩
      by_cases hyz : y=z
      · exact hzb (hyz ▸ hb)
      · exact hyt (hno y hyA hyz hb)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem htA,hA] at hc
    have := hmiss t (hAC htA)
    omega
  -- every vertex of A omits only vertices of A
  have sat (t z) (hz : z ∈ A) (ht : t ∈ A) (htz : t≠z)
      (hno : ∀ y ∈ A, y≠z → y∈ball D V t k → y=t) :
      ∀ v ∈ K, v∉ball D V t k → v ∈ A := by
    intro v hvK hvb
    by_contra hvA
    have hsub : insert v ((A.erase z).erase t) ⊆ K \ ball D V t k := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact Finset.mem_sdiff.mpr ⟨hvK,hvb⟩
      · obtain ⟨hyt,hy'⟩ := Finset.mem_erase.mp hy
        obtain ⟨hyz,hyA⟩ := Finset.mem_erase.mp hy'
        exact Finset.mem_sdiff.mpr ⟨hCK (hAC hyA),fun hb => hyt (hno y hyA hyz hb)⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (fun h => hvA
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨htz,ht⟩),
      Finset.card_erase_of_mem hz,hA] at hc
    have := hmiss t (hAC ht)
    omega
  choose! τ hτ using key
  have hinj : Set.InjOn τ (A : Set ℕ) := by
    intro z hz z' hz' he
    by_contra hne
    obtain ⟨htA,htz,hno,_⟩ := hτ z hz
    obtain ⟨_,htz',_,hb'⟩ := hτ z' hz'
    rw [← he] at htz' hb'
    exact htz' (hno z' hz' (Ne.symm hne) hb').symm
  have himage : A.image τ=A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      exact (hτ z hz).1
    · rw [Finset.card_image_of_injOn hinj]
  have hsurj (x) (hx : x ∈ A) : ∃ z ∈ A, τ z=x := by
    rw [← himage] at hx
    exact Finset.mem_image.mp hx
  obtain ⟨x,hx,hsinkD⟩ := exists_sink (hf.mono_set hAV)
    (Finset.card_pos.mp (by omega)) (by omega : A.card≤q)
  obtain ⟨z,hz,hzx⟩ := hsurj x hx
  obtain ⟨htA,htz,hno,hzb⟩ := hτ z hz
  rw [hzx] at htA htz hno hzb
  obtain ⟨z',hz',hze⟩ := hsurj z hz
  obtain ⟨hzA',hzz',hno',_⟩ := hτ z' hz'
  rw [hze] at hzz' hno'
  have hsatz := sat z z' hz' hz hzz' hno'
  obtain ⟨hzV,m,hm,w⟩ := mem_ball.mp hzb
  cases m with
  | zero => cases w; exact htz rfl
  | succ n =>
    obtain ⟨v,wv,_,hvz⟩ := w.unsnoc
    have hvV : v ∈ V := by
      rcases wv.end_mem_or with h|h
      · exact h ▸ hAV htA
      · exact h
    have hvb : v ∈ ball D V x k := mem_ball.mpr ⟨hvV,n,by omega,wv⟩
    have hvK : v ∈ K := hballs x (hAC htA) hvb
    have hvnot : v ∉ ball D V z k := by
      intro hb
      obtain ⟨_,i,hi,wi⟩ := mem_ball.mp hb
      exact hf z (i+1) (by omega) (by omega) (wi.snoc hzV hvz)
    have hvA := hsatz v hvK hvnot
    have hvz' : v≠z := by
      intro he
      subst he
      exact hf v 1 (by omega) (by omega) (.step hzV hvz (.refl v))
    have hvx := hno v hvA hvz' hvb
    rw [hvx] at hvz
    exact hsinkD z hz hvz


/-- e = 0 table with the sharp floor B = s(s-3); s = a+7, P = s(s-3). -/
theorem case_zero_sharp {a d Q δ : ℕ} (ha : 2≤a) (hδ : δ≤3)
    (hd : d=(a+7)*(a+5)+δ)
    (hpair : Q+2*(2*((a+7)*(a+4))+δ)*((a+7)*(a+4)) ≤
      (2*((a+7)*(a+4))+δ)*(2*((a+7)*(a+4))+δ+1))
    (hcauchy : d^2+(a+7)*d≤(a+7)*Q) : False := by
  have hK1 : (2*((a+7)*(a+4))+δ)*(2*((a+7)*(a+4))+δ+1) =
      2*(2*((a+7)*(a+4))+δ)*((a+7)*(a+4))+(2*((a+7)*(a+4))+δ)*(δ+1) := by ring
  have hQ : Q≤(2*((a+7)*(a+4))+δ)*(δ+1) := by linarith
  have h := le_trans hcauchy (Nat.mul_le_mul_left (a+7) hQ)
  subst hd
  obtain ⟨x,rfl⟩ : ∃ x,a=x+2 := ⟨a-2,by omega⟩
  rcases (by omega : δ=0 ∨ δ=1 ∨ δ=2 ∨ δ=3) with rfl|rfl|rfl|rfl <;>
    (ring_nf at h; linarith only [h,Nat.zero_le x,Nat.zero_le (x^2),Nat.zero_le (x^3),Nat.zero_le (x^4)])

/-- e = 1 table with the sharp floor. -/
theorem case_one_sharp {a d Q δ : ℕ} (ha : 2≤a) (hδ : δ≤2)
    (hd : d+1=(a+7)*(a+5)+δ)
    (hpair : Q+2*(2*((a+7)*(a+4))+δ)*((a+7)*(a+4)) ≤
      (2*((a+7)*(a+4))+δ)*(2*((a+7)*(a+4))+δ+1))
    (hcauchy : d^2+(a+8)*d≤(a+8)*Q) : False := by
  have hK1 : (2*((a+7)*(a+4))+δ)*(2*((a+7)*(a+4))+δ+1) =
      2*(2*((a+7)*(a+4))+δ)*((a+7)*(a+4))+(2*((a+7)*(a+4))+δ)*(δ+1) := by ring
  have hQ : Q≤(2*((a+7)*(a+4))+δ)*(δ+1) := by linarith
  have h := le_trans hcauchy (Nat.mul_le_mul_left (a+8) hQ)
  obtain ⟨x,rfl⟩ : ∃ x,a=x+2 := ⟨a-2,by omega⟩
  have hd' : d=x^2+16*x+62+δ := by ring_nf at hd ⊢; omega
  subst hd'
  rcases (by omega : δ=0 ∨ δ=1 ∨ δ=2) with rfl|rfl|rfl <;>
    (ring_nf at h; linarith only [h,Nat.zero_le x,Nat.zero_le (x^2),Nat.zero_le (x^3),Nat.zero_le (x^4)])

/-- Full columns impose a lower bound on ACTUAL holes, before completing
the prefix. Coincident suppliers are not counted as distinct. -/
theorem minimum_table_holes_all {a e u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (he : e≤1) (hf : QFree D V (2*a+8))
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
        exact DotTwoPassShellTransport.ball_root_injective_short hf (by omega) (hCV hx) (hCV hy)
          (hxe.trans hye.symm)
      omega
  have hb := full_columns_bound (D:=D) (V:=V) (R:=a+3) (u:=u)
  change (shell D V (a+3) u).card≤C.card+holes D V (a+3) u at hb
  omega

/-- The minimum-root packet is impossible for s ≥ 9 once the universal
radius floor s(s-3) is fed into the completed host. -/
theorem minimum_table_false_sharp {a e u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (he : e≤1) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V,a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V)
    (hR : (ball D V u (a+4)).card=(a+7)*(a+4))
    (hprev : (ball D V u (a+3)).card=(a+7)*(a+3)+1+e)
    (hinner : (ball D V u (a+2)).card=(a+7)*(a+2)+1)
    (houter : ∀ y ∈ V,(a+7)*(a+5)≤(ball D V y (a+5)).card+1) : False := by
  have hsmall (y) (hy : y ∈ V) :
      (a+7)*(a+2)+1≤(ball D V y (a+2)).card :=
    ShenFourthStrip.inner_growth hf hm hy (a+2) (by omega) (by omega)
  have hH := minimum_table_holes_all ha he hf hn hu hR hprev hinner hsmall houter
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
    (B:=(a+7)*(a+4)) (by omega : (a+4)+(a+4)≤2*a+8)
    (fun F W hf' hm' hn' x hx => universal_R_floor (by omega) hf' hm' hx)
    (hf.mono_set hUV) hret hne
  change Q+2*K*((a+7)*(a+4))≤K*(K+1) at hquad
  have hqs : (2*a+8)*(a+7)=2*((a+7)*(a+4)) := by ring
  have hsplit : 2*((a+7)*(a+4))=(a+7)*(a+3)+(a+7)*(a+5) := by ring
  obtain ⟨δ,hδ⟩ : ∃ δ,K=2*((a+7)*(a+4))+δ := ⟨K-2*((a+7)*(a+4)),by omega⟩
  rw [hδ] at hquad
  rcases (by omega : e=0 ∨ e=1) with he0|he1
  · subst he0
    have hc0 : S.card=a+7 := by omega
    have ht0 : T.card=a+6 := by omega
    rw [hc0,ht0] at hbudget
    rw [hc0] at hcauchy
    have hexp : (a+7)*(a+6)=(a+7)*(a+5)+(a+7) := by ring
    have hd : dsum=(a+7)*(a+5)+δ := by omega
    exact case_zero_sharp ha (by omega) hd hquad hcauchy
  · subst he1
    have hc1 : S.card=a+8 := by omega
    have ht1 : T.card=a+5 := by omega
    rw [hc1,ht1] at hbudget
    rw [hc1] at hcauchy
    have hexp : (a+8)*(a+5)=(a+7)*(a+5)+(a+5) := by ring
    have hd : dsum+1=(a+7)*(a+5)+δ := by omega
    exact case_one_sharp ha (by omega) hd hquad hcauchy

theorem top_R2_strong_all {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
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
  apply three_omission_container_false hf (by omega) (by omega) hCV hCK hballs ?_ hcard
  intro h hh
  have hc := Finset.card_sdiff_add_card_eq_card (hballs h hh)
  have hl := radius_Rm1_growth hf hm (hCV hh)
  omega

theorem top_inner_strong_all {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
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
  apply three_omission_container_false hf (by omega) (by omega) hCV hCK hballs ?_ hcard
  intro h hh
  have hc := Finset.card_sdiff_add_card_eq_card (hballs h hh)
  have hl := top_R2_strong_all ha hf hm hn (hCV hh)
  omega

theorem top_outer_strong_all {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V) :
    (a+7)*(a+5)≤(ball D V u (a+5)).card+1 :=
  top_R1_of_inner hf hm hu hn.le (by omega) (top_inner_strong_all ha hf hm hn hu)

theorem exists_minimum_root_all {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
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

theorem minimum_root_table_all {a u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hn : V.card=(2*a+8)*(a+7)) (hu : u ∈ V)
    (hR : (ball D V u (a+4)).card=(a+7)*(a+4)) :
    ∃ e : ℕ, e≤1 ∧
      (ball D V u (a+3)).card=(a+7)*(a+3)+1+e ∧
      (ball D V u (a+2)).card=(a+7)*(a+2)+1 := by
  have hprev := top_inner_strong_all ha hf hm hn hu
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
    have hlow := top_outer_strong_all ha hf hm hn (hCV hh)
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
    have hl := top_outer_strong_all ha hf hm hn (Finset.mem_sdiff.mp (hCK hh)).1
    omega
  refine ⟨e,he01,he,?_⟩
  nlinarith only [hcadd,he,hcE]

theorem source_minimum_packet_all {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V, a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+8)*(a+7)) :
    (∀ v ∈ V, (a+7)*(a+3)+1≤(ball D V v (a+3)).card) ∧
    (∀ v ∈ V, (a+7)*(a+5)≤(ball D V v (a+5)).card+1) ∧
    ∃ u ∈ V, ∃ e : ℕ, e≤1 ∧
      (ball D V u (a+4)).card=(a+7)*(a+4) ∧
      (ball D V u (a+3)).card=(a+7)*(a+3)+1+e ∧
      (ball D V u (a+2)).card=(a+7)*(a+2)+1 := by
  obtain ⟨u,hu,hR⟩ := exists_minimum_root_all ha hf hm hne hn
  obtain ⟨e,he,hprev,hinner⟩ := minimum_root_table_all ha hf hm hn hu hR
  exact ⟨fun v hv => top_inner_strong_all ha hf hm hn hv,
    fun v hv => top_outer_strong_all ha hf hm hn hv,u,hu,e,he,hR,hprev,hinner⟩

/-- The full source at n = qs is excluded for s = a+7 ≥ 9, q = 2s-6. -/
theorem fourth_strip_upper_false_all {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V,a+7≤(outN D V v).card)
    (hne : V.Nonempty) (hn : V.card=(2*a+8)*(a+7)) : False := by
  obtain ⟨_,houter,u,hu,e,he,hR,hprev,hinner⟩ :=
    source_minimum_packet_all ha hf hm hne hn
  exact minimum_table_false_sharp ha he hf hm hn hu hR hprev hinner houter

/-- Arbitrary finite nonempty q-free hosts have order strictly greater than qs. -/
theorem order_fourth_strip_closed_all {a : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (ha : 2≤a) (hf : QFree D V (2*a+8))
    (hm : ∀ v ∈ V,a+7≤(outN D V v).card) (hne : V.Nonempty) :
    (2*a+8)*(a+7)<V.card := by
  have hl := ShenFourthStrip.order_to_top hf hm hne (by omega : 1≤a)
  by_contra! hn
  exact fourth_strip_upper_false_all ha hf hm hne (by omega)

/-- Public fourth-strip statement, degree threshold 9. -/
theorem cycle_fourth_strip_closed_all {s q n : ℕ} {D : CH.Digraph}
    (hs : 9≤s) (hq : q=2*s-6) (hn : 0<n) (hnq : n≤q*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n q := by
  obtain ⟨a,ha⟩ : ∃ a,s=a+7 := ⟨s-7,by omega⟩
  subst s
  have hq' : q=2*a+8 := by omega
  rw [hq'] at hnq ⊢
  by_contra hh
  have ho := order_fourth_strip_closed_all (by omega : 2≤a) (qfree_of_noShort hl hh)
    (fun v hv => Compose.FloorSix.out_card hm (Finset.mem_range.mp hv))
    ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at ho
  omega

#print axioms universal_R_floor
#print axioms three_omission_container_false
#print axioms minimum_table_false_sharp
#print axioms source_minimum_packet_all
#print axioms cycle_fourth_strip_closed_all
end LeanCH.BR.FourthStripTopAll

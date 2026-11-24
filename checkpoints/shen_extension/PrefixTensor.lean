import checkpoints.shen_extension.CommonTensorClosure

/-! Actual prefix incidence budgets, with no fixed degree or cutoff. -/
namespace LeanCH.BR.PrefixTensor
open BRq2 BRq3 BR45 BRsGen
open Classical

/-- An actual prefix rectangle with less than one row's spare budget has
maximal row count and a bank of common outgoing heads. -/
theorem rectangle {q s L k u cmax m : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (hu : u ∈ V) (hs : 2≤s)
    (hlower : ∀ (F : CH.Digraph) (W : Finset ℕ), QFree F W q →
      (∀ v ∈ W, s-1≤(outN F W v).card) → W.Nonempty → L≤W.card)
    (hk : k+2≤q) (ht : (ball D V u (k+2) \ ball D V u (k+1)).card<s)
    (hc : (ball D V u (k+1) \ ball D V u k).card≤cmax)
    (hbudget : ((ball D V u (k+1)).erase u).card+
      cmax*((ball D V u (k+2) \ ball D V u (k+1)).card-1)+m≤
      L+(ball D V u (k+2) \ ball D V u (k+1)).card)
    (hm2 : 2≤m) :
    (ball D V u (k+1) \ ball D V u k).card=cmax ∧
    m≤((ball D V u (k+2) \ ball D V u (k+1)).filter
      (fun h => ∀ v ∈ ball D V u (k+1) \ ball D V u k, D v h=true)).card := by
  let B := ball D V u (k+1)
  let U := B.erase u
  let S := B \ ball D V u k
  let T := ball D V u (k+2) \ B
  let gap := fun v => s-1-(outN D U v).card
  let miss := fun v => T \ outN D T v
  let clip := fun v => min (T.card-1) (miss v).card
  change T.card<s at ht
  change S.card≤cmax at hc
  change U.card+cmax*(T.card-1)+m≤L+T.card at hbudget
  suffices result : S.card=cmax ∧ m≤(T.filter (fun h => ∀ v ∈ S, D v h=true)).card by
    refine ⟨result.1,?_⟩
    have he : T.filter (fun h => ∀ v ∈ S, D v h=true) =
        (ball D V u (k+2) \ ball D V u (k+1)).filter
          (fun h => ∀ v ∈ ball D V u (k+1) \ ball D V u k, D v h=true) := by
      ext h
      simp only [Finset.mem_filter]
      rfl
    rw [← he]
    exact result.2
  have hSU : S ⊆ U := by
    intro v hv
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_erase.mpr ⟨?_,hb⟩
    intro h; subst v
    exact hn (self_mem_ball hu)
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hmin : ∀ v ∈ U, 1≤(outN D U v).card :=
    minOut_prefix_erase hf hu (by omega : (k+1)+1≤q) hm (by change 1+T.card≤s; omega)
  have hne : U.Nonempty := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by have := hm u hu; omega : 0<(outN D V u).card)
    obtain ⟨hvV,huv⟩ := mem_outN.mp hv
    refine ⟨v,Finset.mem_erase.mpr ⟨?_,?_⟩⟩
    · intro he; subst v
      exact loopfree hf (by omega) hu huv
    · exact ball_mono_radius (by omega : 1≤k+1) (mem_ball.mpr ⟨hvV,1,by omega,.step hvV huv (.refl v)⟩)
  have low := deficiency_bound_of_size hlower (hf.mono_set hUV) hmin hne
  change L≤U.card+∑ v ∈ U, gap v at low
  have hz (v) (hv : v ∈ U \ S) : gap v=0 := by
    obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hv
    have hi : v ∈ ball D V u k := by
      by_contra hh
      exact hn (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv,hh⟩)
    have h := (hm v (ball_subset hi)).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by omega) hi))
    change s≤(outN D U v).card at h
    dsimp [gap]; omega
  have hzero := Finset.sum_eq_zero hz
  have hsum := Finset.sum_sdiff hSU (f:=gap)
  have cap (v) (hv : v ∈ S) : gap v+clip v≤T.card-1 := by
    have hsub := outN_prefix_loss hf hu (by omega : (k+1)+1≤q) (hSU hv)
    have hsub' : outN D V v ⊆ outN D U v ∪ outN D T v := by
      intro w hw
      obtain hh|hh := Finset.mem_union.mp (hsub hw)
      · exact Finset.mem_union_left _ hh
      · exact Finset.mem_union_right _ (mem_outN.mpr ⟨hh,(mem_outN.mp hw).2⟩)
    have hcount := (hm v (hUV (hSU hv))).trans
      ((Finset.card_le_card hsub').trans (Finset.card_union_le _ _))
    have hmiss : (miss v).card+(outN D T v).card=T.card :=
      Finset.card_sdiff_add_card_eq_card (fun _ hw => (mem_outN.mp hw).1)
    dsimp only [gap,clip]
    omega
  have hcap := Finset.sum_le_sum cap
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at hcap
  have hsource : L≤U.card+S.card*(T.card-1) := by omega
  have hclips : (∑ v ∈ S,clip v)+m≤T.card := by
    have hmul := Nat.mul_le_mul_right (T.card-1) hc
    omega
  have htp : 1≤T.card := by omega
  have htp' : T.card-1+1=T.card := by omega
  have hmc (v) (hv : v ∈ S) : (miss v).card=clip v := by
    have hle := Finset.single_le_sum (f:=clip) (fun _ _ => Nat.zero_le _) hv
    dsimp only [clip] at *
    omega
  constructor
  · by_contra hne
    have hstep : S.card+1≤cmax := by omega
    have hmul := Nat.mul_le_mul_right (T.card-1) hstep
    nlinarith only [hmul,hbudget,hsource,htp',hm2]
  · have hmSum : (∑ v ∈ S,(miss v).card)+m≤T.card := by
      rw [Finset.sum_congr rfl hmc]
      exact hclips
    have sub : T \ S.biUnion miss ⊆ T.filter (fun h => ∀ v ∈ S, D v h=true) := by
      intro h hh
      obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp hh
      refine Finset.mem_filter.mpr ⟨ht,fun v hv => ?_⟩
      by_contra hb
      exact hn (Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_sdiff.mpr ⟨ht,fun he => hb (mem_outN.mp he).2⟩⟩)
    have hbi : S.biUnion miss ⊆ T := by
      intro h hh
      obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hh
      exact (Finset.mem_sdiff.mp hv).1
    have h1 := Finset.card_biUnion_le (s:=S) (t:=miss)
    have h2 := Finset.card_sdiff_add_card_eq_card hbi
    have h3 := Finset.card_le_card sub
    omega

/-- A ball larger than the punctured interior must cross the prefix's last layer. -/
theorem hits_layer {D : CH.Digraph} {V : Finset ℕ} {u y k q : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : k+1≤q)
    (hy : y ∈ (ball D V u (k+1)).erase u)
    (hsize : ((ball D V u k).erase u).card<(ball D V y k).card) :
    ∃ z ∈ ball D V u (k+1) \ ball D V u k, z ∈ ball D V y k := by
  classical
  by_contra h
  have hyV := ball_subset (Finset.mem_of_mem_erase hy)
  have stay {z} (hz : z ∈ (ball D V u (k+1)).erase u) (hr : z ∈ ball D V y k) :
      z ∈ (ball D V u k).erase u := by
    refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,?_⟩
    by_contra hout
    exact h ⟨z,Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hz,hout⟩,hr⟩
  have walks (m) (hm : m≤k) (z) (w : Walk D V y z m) : z ∈ (ball D V u k).erase u := by
    induction m generalizing z with
    | zero =>
      cases w
      exact stay hy (self_mem_ball hyV)
    | succ m ih =>
      obtain ⟨v,wv,hz,hvz⟩ := w.unsnoc
      have hv := Finset.mem_of_mem_erase (ih (by omega) v wv)
      have hr := outN_prefix_erase_root hf hu hk hv (mem_outN.mpr ⟨hz,hvz⟩)
      exact stay (mem_outN.mp hr).1 (mem_ball.mpr ⟨hz,m+1,hm,w⟩)
  have sub : ball D V y k ⊆ (ball D V u k).erase u := by
    intro z hz
    obtain ⟨_,m,hm,w⟩ := mem_ball.mp hz
    exact walks m hm z w
  exact (Nat.not_le_of_lt hsize) (Finset.card_le_card sub)

#print axioms rectangle
#print axioms hits_layer
end LeanCH.BR.PrefixTensor

namespace LeanCH.BR.PrefixTensor
open BRq2 BRq3 BR45 BRsGen
open Classical

/-- Same-degree feedback retains the sum of physical missing cells.
The actual punctured prefix must have a retained head at every vertex. -/
theorem same_degree_missing_capacity {q s L k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s≤(outN D V v).card) (hu : u ∈ V) (hs : 1≤s)
    (hlower : ∀ (F : CH.Digraph) (W : Finset ℕ), QFree F W q →
      (∀ v ∈ W, s≤(outN F W v).card) → W.Nonempty → L≤W.card)
    (hk : k+2≤q)
    (hretained : ∀ v ∈ (ball D V u (k+1)).erase u,
      1≤(outN D ((ball D V u (k+1)).erase u) v).card) :
    L+(∑ v ∈ ball D V u (k+1) \ ball D V u k,
      ((ball D V u (k+2) \ ball D V u (k+1)) \
        outN D (ball D V u (k+2) \ ball D V u (k+1)) v).card) ≤
      ((ball D V u (k+1)).erase u).card+
        (ball D V u (k+1) \ ball D V u k).card*
          (ball D V u (k+2) \ ball D V u (k+1)).card := by
  let B := ball D V u (k+1)
  let U := B.erase u
  let S := B \ ball D V u k
  let T := ball D V u (k+2) \ B
  let gap := fun v => s-(outN D U v).card
  let miss := fun v => (T \ outN D T v).card
  change L+(∑ v ∈ S,miss v)≤U.card+S.card*T.card
  have hSU : S ⊆ U := by
    intro v hv
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_erase.mpr ⟨?_,hb⟩
    intro h; subst v
    exact hn (self_mem_ball hu)
  have hUV : U ⊆ V := (Finset.erase_subset u B).trans ball_subset
  have hne : U.Nonempty := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by have := hm u hu; omega : 0<(outN D V u).card)
    obtain ⟨hvV,huv⟩ := mem_outN.mp hv
    refine ⟨v,Finset.mem_erase.mpr ⟨?_,?_⟩⟩
    · intro he; subst v
      exact loopfree hf (by omega) hu huv
    · exact ball_mono_radius (by omega : 1≤k+1)
        (mem_ball.mpr ⟨hvV,1,by omega,.step hvV huv (.refl v)⟩)
  have low := deficiency_bound_of_size hlower (hf.mono_set hUV) hretained hne
  change L≤U.card+∑ v ∈ U,gap v at low
  have hz (v) (hv : v ∈ U \ S) : gap v=0 := by
    obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hv
    have hi : v ∈ ball D V u k := by
      by_contra hh
      exact hn (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv,hh⟩)
    have h := (hm v (ball_subset hi)).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by omega) hi))
    change s≤(outN D U v).card at h
    dsimp [gap]; omega
  have hzero := Finset.sum_eq_zero hz
  have hsum := Finset.sum_sdiff hSU (f:=gap)
  have cap (v) (hv : v ∈ S) : gap v+miss v≤T.card := by
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
    dsimp only [gap]
    omega
  have hcap := Finset.sum_le_sum cap
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at hcap
  omega

#print axioms same_degree_missing_capacity
end LeanCH.BR.PrefixTensor

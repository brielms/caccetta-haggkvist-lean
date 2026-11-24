import checkpoints.shen_extension.SharedHeadEndpoints
import LeanCH.BR.BROutModule

namespace LeanCH.BR.ShenReturnCut
open BRq2 BRq3 BR45 ShenFirstStrip
open Classical

def image (D : CH.Digraph) (V B : Finset ℕ) := B.biUnion (outN D V)
def boundary (D : CH.Digraph) (V B : Finset ℕ) := image D V B \ B

structure Minimal (D : CH.Digraph) (V A : Finset ℕ) (s : ℕ) : Prop where
  inside : A⊆V
  nonempty : A.Nonempty
  small : (boundary D V A).card<s
  proper : ∀ B⊆A,B.Nonempty → B≠A → s≤(boundary D V B).card

theorem extract {D : CH.Digraph} {V U : Finset ℕ} {s : ℕ} (sub : U⊆V)
    (hne : U.Nonempty) (small : (boundary D V U).card<s) :
    ∃ A⊆U,Minimal D V A s := by
  let candidates := U.powerset.filter (fun B => B.Nonempty ∧ (boundary D V B).card<s)
  have mem {B} : B∈candidates ↔ B⊆U ∧ B.Nonempty ∧ (boundary D V B).card<s := by
    simp only [candidates,Finset.mem_filter,Finset.mem_powerset]
  obtain ⟨A,ha,least⟩ := candidates.exists_min_image Finset.card ⟨U,mem.mpr ⟨Finset.Subset.refl _,hne,small⟩⟩
  obtain ⟨au,an,cut⟩ := mem.mp ha
  refine ⟨A,au,au.trans sub,an,cut,?_⟩
  intro B ba bn diff
  by_contra! bad
  have low := least B (mem.mpr ⟨ba.trans au,bn,bad⟩)
  have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ba,diff⟩)
  omega

/-- Every proper nonempty part of the minimal set has more internal exits
than there are old boundary labels that this part fails to reach in one step. -/
theorem exchange {D : CH.Digraph} {V A B : Finset ℕ} {s : ℕ} (M : Minimal D V A s)
    (ba : B⊆A) (bn : B.Nonempty) (diff : B≠A) :
    (boundary D V A \ image D V B).card+1≤(boundary D V B ∩ A).card := by
  let C := boundary D V A
  let P := boundary D V B
  have sub : P \ A⊆C := by
    intro z hz
    obtain ⟨inP,no⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨w,hw,edge⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp inP).1
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w,ba hw,edge⟩,no⟩
  have eq : P \ A=C∩image D V B := by
    ext z; constructor
    · intro h; exact Finset.mem_inter.mpr ⟨sub h,(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1⟩
    · intro h; obtain ⟨hc,hi⟩ := Finset.mem_inter.mp h
      have no := (Finset.mem_sdiff.mp hc).2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hi,fun w => no (ba w)⟩,no⟩
  have one := Finset.card_sdiff_add_card_inter P A
  have two := Finset.card_sdiff_add_card_inter C (image D V B)
  rw [eq] at one
  have less : C.card<s := M.small
  have more : s≤P.card := M.proper B ba bn diff
  change (C \ _).card+1≤(P∩A).card
  omega

private theorem singleton {D : CH.Digraph} {V : Finset ℕ} {q x} (hf : QFree D V q)
    (hq : 1≤q) (hx : x∈V) : boundary D V {x}=outN D V x := by
  ext z
  simp only [boundary,image,Finset.singleton_biUnion,Finset.mem_sdiff,Finset.mem_singleton]
  exact ⟨And.left,fun hz => ⟨hz,fun he => loopfree hf hq hx (he ▸ (mem_outN.mp hz).2)⟩⟩

theorem predecessor {D : CH.Digraph} {V A : Finset ℕ} {q s x}
    (hf : QFree D V q) (hq : 1≤q) (hm : ∀ w∈V,s≤(outN D V w).card)
    (M : Minimal D V A s) (hx : x∈A) : ∃ y∈A,D y x=true := by
  have bn : (A.erase x).Nonempty := by
    by_contra bad
    have zero := Finset.not_nonempty_iff_eq_empty.mp bad
    have id := Finset.insert_erase hx
    rw [zero,Finset.insert_empty] at id
    have low := M.small
    rw [← id,singleton hf hq (M.inside hx)] at low
    have := hm x (M.inside hx); omega
  have diff : A.erase x≠A := fun he => Finset.notMem_erase x A (by rwa [he])
  have ex := exchange M (Finset.erase_subset x A) bn diff
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0<(boundary D V (A.erase x)∩A).card)
  obtain ⟨hc,ha⟩ := Finset.mem_inter.mp hz
  obtain ⟨hi,notB⟩ := Finset.mem_sdiff.mp hc
  have he : z=x := by by_contra ne; exact notB (Finset.mem_erase.mpr ⟨ne,ha⟩)
  obtain ⟨y,hy,edge⟩ := Finset.mem_biUnion.mp hi
  exact ⟨y,(Finset.mem_erase.mp hy).2,he ▸ (mem_outN.mp edge).2⟩

/-- Roots inside the cut pay for each reachable boundary label separately,
with a second payment at every smaller internal radius where it is absent. -/
theorem missed_layer {D : CH.Digraph} {V A : Finset ℕ} {s q x k}
    (M : Minimal D V A s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈A) (hk : k<q) :
    1+(boundary D V A \ image D V (ball D A x k)).card+(ball D A x k).card≤
      (ball D A x (k+1)).card := by
  let B := ball D A x k
  obtain ⟨y,hy,back⟩ := predecessor hf hq hm M hx
  have proper : B≠A := by
    intro eq
    have h : y∈B := eq ▸ hy
    exact no_back_arc (hf.mono_set M.inside) hx h (by omega) back
  have count := exchange M (ball_subset : B⊆A) ⟨x,self_mem_ball hx⟩ proper
  have step : boundary D V B ∩ A⊆ball D A x (k+1) \ B := by
    intro z hz
    obtain ⟨hc,ha⟩ := Finset.mem_inter.mp hz
    obtain ⟨im,notB⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨w,hw,wz⟩ := Finset.mem_biUnion.mp im
    exact Finset.mem_sdiff.mpr ⟨ball_step hw ha (mem_outN.mp wz).2,notB⟩
  have two := Finset.card_le_card step
  have add := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=A) (u:=x) (by omega : k≤k+1))
  change _+B.card=_ at add
  change _+B.card≤_
  dsimp only [B] at *
  omega

/-- Roots inside the cut pay for each reachable boundary label separately,
with a second payment at every smaller internal radius where it is absent. -/
theorem layer_payment {D : CH.Digraph} {V A : Finset ℕ} {s q x k}
    (M : Minimal D V A s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈A) (hk : k<q) :
    1+(boundary D V A ∩ reverseBall D V x (q-1-k)).card+(ball D A x k).card≤
      (ball D A x (k+1)).card := by
  let B := ball D A x k
  have avoid : boundary D V A ∩ reverseBall D V x (q-1-k)⊆boundary D V A \ image D V B := by
    intro z hz
    obtain ⟨hc,hr⟩ := Finset.mem_inter.mp hz
    refine Finset.mem_sdiff.mpr ⟨hc,?_⟩
    intro im
    obtain ⟨w,hw,wz⟩ := Finset.mem_biUnion.mp im
    obtain ⟨_,j,hj,xw⟩ := mem_ball.mp hw
    obtain ⟨_,l,hl,zx⟩ := mem_ball.mp (Finset.mem_filter.mp hr).2
    have walk := ((xw.mono M.inside).snoc (mem_outN.mp wz).1 (mem_outN.mp wz).2).append zx
    exact hf x (j+1+l) (by omega) (by omega) walk
  have payment := missed_layer M hf hq hm hx hk
  have amount := Finset.card_le_card avoid
  dsimp only [B] at amount
  omega

theorem missed_budget {D : CH.Digraph} {V A : Finset ℕ} {s q x} (M : Minimal D V A s)
    (hf : QFree D V q) (hq : 1≤q) (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈A) :
    q+1+(∑ k∈Finset.range q,(boundary D V A \ image D V (ball D A x k)).card)≤A.card := by
  have bound (j : ℕ) (hj : j≤q) :
      j+1+(∑ k∈Finset.range j,(boundary D V A \ image D V (ball D A x k)).card)≤(ball D A x j).card := by
    induction j with
    | zero => simpa using (Finset.card_pos.mpr ⟨x,self_mem_ball hx⟩ : 0<(ball D A x 0).card)
    | succ j ih =>
      have one := ih (by omega)
      have pay := missed_layer M hf hq hm hx (by omega : j<q)
      rw [Finset.sum_range_succ]; omega
  exact (bound q le_rfl).trans (Finset.card_le_card ball_subset)

theorem return_budget {D : CH.Digraph} {V A : Finset ℕ} {s q x} (M : Minimal D V A s)
    (hf : QFree D V q) (hq : 1≤q) (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈A) :
    q+1+(∑ k∈Finset.range q,(boundary D V A ∩ reverseBall D V x (q-1-k)).card)≤A.card := by
  have bound (j : ℕ) (hj : j≤q) :
      j+1+(∑ k∈Finset.range j,(boundary D V A ∩ reverseBall D V x (q-1-k)).card)≤(ball D A x j).card := by
    induction j with
    | zero => simpa using (Finset.card_pos.mpr ⟨x,self_mem_ball hx⟩ : 0<(ball D A x 0).card)
    | succ j ih =>
      have one := ih (by omega)
      have pay := layer_payment M hf hq hm hx (by omega : j<q)
      rw [Finset.sum_range_succ]; omega
  exact (bound q le_rfl).trans (Finset.card_le_card ball_subset)

#print axioms extract
#print axioms return_budget

/-- A deficient cut occurs inside a punctured forward ball before either
half-radius has been passed. Both parities use the same argument. -/
theorem half_ball_cut {D : CH.Digraph} {V : Finset ℕ} {q s}
    (hf : QFree D V q) (hq : 2≤q) (hm : ∀ w∈V,s≤(outN D V w).card)
    (ne : V.Nonempty) (order : V.card≤q*s) :
    ∃ u∈V,∃ k,(k+1≤(q+1)/2) ∧ ∃ A⊆(ball D V u k).erase u,Minimal D V A s := by
  let i := q/2
  let l := (q+1)/2
  have pair : i+l=q := by dsimp [i,l]; omega
  have il : i≤l := by dsimp [i,l]; omega
  obtain ⟨u,hu,k,kl,bad⟩ : ∃ u∈V,∃ k,k+1≤l ∧ (ball D V u (k+1) \ ball D V u k).card<s := by
    by_contra! wide
    have grows (w) (hw : w∈V) (j) (hj : j≤l) : s*j+1≤(ball D V w j).card := by
      induction j with
      | zero => simpa using (Finset.card_pos.mpr ⟨w,self_mem_ball hw⟩ : 0<(ball D V w 0).card)
      | succ j ih =>
        have step := wide w hw j hj
        have before := ih (by omega)
        have := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=w) (by omega : j≤j+1))
        rw [Nat.mul_succ]; omega
    have cap := card_ge_of_two_balls hf pair.le (fun w hw => grows w hw i il)
      (fun w hw => grows w hw l le_rfl) ne
    have price : s*i+s*l=q*s := by rw [← Nat.mul_add,pair,Nat.mul_comm]
    omega
  let B := ball D V u k
  let U := B.erase u
  let L := ball D V u (k+1) \ B
  have base : u∈B := self_mem_ball hu
  have reach (w) (hw : w∈B) {z} (hz : z∈outN D V w) : z∈ball D V u (k+1) ∧ z≠u := by
    have small : k+1≤q := by dsimp [l] at kl; omega
    obtain ⟨hn,ho⟩ := Finset.mem_erase.mp (mem_outN.mp (outN_prefix_erase_root hf hu small hw hz)).1
    exact ⟨ho,hn⟩
  have sub : boundary D V U⊆L := by
    intro z hz
    obtain ⟨hit,notU⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨w,hw,edge⟩ := Finset.mem_biUnion.mp hit
    obtain ⟨ho,hn⟩ := reach w (Finset.mem_erase.mp hw).2 edge
    exact Finset.mem_sdiff.mpr ⟨ho,fun h => notU (Finset.mem_erase.mpr ⟨hn,h⟩)⟩
  have nonempty : U.Nonempty := by
    by_contra no
    have zero := Finset.not_nonempty_iff_eq_empty.mp no
    have eq := Finset.insert_erase base
    change insert u U=B at eq
    rw [zero,Finset.insert_empty] at eq
    have inc : outN D V u⊆L := by
      intro z hz; obtain ⟨ho,hn⟩ := reach u base hz
      exact Finset.mem_sdiff.mpr ⟨ho,fun hb => hn (Finset.mem_singleton.mp (eq ▸ hb))⟩
    have sL := (hm u hu).trans (Finset.card_le_card inc)
    exact (Nat.not_le_of_lt bad) sL
  obtain ⟨A,au,m⟩ := extract ((Finset.erase_subset u B).trans ball_subset) nonempty ((Finset.card_le_card sub).trans_lt bad)
  exact ⟨u,hu,k,kl,A,au,m⟩

/-- At q=3 the entire cut can be extracted inside the common heads of one arc
of the regular graph. The same atoms therefore obey the global return budget. -/
theorem common_head_cut {D : CH.Digraph} {V : Finset ℕ} {s}
    (hf : QFree D V 3) (hm : OutEq s D V) (ne : V.Nonempty) (hs : 0<s) (order : V.card≤3*s) :
    ∃ u∈V,∃ v∈outN D V u,∃ A⊆ShenSharedHead.commonOut D V u v,Minimal D V A s := by
  obtain ⟨u,hu,v,hv,nt,_,loss,_⟩ := ShenSharedHead.deficient_arc hf hm ne hs order
  let T := ShenSharedHead.commonOut D V u v
  have tv : T⊆outN D V v := Finset.inter_subset_right
  have tvV : T⊆V := tv.trans (Finset.filter_subset _ _)
  have inc : boundary D V T⊆(outN D V v \ T)∪ShenSharedHead.endpoints D V u v := by
    intro z hz
    obtain ⟨im,hn⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨w,hw,edge⟩ := Finset.mem_biUnion.mp im
    by_cases ho : z∈outN D V v
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ho,hn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(mem_outN.mp edge).1,ho,w,hw,(mem_outN.mp edge).2⟩)
  have size := (Finset.card_le_card inc).trans (Finset.card_union_le _ _)
  have width := Finset.card_sdiff_add_card_eq_card tv
  rw [hm v (mem_outN.mp hv).1] at width
  change _+(3*s+1-V.card)≤T.card at loss
  obtain ⟨A,at',m⟩ := extract tvV nt (by omega : (boundary D V T).card<s)
  exact ⟨u,hu,v,hv,A,at',m⟩

#print axioms half_ball_cut
#print axioms common_head_cut


/-- Each row in a small cut comes close to hitting its entire external
boundary. The error is measured by the excess of the cut size over q+1. -/
theorem missing_exits {D : CH.Digraph} {V A : Finset ℕ} {s q x} (M : Minimal D V A s)
    (hf : QFree D V q) (hq : 1≤q) (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈A) :
    q+1+(boundary D V A \ outN D V x).card≤A.card := by
  have budget := missed_budget M hf hq hm hx
  have zero : ball D A x 0={x} := by
    ext y; constructor
    · intro h; obtain ⟨_,j,le,w⟩ := mem_ball.mp h
      obtain rfl : j=0 := by omega
      cases w; simp
    · intro h; obtain rfl := Finset.mem_singleton.mp h; exact self_mem_ball hx
  have term := Finset.single_le_sum (f:=fun k => (boundary D V A \ image D V (ball D A x k)).card)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 0<q))
  rw [zero,image,Finset.singleton_biUnion] at term
  omega

theorem uniform_at_minimum {D : CH.Digraph} {V A : Finset ℕ} {s q} (M : Minimal D V A s)
    (hf : QFree D V q) (hq : 1≤q) (hm : ∀ w∈V,s≤(outN D V w).card) (size : A.card≤q+1) :
    BRsub.OutUniform D V A := by
  have all (x) (hx : x∈A) : boundary D V A⊆outN D V x := by
    have low := missing_exits M hf hq hm hx
    exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp (by omega))
  intro x hx y hy z hz no
  have copy {a b} (ha : a∈A) (hb : b∈A) (arc : D a z=true) : D b z=true := by
    have h : z∈boundary D V A := Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨a,ha,mem_outN.mpr ⟨hz,arc⟩⟩,no⟩
    exact (mem_outN.mp (all b hb h)).2
  cases h : D x z <;> cases h' : D y z <;> simp_all [copy hx hy,copy hy hx]

theorem internal_reach {D : CH.Digraph} {V A : Finset ℕ} {s x} (M : Minimal D V A s) (hx : x∈A) :
    ball D A x (A.card-1)=A := by
  have grow (k) (proper : ball D A x k≠A) : (ball D A x k).card<(ball D A x (k+1)).card := by
    let B := ball D A x k
    have pay := exchange M (ball_subset : B⊆A) ⟨x,self_mem_ball hx⟩ proper
    have inc : boundary D V B∩A⊆ball D A x (k+1) \ B := by
      intro y hy
      obtain ⟨cut,ya⟩ := Finset.mem_inter.mp hy
      obtain ⟨im,no⟩ := Finset.mem_sdiff.mp cut
      obtain ⟨z,hz,zy⟩ := Finset.mem_biUnion.mp im
      exact Finset.mem_sdiff.mpr ⟨ball_step hz ya (mem_outN.mp zy).2,no⟩
    have le := Finset.card_le_card inc
    have eq := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=A) (u:=x) (by omega : k≤k+1))
    dsimp only [B] at *; omega
  have size (k) : ball D A x k=A ∨ k+1≤(ball D A x k).card := by
    induction k with
    | zero => exact Or.inr (Finset.card_pos.mpr ⟨x,self_mem_ball hx⟩)
    | succ k ih =>
      by_cases eq : ball D A x k=A
      · apply Or.inl
        apply Finset.Subset.antisymm ball_subset
        intro y hy
        exact ball_mono_radius (by omega : k≤k+1) (show y∈ball D A x k by rwa [eq])
      · have := grow k eq; have := ih.resolve_left eq; exact Or.inr (by omega)
  rcases size (A.card-1) with h|h
  · exact h
  · exact Finset.eq_of_subset_of_card_le ball_subset (by omega)

/-- The reachable external boundary has exactly s-1 vertices when the cut
is inclusion-minimal among the sets with fewer than s external successors. -/
theorem boundary_size {D : CH.Digraph} {V A : Finset ℕ} {s q} (M : Minimal D V A s)
    (hf : QFree D V q) (hq : 1≤q) (hm : ∀ w∈V,s≤(outN D V w).card) :
    (boundary D V A).card+1=s := by
  obtain ⟨x,hx⟩ := M.nonempty
  obtain ⟨y,hy,arc⟩ := predecessor hf hq hm M hx
  have yx : y≠x := by rintro rfl; exact loopfree hf hq (M.inside hx) arc
  let B := A.erase x
  have subset : B⊆A := Finset.erase_subset _ _
  have sep := M.proper B subset ⟨y,Finset.mem_erase.mpr ⟨yx,hy⟩⟩
    (show B≠A from fun he => Finset.notMem_erase x A (by change x∈B; rwa [he]))
  have inc : boundary D V B⊆insert x (boundary D V A) := by
    intro z hz
    obtain ⟨im,hn⟩ := Finset.mem_sdiff.mp hz
    by_cases zx : z=x
    · exact Finset.mem_insert.mpr (Or.inl zx)
    obtain ⟨w,hw,edge⟩ := Finset.mem_biUnion.mp im
    exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w,subset hw,edge⟩,
      fun za => hn (Finset.mem_erase.mpr ⟨zx,za⟩)⟩)
  have := (Finset.card_le_card inc).trans (Finset.card_insert_le _ _)
  have := M.small; omega

#print axioms missing_exits
#print axioms uniform_at_minimum
#print axioms internal_reach
#print axioms boundary_size


/-- Outgoing boundary size is submodular, with original vertex labels kept. -/
theorem boundary_submodular (D : CH.Digraph) (V X Y : Finset ℕ) :
    (boundary D V (X∪Y)).card+(boundary D V (X∩Y)).card≤(boundary D V X).card+(boundary D V Y).card := by
  let close := fun B => B∪image D V B
  have count (B) : (boundary D V B).card+B.card=(close B).card := by
    dsimp [close,boundary]
    rw [Finset.union_comm B]
    have h := Finset.card_sdiff_add_card_inter (image D V B) B
    have eq := Finset.card_union_add_card_inter (image D V B) B
    omega
  have cup : close (X∪Y)=close X∪close Y := by
    ext z; simp only [close,image,Finset.union_biUnion,Finset.mem_union]; tauto
  have cap : close (X∩Y)⊆close X∩close Y := by
    intro z hz
    have lift {A B : Finset ℕ} (sub : A⊆B) : close A⊆close B := by
      intro z hz
      rcases Finset.mem_union.mp hz with h|h
      · exact Finset.mem_union_left _ (sub h)
      · obtain ⟨a,ha,arc⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a,sub ha,arc⟩)
    exact Finset.mem_inter.mpr ⟨lift Finset.inter_subset_left hz,lift Finset.inter_subset_right hz⟩
  have cu := count (X∪Y); rw [cup] at cu
  have := count (X∩Y); have := count X; have := count Y
  have := Finset.card_le_card cap
  have := Finset.card_union_add_card_inter X Y
  have := Finset.card_union_add_card_inter (close X) (close Y)
  omega

/-- Minimize boundary first and cardinality second within the chosen carrier.
The boundary deficit of the original carrier is preserved. -/
theorem optimal_in {D : CH.Digraph} {V U : Finset ℕ} (sub : U⊆V) (ne : U.Nonempty) :
    ∃ A⊆U, let κ := (boundary D V A).card
      Minimal D V A (κ+1) ∧ ∀ B⊆U,B.Nonempty → κ≤(boundary D V B).card := by
  let family := U.powerset.filter Finset.Nonempty
  have mem {B} : B∈family ↔ B⊆U ∧ B.Nonempty := by simp [family]
  obtain ⟨B,hB,best⟩ := family.exists_min_image (fun B => (boundary D V B).card) ⟨U,mem.mpr ⟨Finset.Subset.refl _,ne⟩⟩
  have bound {Y} (ys : Y⊆U) (yn : Y.Nonempty) := best Y (mem.mpr ⟨ys,yn⟩)
  obtain ⟨bu,bn⟩ := mem.mp hB
  obtain ⟨A,ab,minimum⟩ := extract (bu.trans sub) bn (Nat.lt_succ_self (boundary D V B).card)
  have equal : (boundary D V A).card=(boundary D V B).card := by
    have := bound (ab.trans bu) minimum.nonempty
    have := minimum.small; omega
  refine ⟨A,ab.trans bu,?_⟩
  dsimp only; rw [equal]
  exact ⟨minimum,fun _ ys yn => bound ys yn⟩

/-- Intersecting minimizers in the same carrier agree if both are
inclusion-minimal. No graph symmetry or transitivity assumption is used. -/
theorem equal_or_disjoint {D : CH.Digraph} {V U A B : Finset ℕ} {κ}
    (au : A⊆U) (bu : B⊆U) (ma : Minimal D V A (κ+1)) (mb : Minimal D V B (κ+1))
    (minCut : ∀ Y⊆U,Y.Nonempty → κ≤(boundary D V Y).card) : A=B ∨ Disjoint A B := by
  by_cases eq : A=B
  · exact Or.inl eq
  apply Or.inr; apply Finset.disjoint_left.mpr
  intro x xa xb
  have common : (A∩B).Nonempty := ⟨x,Finset.mem_inter.mpr ⟨xa,xb⟩⟩
  have union := minCut _ (Finset.union_subset au bu) ⟨x,Finset.mem_union_left _ xa⟩
  have costs := boundary_submodular D V A B
  have := ma.small; have := mb.small
  by_cases ea : A∩B=A
  · have eb : A∩B≠B := fun wh => eq (ea.symm.trans wh)
    have := mb.proper _ Finset.inter_subset_right common eb
    omega
  · have := ma.proper _ Finset.inter_subset_left common ea
    omega

/-- A boundary label returning directly to a root pays at every positive
reverse radius, giving a uniform bound on actual incoming arcs. -/
theorem incoming_bound {D : CH.Digraph} {V A : Finset ℕ} {s q x}
    (M : Minimal D V A s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈A) :
    q+1+(q-1)*(inN D (boundary D V A) x).card≤A.card := by
  have budget := return_budget M hf hq hm hx
  have row (k) (hk : k∈Finset.range (q-1)) : (inN D (boundary D V A) x).card≤
      (boundary D V A∩reverseBall D V x (q-1-k)).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨zc,zx⟩ := mem_inN.mp hz
    obtain ⟨w,_,wz⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp zc).1
    have len := Finset.mem_range.mp hk
    exact Finset.mem_inter.mpr ⟨zc,Finset.mem_filter.mpr ⟨(mem_outN.mp wz).1,
      ball_mono_radius (by omega : 1≤q-1-k) (ball_of_adj (M.inside hx) zx)⟩⟩
  have sum := Finset.sum_le_sum row
  rw [Finset.sum_const_nat (fun _ _ => rfl),Finset.card_range] at sum
  have inc := Finset.sum_le_sum_of_subset_of_nonneg
    (f:=fun k => (boundary D V A∩reverseBall D V x (q-1-k)).card)
    (Finset.range_mono (by omega : q-1≤q)) (fun _ _ _ => Nat.zero_le _)
  omega

#print axioms optimal_in
#print axioms equal_or_disjoint
#print axioms incoming_bound

/-- Literal CH whenever every punctured half-ball is acyclic, at either parity.
A minimal cut inside such a ball would itself have positive internal degree. -/
theorem cycle_of_acyclic_half_balls {D : CH.Digraph} {q s n : ℕ} (hq : 2≤q) (hn : 0<n)
    (ord : n≤q*s) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s)
    (acyclic : ∀ u∈Finset.range n, let B := (ball D (Finset.range n) u ((q-1)/2)).erase u
      QFree D B B.card) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  have free := qfree_of_noShort hl no
  have degree (x) (hx : x∈Finset.range n) := Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)
  obtain ⟨u,hu,k,rad,A,sub,M⟩ := half_ball_cut free hq degree ⟨0,Finset.mem_range.mpr hn⟩ (by simpa using ord)
  let B := (ball D (Finset.range n) u ((q-1)/2)).erase u
  have ab : A⊆B := by
    intro z hz
    obtain ⟨nu,reach⟩ := Finset.mem_erase.mp (sub hz)
    exact Finset.mem_erase.mpr ⟨nu,ball_mono_radius (by omega : k≤(q-1)/2) reach⟩
  have noCycle := ((acyclic u hu).mono_set ab).mono_bound (Finset.card_le_card ab)
  obtain ⟨x,hx,sink⟩ := exists_sink noCycle M.nonempty le_rfl
  have boundaryCap := M.small
  have inc : outN D (Finset.range n) x⊆boundary D (Finset.range n) A := by
    intro y hy
    obtain ⟨_,arc⟩ := mem_outN.mp hy
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨x,hx,hy⟩,fun ya => sink y ya arc⟩
  have := (degree x (M.inside hx)).trans (Finset.card_le_card inc)
  omega

#print axioms cycle_of_acyclic_half_balls

end LeanCH.BR.ShenReturnCut

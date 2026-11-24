import checkpoints.shen_extension.FirstDeficientTensor

namespace LeanCH.BR.ShenSharedHead
open BRq2 BRq3 BR45 ShenFirstStrip
open Classical

def commonOut (D : CH.Digraph) (V : Finset ℕ) (u v : ℕ) :=
  outN D V u ∩ outN D V v

def commonIn (D : CH.Digraph) (V : Finset ℕ) (u v : ℕ) :=
  inN D V u ∩ inN D V v

def edges (D : CH.Digraph) (V : Finset ℕ) (f : ℕ → ℕ → ℕ) :=
  ∑ u∈V,∑ v∈outN D V u,f u v

theorem transpose (D : CH.Digraph) (V : Finset ℕ) (f : ℕ → ℕ → ℕ) :
    edges D V f=∑ v∈V,∑ u∈inN D V v,f u v := by
  unfold edges outN inN
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

/-- Two choices of the distinguished arc in the same transitive triple. -/
theorem triple_balance (D : CH.Digraph) (V : Finset ℕ) :
    edges D V (fun u v => (commonOut D V u v).card)=
    edges D V (fun u v => (commonIn D V u v).card) := by
  let p := fun u v => (inN D (outN D V u) v).card
  have mid : edges D V (fun u v => (commonOut D V u v).card)=edges D V p := by
    apply Finset.sum_congr rfl
    intro u _
    have eq (v) : commonOut D V u v=outN D (outN D V u) v := by
      ext x; simp [commonOut,outN]; tauto
    simp only [eq,p]
    exact Compose.ThinRigid.sum_out_eq_sum_in D _
  rw [mid,transpose,transpose D V (fun u v => (commonIn D V u v).card)]
  apply Finset.sum_congr rfl
  intro v _
  have eq (u) : inN D (outN D V u) v=outN D (inN D V v) u := by
    ext x; simp [outN,inN]; tauto
  have eq' (u) : commonIn D V u v=inN D (inN D V v) u := by
    ext x; simp [commonIn,inN]; tauto
  simp only [p,eq,eq']
  exact Compose.ThinRigid.sum_out_eq_sum_in D _

private theorem orientation {D : CH.Digraph} {V U : Finset ℕ} (hf : QFree D V 3) (sub : U⊆V) :
    2*(∑ x∈U,(outN D U x).card)+U.card≤U.card*U.card := by
  have row (x) (hx : x∈U) : (outN D U x).card+(inN D U x).card+1≤U.card := by
    have dis : Disjoint (outN D U x) (inN D U x) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact digonfree hf (by decide) (sub hx) (sub (mem_outN.mp hy).1) (mem_outN.mp hy).2 (mem_inN.mp hz).2
    have inc : outN D U x ∪ inN D U x ⊆ U.erase x := by
      intro y hy
      rcases Finset.mem_union.mp hy with a|a
      · obtain ⟨hy,arc⟩ := mem_outN.mp a
        exact Finset.mem_erase.mpr ⟨fun h => loopfree hf (by decide) (sub hx) (h ▸ arc),hy⟩
      · obtain ⟨hy,arc⟩ := mem_inN.mp a
        exact Finset.mem_erase.mpr ⟨fun h => loopfree hf (by decide) (sub hx) (h ▸ arc),hy⟩
    have := Finset.card_le_card inc
    rw [Finset.card_union_of_disjoint dis] at this
    have := Finset.card_erase_add_one hx; omega
  have sum := Finset.sum_le_sum row
  simp only [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_one] at sum
  have eq : (∑ x∈U,(outN D U x).card)=∑ x∈U,(inN D U x).card := Compose.ThinRigid.sum_out_eq_sum_in D U
  omega

private theorem tri {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 3)
    {x y z} (hx : x∈V) (hy : y∈V) (hz : z∈V)
    (a : D x y=true) (b : D y z=true) (c : D z x=true) : False :=
  hf x 3 (by decide) le_rfl (.step hy a (.step hz b (.step hx c (.refl x))))

/-- A common head and its outgoing row must avoid both parent in-rows. -/
theorem arc_table {D : CH.Digraph} {V : Finset ℕ} {u v s a b : ℕ}
    (hf : QFree D V 3) (hm : OutEq s D V) (hu : u∈V) (hv : v∈V) (uv : D u v=true)
    (light : let T := commonOut D V u v
             T.Nonempty → ∃ w∈T,a*(outN D T w).card≤b*T.card) :
    a*((inN D V u).card+(inN D V v).card+s+(commonOut D V u v).card)≤
      a*(V.card+(commonIn D V u v).card)+b*(commonOut D V u v).card := by
  let T := commonOut D V u v
  let I := inN D V u ∪ inN D V v
  have sizeI : I.card+(commonIn D V u v).card=(inN D V u).card+(inN D V v).card :=
    Finset.card_union_add_card_inter _ _
  have iV : I⊆V := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have tV : T⊆V := Finset.inter_subset_left.trans (Finset.filter_subset _ _)
  have dt : Disjoint I T := by
    apply Finset.disjoint_left.mpr
    intro z hz hT
    obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hT
    rcases Finset.mem_union.mp hz with h|h
    · exact digonfree hf (by decide) hu (tV hT) (mem_outN.mp h1).2 (mem_inN.mp h).2
    · exact digonfree hf (by decide) hv (tV hT) (mem_outN.mp h2).2 (mem_inN.mp h).2
  by_cases ne : T.Nonempty
  · obtain ⟨w,hw,cheap⟩ := light ne
    have dis : Disjoint I (outN D V w) := by
      apply Finset.disjoint_left.mpr
      intro z hz ho
      obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hw
      rcases Finset.mem_union.mp hz with h|h
      · exact tri hf hu (tV hw) (mem_outN.mp ho).1 (mem_outN.mp h1).2 (mem_outN.mp ho).2 (mem_inN.mp h).2
      · exact tri hf hv (tV hw) (mem_outN.mp ho).1 (mem_outN.mp h2).2 (mem_outN.mp ho).2 (mem_inN.mp h).2
    have inc : I∪(T∪outN D V w)⊆V :=
      Finset.union_subset iV (Finset.union_subset tV (Finset.filter_subset _ _))
    have hc := Finset.card_le_card inc
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨dt,dis⟩)] at hc
    have inner := Finset.card_union_add_card_inter T (outN D V w)
    have eq : T∩outN D V w=outN D T w := by
      ext z; simp only [Finset.mem_inter,mem_outN]
      exact ⟨fun k => ⟨k.1,k.2.2⟩,fun k => ⟨k.1,tV k.1,k.2⟩⟩
    rw [eq,hm w (tV hw)] at inner
    have bound : (inN D V u).card+(inN D V v).card+s+T.card≤V.card+(commonIn D V u v).card+(outN D T w).card := by omega
    have mul := Nat.mul_le_mul_left a bound
    change a*(_+_+s+T.card)≤a*(_+_)+b*T.card
    change a*(outN D T w).card≤b*T.card at cheap
    nlinarith only [mul,cheap]
  · have empty := Finset.not_nonempty_iff_eq_empty.mp ne
    have dis : Disjoint I (outN D V v) := by
      apply Finset.disjoint_left.mpr
      intro z hz ho
      rcases Finset.mem_union.mp hz with h|h
      · exact tri hf hu hv (mem_outN.mp ho).1 uv (mem_outN.mp ho).2 (mem_inN.mp h).2
      · exact digonfree hf (by decide) hv (mem_outN.mp ho).1 (mem_outN.mp ho).2 (mem_inN.mp h).2
    have bound := Finset.card_le_card (Finset.union_subset iV (Finset.filter_subset _ _) : I∪outN D V v⊆V)
    rw [Finset.card_union_of_disjoint dis,hm v hv] at bound
    have zero : (commonOut D V u v).card=0 := by change T.card=0; rw [empty]; rfl
    rw [zero,add_zero,Nat.mul_zero,add_zero]
    exact Nat.mul_le_mul_left _ (by omega)

#print axioms arc_table

theorem edges_add (D : CH.Digraph) (V : Finset ℕ) (f g : ℕ → ℕ → ℕ) :
    edges D V (fun u v => f u v+g u v)=edges D V f+edges D V g := by simp only [edges,Finset.sum_add_distrib]

private theorem edges_scale (D : CH.Digraph) (V : Finset ℕ) (k) (f : ℕ → ℕ → ℕ) :
    edges D V (fun u v => k*f u v)=k*edges D V f := by simp only [edges,Finset.mul_sum]

theorem edges_const {D : CH.Digraph} {V : Finset ℕ} {s : ℕ} (hm : OutEq s D V) (k : ℕ) :
    edges D V (fun _ _ => k)=V.card*s*k := by
  have row (u) (hu : u∈V) : (∑ _v∈outN D V u,k)=s*k := by
    rw [Finset.sum_const_nat (fun _ _ => rfl),hm u hu]
  unfold edges
  rw [Finset.sum_const_nat row,Nat.mul_assoc]

theorem indegree_contractions {D : CH.Digraph} {V : Finset ℕ} {s : ℕ} (hm : OutEq s D V) :
    let N := V.card*s
    let din := fun v => (inN D V v).card
    edges D V (fun u _ => din u)=N*s ∧ N*s≤edges D V (fun _ v => din v) := by
  intro N din
  have total : (∑ u∈V,din u)=N := by
    have out := Finset.sum_const_nat hm
    have eq : (∑ u∈V,(outN D V u).card)=∑ u∈V,din u := Compose.ThinRigid.sum_out_eq_sum_in D V
    exact eq.symm.trans out
  have tails : edges D V (fun u _ => din u)=N*s := by
    have one (u) (hu : u∈V) : (∑ _v∈outN D V u,din u)=s*din u := by
      rw [Finset.sum_const_nat (fun _ _ => rfl),hm u hu]
    unfold edges
    rw [Finset.sum_congr rfl one,← Finset.mul_sum,total,Nat.mul_comm]
  have heads : N*s≤edges D V (fun _ v => din v) := by
    rw [transpose]; simp only [Finset.sum_const_nat (fun _ _ => rfl)]
    change N*s≤∑ v∈V,din v*din v
    have point (v) (_ : v∈V) : (2*s)*din v≤din v*din v+s*s := by
      zify; nlinarith only [sq_nonneg ((din v:ℤ)-s)]
    have sum := Finset.sum_le_sum point
    rw [← Finset.mul_sum,total,Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at sum
    dsimp [N] at *; nlinarith only [sum]
  exact ⟨tails,heads⟩

theorem common_head_capacity {D : CH.Digraph} {V : Finset ℕ} {s}
    (hf : QFree D V 3) (hm : OutEq s D V) :
    2*edges D V (fun u v => (commonOut D V u v).card)+V.card*s≤V.card*s*s := by
  have row (u) (hu : u∈V) : 2*(∑ v∈outN D V u,(commonOut D V u v).card)+s≤s*s := by
    have eq (v) : commonOut D V u v=outN D (outN D V u) v := by
      ext x; simp [commonOut,outN]; tauto
    simp only [eq]
    have h := orientation (U:=outN D V u) hf (Finset.filter_subset _ _)
    rwa [hm u hu] at h
  have cap := Finset.sum_le_sum row
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const_nat (fun _ _ => rfl),
    Finset.sum_const_nat (fun _ _ => rfl)] at cap
  simpa only [edges,Nat.mul_assoc] using cap

/-- Contract the shared-head constraint over every arc. The common-parent
and common-head sums cancel, while the indegree second moment is retained. -/
theorem global_table {D : CH.Digraph} {V : Finset ℕ} {s a b : ℕ}
    (hf : QFree D V 3) (hm : OutEq s D V) (ne : V.Nonempty) (hs : 0<s)
    (light : ∀ u∈V, ∀ v∈outN D V u, let T := commonOut D V u v
             T.Nonempty → ∃ w∈T,a*(outN D T w).card≤b*T.card) :
    6*a*s+b≤2*a*V.card+b*s := by
  let N := V.card*s
  let din := fun v => (inN D V v).card
  let t := fun u v => (commonOut D V u v).card
  let z := fun u v => (commonIn D V u v).card
  obtain ⟨tails,heads⟩ := indegree_contractions hm
  change edges D V (fun u _ => din u)=N*s at tails
  change N*s≤edges D V (fun _ v => din v) at heads
  have line (u) (hu : u∈V) (v) (hv : v∈outN D V u) :
      a*(din u+din v+s+t u v)≤a*(V.card+z u v)+b*t u v :=
    arc_table hf hm hu (mem_outN.mp hv).1 (mem_outN.mp hv).2 (light u hu v hv)
  have ledger := Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (line u hu))
  change edges D V (fun u v => a*(din u+din v+s+t u v))≤
    edges D V (fun u v => a*(V.card+z u v)+b*t u v) at ledger
  simp only [edges_scale,edges_add,edges_const hm,tails] at ledger
  have balance : edges D V t=edges D V z := triple_balance D V
  rw [← balance] at ledger
  have counts := Nat.mul_le_mul_left a heads
  have bound : 3*a*(N*s)≤a*(N*V.card)+b*edges D V t := by
    change a*(N*s+edges D V (fun _ v => din v)+N*s+edges D V t)≤
      a*(N*V.card+edges D V t)+b*edges D V t at ledger
    nlinarith only [ledger,counts]
  have orient : 2*edges D V t+N≤N*s := common_head_capacity hf hm
  have weighted := Nat.mul_le_mul_left b orient
  have positive : 0<N := Nat.mul_pos (Finset.card_pos.mpr ne) hs
  apply Nat.le_of_mul_le_mul_left _ positive
  nlinarith only [bound,weighted]

/-- All degree scales at cutoff three, for every rational coefficient a/b
satisfying the displayed quadratic inequality. Induction uses the actual
common out-neighbourhood of each arc as the smaller graph. -/
theorem order_bound {D : CH.Digraph} {V : Finset ℕ} {s a b : ℕ}
    (hb : 0<b) (ratio : 2*a*a+b*b≤6*a*b)
    (hf : QFree D V 3) (hm : ∀ x∈V,s≤(outN D V x).card) (ne : V.Nonempty) :
    a*s<b*V.card := by
  generalize hn : V.card=n at *
  induction n using Nat.strong_induction_on generalizing V s D with
  | h n ih =>
    by_cases hs : 0<s
    · obtain ⟨F,sub,reg⟩ := exists_outEq hm
      have free := qfree_sub sub hf
      have light (u) (hu : u∈V) (v) (hv : v∈outN F V u) :
          let T := commonOut F V u v
          T.Nonempty → ∃ w∈T,a*(outN F T w).card≤b*T.card := by
        intro T hT
        have tv : T⊆V := Finset.inter_subset_left.trans (Finset.filter_subset _ _)
        have un : u∉T := fun h => loopfree free (by decide) hu (mem_outN.mp (Finset.mem_inter.mp h).1).2
        have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨tv,fun he => un (he ▸ hu)⟩)
        obtain ⟨w,hw,wmin⟩ := T.exists_min_image (fun x => (outN F T x).card) hT
        have use := ih T.card (by omega) (free.mono_set tv) wmin hT rfl
        exact ⟨w,hw,use.le⟩
      have bound := global_table free reg ne hs light
      have poly := Nat.mul_le_mul_right s ratio
      have scale := Nat.mul_le_mul_left b bound
      by_contra! small
      have twice := Nat.mul_le_mul_left (2*a) small
      have pos : 0<b*b := Nat.mul_pos hb hb
      rw [hn] at scale
      nlinarith only [poly,scale,twice,pos]
    · rw [show s=0 by omega,Nat.mul_zero]
      exact Nat.mul_pos hb (hn ▸ Finset.card_pos.mpr ne)

theorem cycle_of_ratio {D : CH.Digraph} {n s a b : ℕ}
    (hb : 0<b) (ratio : 2*a*a+b*b≤6*a*b) (hn : 0<n) (order : b*n≤a*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  have h := order_bound hb ratio (qfree_of_noShort hl no)
    (fun x hx => Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)) ⟨0,Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h; omega

#print axioms global_table
#print axioms order_bound
#print axioms cycle_of_ratio

end LeanCH.BR.ShenSharedHead

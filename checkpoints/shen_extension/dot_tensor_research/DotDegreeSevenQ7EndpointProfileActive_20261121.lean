import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileBudget_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileOmissions_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

/-- The coupled state left by the multiple-sink branch: returns stay labelled
by their actual omitted B-head, and their entire sink paths stay in disjoint basins. -/
structure ActiveBasinFrame (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) where
  missing : ℕ → ℕ
  s : ℕ
  t : ℕ
  sSink : IsSinkOn D (outN D V u) s
  tSink : IsSinkOn D (outN D V u) t
  ne : s ≠ t
  omissions : ∀ a, IsSinkOn D (outN D V u) a →
    missing a ∈ ball D V u 2 \ ball D V u 1
  omitted : ∀ a, IsSinkOn D (outN D V u) a →
    ∀ b ∈ ball D V u 2 \ ball D V u 1, (D a b ≠ true ↔ b = missing a)
  missing_ne : missing s ≠ missing t
  activeS : ∃ v, ExclusiveBasin D (outN D V u) s v ∧ D (missing s) v = true
  activeT : ∃ v, ExclusiveBasin D (outN D V u) t v ∧ D (missing t) v = true
  returns : ∀ b ∈ ball D V u 2 \ ball D V u 1, ∀ v ∈ outN D V u, D b v = true →
    (b = missing s ∧ ExclusiveBasin D (outN D V u) s v) ∨
    (b = missing t ∧ ExclusiveBasin D (outN D V u) t v)

theorem native_active_basins {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hu : u∈V)
    (b3 : ∀ x∈V, (ball D V x 3).card=22)
    (b4 : ∀ x∈V, (ball D V x 4).card=28)
    (noTwin : ∀ s∈V, ∀ t∈V, outN D V s = outN D V t → s=t) :
    Nonempty (ActiveBasinFrame D V u) := by
  classical
  let A := outN D V u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  have AV : A⊆V := fun _ h => (mem_outN.mp h).1
  have A1 : A⊆ball D V u 1 := fun _ h => (mem_ball_one hu).2 (Or.inr h)
  have BV : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have A7 : A.card=7 := ho u hu
  have b2 v (hv : v∈V) := paired_profile_two hf ho hv (b3 v hv) (b4 v hv)
  have B8 : B.card=8 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+(ball D V u 1).card=(ball D V u 2).card at h
    rw [card_B1 (hf.mono_bound (by decide : 4≤7)) hu,ho u hu,b2 u hu] at h
    omega
  have T6 : T.card=6 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+(ball D V u 2).card=(ball D V u 3).card at h
    rw [b2 u hu,b3 u hu] at h
    omega
  obtain ⟨a,ha,b,hb,ne,sa,sb⟩ := paired_profile_two_sinks hf ho hu b3 b4
  have two (s) (ss : IsSinkOn D A s) : ∃ t, IsSinkOn D A t ∧ t≠s := by
    by_cases e : s=a
    · exact ⟨b,⟨hb,sb⟩,by omega⟩
    · exact ⟨a,⟨ha,sa⟩,Ne.symm e⟩
  obtain ⟨missing,mB,minj,mom⟩ := native_sink_omissions hf ho hu (b2 u hu) noTwin
  let Active := fun s => ∃ v, ExclusiveBasin D A s v ∧ D (missing s) v=true
  have cause (b) (hb : b∈B) (v) (hv : v∈A) (arc : D b v=true) :
      ∃ s, IsSinkOn D A s ∧ b=missing s ∧ ExclusiveBasin D A s v :=
    return_classified hf AV A7 BV two missing minj mom hv hb arc
  have another (s) (ss : IsSinkOn D A s) : ∃ t, IsSinkOn D A t ∧ t≠s ∧ Active t := by
    by_contra no
    have sub : ball D V s 2 ⊆ insert s (B∪T) := by
      intro y hy
      by_cases eq : y=s
      · exact mem_insert.mpr (Or.inl eq)
      obtain ⟨p,hp,apy⟩ := exists_pred (AV ss.1) hy eq
      have sink_heads (z) (hz : z∈V) (asz : D s z=true) : z∈B := by
        refine mem_sdiff.mpr ⟨ball_step (A1 ss.1) hz asz,?_⟩
        intro h
        rcases (mem_ball_one hu).1 h with rfl|ha
        · exact no_back_arc hf hu (A1 ss.1) (by decide : 1+1≤7) asz
        · exact ss.2 z ha asz
      rcases (mem_ball_one (AV ss.1)).1 hp with rfl|hp'
      · exact mem_insert_of_mem (mem_union_left _ (sink_heads y (ball_subset hy) apy))
      have pb := sink_heads p (mem_outN.mp hp').1 (mem_outN.mp hp').2
      have y3 := ball_step (mem_sdiff.mp pb).1 (ball_subset hy) apy
      by_cases y2 : y∈ball D V u 2
      · by_cases y1 : y∈ball D V u 1
        · rcases (mem_ball_one hu).1 y1 with rfl|ya
          · exact (no_back_arc hf hu (mem_sdiff.mp pb).1 (by decide : 2+1≤7) apy).elim
          obtain ⟨t,st,mt,bt⟩ := cause p pb y ya apy
          have nts : t≠s := by
            intro et
            apply (mom s ss p pb).mpr (mt.trans (congrArg missing et))
            exact (mem_outN.mp hp').2
          exact (no ⟨t,st,nts,y,bt,mt ▸ apy⟩).elim
        · exact mem_insert_of_mem (mem_union_left _ (mem_sdiff.mpr ⟨y2,y1⟩))
      · exact mem_insert_of_mem (mem_union_right _ (mem_sdiff.mpr ⟨y3,y2⟩))
    have h := (card_le_card sub).trans ((card_insert_le _ _).trans (Nat.succ_le_succ (card_union_le _ _)))
    rw [b2 s (AV ss.1),B8,T6] at h
    omega
  obtain ⟨s,ss,_,activeS⟩ := another a ⟨ha,sa⟩
  obtain ⟨t,st,nts,activeT⟩ := another s ss
  let P (s : ℕ) := A.filter (ExclusiveBasin D A s)
  have Psub (s) : P s ⊆ A := filter_subset _ _
  have Pd (s t) (ne : s≠t) : Disjoint (P s) (P t) :=
    disjoint_left.mpr fun x hs ht =>
      exclusive_ne (hf.mono_set AV) A7.le ne (mem_filter.mp hs).2 (mem_filter.mp ht).2
  have len_budget (s x) (bs : ExclusiveBasin D A s x) (p : ShortestSinkPath D A x) :
      p.len+1≤(P s).card := by
    have hsub : (range (p.len+1)).image p.vertex ⊆ P s := by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      have hi := mem_range.mp hi
      have w := p.walk (Nat.zero_le i) (show i≤p.len by omega)
      rw [p.start,Nat.sub_zero] at w
      have m := p.mem i (by omega)
      exact mem_filter.mpr ⟨m,exclusive_of_walk bs m w⟩
    have h := card_le_card hsub
    rwa [card_image_of_injOn (p.injective (hf.mono_set AV) A7.le),card_range] at h
  have other_edges (s t) (ss : IsSinkOn D A s) (st : IsSinkOn D A t) (ne : s≠t) :
      D s (missing t)=true := by
    by_contra h
    exact ne (minj s ss t st ((mom s ss (missing t) (mB t st)).mp h).symm)
  have pair (s t x y) (ss : IsSinkOn D A s) (st : IsSinkOn D A t) (ne : s≠t)
      (xs : ExclusiveBasin D A s x) (yt : ExclusiveBasin D A t y)
      (ex : D (missing s) x=true) (ey : D (missing t) y=true)
      (p : ShortestSinkPath D A x) (q : ShortestSinkPath D A y) : 4≤p.len+q.len := by
    have wp := p.walk (Nat.zero_le p.len) le_rfl
    have wq := q.walk (Nat.zero_le q.len) le_rfl
    rw [p.start,Nat.sub_zero] at wp
    rw [q.start,Nat.sub_zero] at wq
    have ep := xs.2 _ ⟨p.mem _ le_rfl,p.sink⟩ ⟨_,wp⟩
    have eq := yt.2 _ ⟨q.mem _ le_rfl,q.sink⟩ ⟨_,wq⟩
    rw [ep] at wp
    rw [eq] at wq
    exact basin_pair_gap hf AV xs.1 yt.1 (BV (mB _ ss)) (BV (mB _ st))
      wp wq (other_edges _ _ ss st ne) ey (other_edges _ _ st ss ne.symm) ex
  have only (k) (sk : IsSinkOn D A k) (ak : Active k) : k=s ∨ k=t := by
    by_contra! nk
    obtain ⟨x,xs,ex⟩ := activeS
    obtain ⟨y,yt,ey⟩ := activeT
    obtain ⟨z,zk,ez⟩ := ak
    obtain ⟨p⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le xs.1
    obtain ⟨q⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le yt.1
    obtain ⟨r⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le zk.1
    exact three_basin_budget A7.le (Psub s) (Psub t) (Psub k)
      (len_budget s x xs p) (len_budget t y yt q) (len_budget k z zk r)
      (Pd s t nts.symm) (Pd s k nk.1.symm) (Pd t k nk.2.symm)
      (pair s t x y ss st nts.symm xs yt ex ey p q)
      (pair s k x z ss sk nk.1.symm xs zk ex ez p r)
      (pair t k y z st sk nk.2.symm yt zk ey ez q r)
  refine ⟨⟨missing,s,t,ss,st,nts.symm,mB,mom,?_,activeS,activeT,?_⟩⟩
  · intro me
    exact nts (minj s ss t st me).symm
  · intro b hb x hx eb
    obtain ⟨k,sk,eq,bs⟩ := cause b hb x hx eb
    have act : Active k := ⟨x,bs,eq ▸ eb⟩
    rcases only k sk act with rfl|rfl
    · exact Or.inl ⟨eq,bs⟩
    · exact Or.inr ⟨eq,bs⟩

#print axioms native_active_basins
end LeanCH.BR.DotDegreeSevenQ7


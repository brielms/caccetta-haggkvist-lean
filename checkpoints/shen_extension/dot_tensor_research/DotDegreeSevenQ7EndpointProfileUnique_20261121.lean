import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfile_20261121
import LeanCH.BR.BRFiniteWalk

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

/-- A unique sink in a native first layer is incompatible with the paired profile. -/
theorem paired_profile_no_unique_sink {D : CH.Digraph} {V : Finset ℕ} {u a : ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hu : u ∈ V)
    (b2 : ∀ x ∈ V, (ball D V x 2).card = 16)
    (b3 : ∀ x ∈ V, (ball D V x 3).card = 22)
    (b4 : (ball D V u 4).card = 28)
    (ha : a ∈ outN D V u)
    (sink : ∀ z ∈ outN D V u, ¬ D a z = true)
    (unique : ∀ x ∈ outN D V u, (∀ z ∈ outN D V u, ¬ D x z = true) → x = a) :
    False := by
  classical
  let A := outN D V u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  let W := ball D V u 4 \ ball D V u 3
  let B' := outN D V a
  have aV : a ∈ V := (mem_outN.mp ha).1
  have A1 : A ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).2 (Or.inr hx)
  have AV : A ⊆ V := A1.trans ball_subset
  have BV : B ⊆ V := fun _ hx => ball_subset (mem_sdiff.mp hx).1
  have TV : T ⊆ V := fun _ hx => ball_subset (mem_sdiff.mp hx).1
  have WV : W ⊆ V := fun _ hx => ball_subset (mem_sdiff.mp hx).1
  have A7 : A.card = 7 := ho u hu
  have ba : B'.card = 7 := ho a aV
  have B8 : B.card = 8 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+(ball D V u 1).card=(ball D V u 2).card at h
    rw [card_B1 (hf.mono_bound (by decide : 4≤7)) hu, ho u hu, b2 u hu] at h
    omega
  have T6 : T.card = 6 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+(ball D V u 2).card=(ball D V u 3).card at h
    rw [b2 u hu,b3 u hu] at h
    omega
  have W6 : W.card = 6 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
    change W.card+(ball D V u 3).card=(ball D V u 4).card at h
    rw [b3 u hu,b4] at h
    omega
  have B'B : B' ⊆ B := by
    intro y hy
    obtain ⟨hyV,hay⟩ := mem_outN.mp hy
    refine mem_sdiff.mpr ⟨ball_step (A1 ha) hyV hay,?_⟩
    intro hy1
    rcases (mem_ball_one hu).1 hy1 with rfl | hyA
    · exact no_back_arc hf hu (A1 ha) (by decide : 1+1≤7) hay
    · exact sink y hyA hay
  have forward (b) (hb : b∈B') (y) (hy : y∈V) (hby : D b y=true) :
      y∈B∪T ∨ y∈A := by
    have b2u := (mem_sdiff.mp (B'B hb)).1
    have y3 := ball_step b2u hy hby
    by_cases y2 : y∈ball D V u 2
    · by_cases y1 : y∈ball D V u 1
      · rcases (mem_ball_one hu).1 y1 with rfl | hyA
        · exact (no_back_arc hf hu b2u (by decide : 2+1≤7) hby).elim
        · exact Or.inr hyA
      · exact Or.inl (mem_union_left _ (mem_sdiff.mpr ⟨y2,y1⟩))
    · exact Or.inl (mem_union_right _ (mem_sdiff.mpr ⟨y3,y2⟩))
  have long (v) (hv : v∈A) (b) (hb : b∈B') (hbv : D b v=true)
      (m) (walk : Walk D A v a m) : 6≤m := by
    by_contra! short
    exact hf v (m+1+1) (by omega) (by omega)
      (((walk.mono AV).snoc (BV (B'B hb)) (mem_outN.mp hb).2).snoc (AV hv) hbv)
  have ex : ∃ v∈A, ∃ b∈B', D b v=true := by
    by_contra no
    have sub : ball D V a 2 ⊆ insert a (B ∪ T) := by
      intro y hy
      by_cases eq : y=a
      · exact mem_insert.mpr (Or.inl eq)
      obtain ⟨b,hb,hby⟩ := exists_pred aV hy eq
      rcases (mem_ball_one aV).mp hb with rfl | hb'
      · exact mem_insert_of_mem (mem_union_left _ (B'B (mem_outN.mpr ⟨ball_subset hy,hby⟩)))
      rcases forward b hb' y (ball_subset hy) hby with hyBT | hyA
      · exact mem_insert_of_mem hyBT
      · exact (no ⟨y,hyA,b,hb',hby⟩).elim
    have h := (card_le_card sub).trans ((card_insert_le _ _).trans (Nat.succ_le_succ (card_union_le _ _)))
    rw [b2 a aV,B8,T6] at h
    omega
  obtain ⟨v,hv,b,hb,hbv⟩ := ex
  obtain ⟨p⟩ := exists_shortest_sink_path (hf.mono_set AV) (by omega) hv
  have last : p.vertex p.len = a := unique _ (p.mem _ le_rfl) p.sink
  have len : p.len = 6 := by
    have walk := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start,last,Nat.sub_zero] at walk
    have h := long v hv b hb hbv p.len walk
    have hb := p.bounded
    omega
  have inj := p.injective (hf.mono_set AV) (by omega)
  have full : (range (p.len+1)).image p.vertex = A := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact p.mem i (by have := mem_range.mp hi; omega)
    · rw [card_image_of_injOn inj,card_range]
      omega
  have allret (y) (hy : y∈A) (c) (hc : c∈B') (hcy : D c y=true) : y=v := by
    have hy' : y∈(range (p.len+1)).image p.vertex := full.symm ▸ hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy'
    have ile : i≤p.len := by have := mem_range.mp hi; omega
    have w := p.walk ile le_rfl
    rw [last] at w
    have h := long _ hy c hc hcy _ w
    have iz : i=0 := by omega
    rw [iz,p.start]
  let C := insert a (insert v (B∪T))
  have sub : ball D V a 2 ⊆ C := by
    intro y hy
    by_cases eq : y=a
    · exact mem_insert.mpr (Or.inl eq)
    obtain ⟨c,hc,hcy⟩ := exists_pred aV hy eq
    rcases (mem_ball_one aV).mp hc with rfl | hc'
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (B'B (mem_outN.mpr ⟨ball_subset hy,hcy⟩))))
    rcases forward c hc' y (ball_subset hy) hcy with hyBT | hyA
    · exact mem_insert_of_mem (mem_insert_of_mem hyBT)
    · exact mem_insert_of_mem (mem_insert.mpr (Or.inl (allret y hyA c hc' hcy)))
  have eqC : ball D V a 2 = C := by
    apply eq_of_subset_of_card_le sub
    rw [b2 a aV]
    have c := (card_insert_le a (insert v (B∪T))).trans (Nat.succ_le_succ
      ((card_insert_le v (B∪T)).trans (Nat.succ_le_succ (card_union_le B T))))
    change C.card≤(B.card+T.card+1)+1 at c
    omega
  have tf : T ⊆ ball D V a 2 := by
    rw [eqC]
    exact fun y hy => mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ hy))
  have w3 : W ⊆ ball D V a 3 := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := ball_succ_pred hu (mem_sdiff.mp hy).1 (mem_sdiff.mp hy).2
    have hxT : x∈T := mem_sdiff.mpr ⟨hx,fun x2 => (mem_sdiff.mp hy).2 (ball_step x2 (WV hy) hxy)⟩
    exact ball_step (tf hxT) (WV hy) hxy
  let y := p.vertex 1
  have yA : y∈A := p.mem 1 (by omega)
  have yneV : y≠v := fun eq => by
    have e : p.vertex 1 = p.vertex 0 := eq.trans p.start.symm
    have z := inj (by simp; omega : 1 ∈ range (p.len+1)) (by simp : 0 ∈ range (p.len+1)) e
    omega
  have yneA : y≠a := fun eq => by
    have e : p.vertex 1 = p.vertex p.len := eq.trans last.symm
    have z := inj (by simp; omega : 1 ∈ range (p.len+1)) (by simp : p.len ∈ range (p.len+1)) e
    omega
  have y3 : y∈ball D V a 3 := by
    have hv2 : v ∈ ball D V a 2 := by
      rw [eqC]
      exact mem_insert_of_mem (mem_insert_self _ _)
    exact ball_step hv2 (AV yA) (by simpa [y,p.start] using p.edge 0 (by omega))
  have ynot : y∉ C ∪ W := by
    have y1 := A1 yA
    have y2 := ball_mono_radius (by decide : 1≤2) y1
    have y3u := ball_mono_radius (by decide : 2≤3) y2
    simp only [C,mem_union,mem_insert]
    rintro ((e|e|hB|hT)|hW)
    · exact yneA e
    · exact yneV e
    · exact (mem_sdiff.mp hB).2 y1
    · exact (mem_sdiff.mp hT).2 y2
    · exact (mem_sdiff.mp hW).2 y3u
  have C3u : C ⊆ ball D V u 3 := by
    intro x hx
    simp only [C,mem_insert,mem_union] at hx
    rcases hx with rfl|rfl|hx|hx
    · exact ball_mono_radius (by decide : 1≤3) (A1 ha)
    · exact ball_mono_radius (by decide : 1≤3) (A1 hv)
    · exact ball_mono_radius (by decide : 2≤3) (mem_sdiff.mp hx).1
    · exact (mem_sdiff.mp hx).1
  have disj : Disjoint C W := disjoint_left.mpr fun x hx hw => (mem_sdiff.mp hw).2 (C3u hx)
  have big : insert y (C∪W) ⊆ ball D V a 3 := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact y3
    rcases mem_union.mp hx with hx | hx
    · exact ball_mono_radius (by decide : 2≤3) (eqC.symm ▸ hx)
    · exact w3 hx
  have cnt := card_le_card big
  rw [card_insert_of_notMem ynot,card_union_of_disjoint disj,←eqC,b2 a aV,W6,b3 a aV] at cnt
  omega

#print axioms paired_profile_no_unique_sink
end LeanCH.BR.DotDegreeSevenQ7



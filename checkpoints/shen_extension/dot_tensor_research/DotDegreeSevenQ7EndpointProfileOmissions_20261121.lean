import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileBasins_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

/-- Recover the one omitted B label from each actual first-layer sink row. -/
theorem native_sink_omissions {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hu : u∈V)
    (b2 : (ball D V u 2).card=16)
    (noTwin : ∀ s∈V, ∀ t∈V, outN D V s = outN D V t → s=t) :
    let A := outN D V u
    let B := ball D V u 2 \ ball D V u 1
    ∃ missing : ℕ→ℕ,
      (∀ s, IsSinkOn D A s → missing s∈B) ∧
      (∀ s, IsSinkOn D A s → ∀ t, IsSinkOn D A t → missing s=missing t → s=t) ∧
      (∀ s, IsSinkOn D A s → ∀ y∈B, (D s y≠true ↔ y=missing s)) := by
  classical
  intro A B
  have BV : B⊆V := fun y hy => ball_subset (mem_sdiff.mp hy).1
  have AV : A⊆V := fun x hx => (mem_outN.mp hx).1
  have A1 : A⊆ball D V u 1 := fun x hx => (mem_ball_one hu).2 (Or.inr hx)
  have BC : B.card=8 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+(ball D V u 1).card=(ball D V u 2).card at h
    rw [card_B1 (hf.mono_bound (by decide : 4≤7)) hu,ho u hu,b2] at h
    omega
  have heads (s) (hs : IsSinkOn D A s) : outN D V s ⊆ B := by
    intro y hy
    obtain ⟨hyV,hsy⟩ := mem_outN.mp hy
    refine mem_sdiff.mpr ⟨ball_step (A1 hs.1) hyV hsy,?_⟩
    intro hy1
    rcases (mem_ball_one hu).1 hy1 with rfl|hyA
    · exact no_back_arc hf hu (A1 hs.1) (by decide : 1+1≤7) hsy
    · exact hs.2 y hyA hsy
  have ex (s) (hs : IsSinkOn D A s) : ∃ i, B \ outN D V s = {i} := by
    apply card_eq_one.mp
    have c := card_sdiff_add_card_eq_card (heads s hs)
    rw [ho s (AV hs.1),BC] at c
    omega
  let missing : ℕ→ℕ := fun s => if hs:IsSinkOn D A s then (ex s hs).choose else 0
  have eq (s) (hs : IsSinkOn D A s) : B \ outN D V s = {missing s} := by
    simpa [missing,hs] using (ex s hs).choose_spec
  have m (s) (hs : IsSinkOn D A s) : missing s∈B := by
    have h : missing s∈B \ outN D V s := (eq s hs).symm ▸ mem_singleton_self _
    exact (mem_sdiff.mp h).1
  have om (s) (hs : IsSinkOn D A s) (y) (hy : y∈B) : D s y≠true ↔ y=missing s := by
    have h : y∈ B \ outN D V s ↔ y=missing s := by rw [eq s hs,mem_singleton]
    simpa [mem_sdiff,mem_outN,hy,BV hy] using h
  refine ⟨missing,m,?_,om⟩
  intro s hs t ht same
  apply noTwin s (AV hs.1) t (AV ht.1)
  ext y
  constructor
  · intro hy
    have ym := heads s hs hy
    refine mem_outN.mpr ⟨BV ym,?_⟩
    by_contra no
    exact (om s hs y ym).mpr (((om t ht y ym).mp no).trans same.symm) (mem_outN.mp hy).2
  · intro hy
    have ym := heads t ht hy
    refine mem_outN.mpr ⟨BV ym,?_⟩
    by_contra no
    exact (om t ht y ym).mpr (((om s hs y ym).mp no).trans same) (mem_outN.mp hy).2

#print axioms native_sink_omissions
end LeanCH.BR.DotDegreeSevenQ7


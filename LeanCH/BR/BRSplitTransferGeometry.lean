import LeanCH.BR.BRCommonParentTransferGeometry

/-! Simultaneous individually safe additions between separated head/tail sets.
The root specialization permits arbitrary physical cuts for safety. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem walk_split_added_relation {D E : CH.Digraph} {K : Finset ℕ}
    {R : ℕ → ℕ → Prop} (hE : ∀ a b, E a b = true → D a b = true ∨ R a b)
    {a b m : ℕ} (p : Walk E K a b m) :
    Walk D K a b m ∨ ∃ x t m1 m2, R x t ∧ m1 + 1 + m2 = m ∧
      Walk D K a x m1 ∧ Walk E K t b m2 := by
  induction p with
  | refl a => exact Or.inl (.refl a)
  | @step a c b k hc hac rest ih =>
    rcases hE a c hac with h | hR
    · rcases ih with h' | ⟨x, t, m1, m2, hx, hm, w1, w2⟩
      · exact Or.inl (.step hc h h')
      · exact Or.inr ⟨x, t, m1 + 1, m2, hx, by omega, .step hc h w1, w2⟩
    · exact Or.inr ⟨a, c, 0, k, hR, by omega, .refl _, rest⟩

theorem qfree_separated_additions {D E : CH.Digraph} {K : Finset ℕ} {q : ℕ}
    {X T : Finset ℕ} {R : ℕ → ℕ → Prop} (hf : QFree D K q)
    (hE : ∀ a b, E a b = true → D a b = true ∨ R a b)
    (hR : ∀ x t, R x t → x ∈ X ∧ t ∈ T ∧ x ∈ K ∧ x ∉ ball D K t (q - 1))
    (hsep : ∀ t ∈ T, ∀ x ∈ X, ∀ k, Walk D K t x k → q - 1 ≤ k) :
    QFree E K q := by
  intro a l h1 hl p
  rcases walk_split_added_relation hE p with h | ⟨x, t, m1, m2, hx, hm, w1, w2⟩
  · exact hf a l h1 hl h
  · obtain ⟨hxX, htT, hxK, hsafe⟩ := hR x t hx
    rcases walk_split_added_relation hE w2 with h | ⟨x', t', m3, m4, hx', hm', w3, _⟩
    · exact hsafe (mem_ball.mpr ⟨hxK, m2 + m1, by omega, h.append w1⟩)
    · have hlong := hsep t htT x' (hR x' t' hx').1 m3 w3
      omega

def cutGraph (D : CH.Digraph) (C : Finset (ℕ × ℕ)) : CH.Digraph :=
  fun x z => decide (D x z = true ∧ (x, z) ∉ C)

def cutHeads (V : Finset ℕ) (C : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  V.filter (fun z => (x, z) ∈ C)

noncomputable def splitSafe (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (v : ℕ) (C : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  (outN D V v).filter (fun t => x ∉ ball (cutGraph D C) (V.erase v) t (q - 1))

noncomputable def splitNew (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (v : ℕ) (C : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  splitSafe q D V v C x \ outN D V x

noncomputable def splitBlocked (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (v : ℕ) (C : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  outN D V v \ splitSafe q D V v C x

noncomputable def splitTransferGraph (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (v : ℕ) (C : Finset (ℕ × ℕ)) : CH.Digraph :=
  fun x z => decide (x ∈ V.erase v ∧ z ∈ V.erase v ∧
    (cutGraph D C x z = true ∨ (x ∈ inN D V v ∧ z ∈ splitSafe q D V v C x)))

/-- Physical old edges, with the endpoint exclusions needed for exact budgets. -/
def RootCuts (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) (C : Finset (ℕ × ℕ)) : Prop :=
  ∀ x z, (x, z) ∈ C → x ∈ V ∧ z ∈ V ∧ D x z = true ∧
    x ∉ inN D V v ∧ z ∉ outN D V v

theorem cutGraph_sub (D : CH.Digraph) (C : Finset (ℕ × ℕ)) :
    ∀ x z, cutGraph D C x z = true → D x z = true :=
  fun _ _ h => (of_decide_eq_true h).1

theorem common_set_head_parent_separation {q : ℕ} {D : CH.Digraph}
    {V S : Finset ℕ} {t x k : ℕ} (hf : QFree D V q) (hSV : S ⊆ V)
    (ht : t ∈ V) (hcommon : ∀ s ∈ S, D s t = true)
    (hx : ∃ s ∈ S, D x s = true) (p : Walk D V t x k) : q - 1 ≤ k := by
  obtain ⟨s, hs, hxs⟩ := hx
  by_contra hn
  exact hf t (k + 1 + 1) (by omega) (by omega)
    ((p.snoc (hSV hs) hxs).snoc ht (hcommon s hs))

theorem root_head_parent_separation {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    {t x k : ℕ} (ht : t ∈ outN D V v) (hx : x ∈ inN D V v)
    (p : Walk D V t x k) : q - 1 ≤ k := by
  by_contra hn
  exact hf t (k + 1 + 1) (by omega) (by omega)
    ((p.snoc hv (mem_inN.mp hx).2).snoc (outN_subset ht) (mem_outN.mp ht).2)

theorem root_interfaces_retained {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V) :
    inN D V v ⊆ V.erase v ∧ outN D V v ⊆ V.erase v := by
  constructor
  · intro x hx
    refine mem_erase.mpr ⟨?_, (mem_inN.mp hx).1⟩
    intro he
    subst x
    exact loopfree hf hq hv (mem_inN.mp hx).2
  · intro t ht
    refine mem_erase.mpr ⟨?_, outN_subset ht⟩
    intro he
    subst t
    exact loopfree hf hq hv (mem_outN.mp ht).2

theorem root_interfaces_disjoint {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V) :
    Disjoint (inN D V v) (outN D V v) := by
  apply disjoint_left.mpr
  intro x hx ht
  exact digonfree hf hq hv (outN_subset ht) (mem_outN.mp ht).2 (mem_inN.mp hx).2

/-- No restrictions on the cut set are needed for simultaneous safety. -/
theorem splitTransferGraph_qfree {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (C : Finset (ℕ × ℕ)) : QFree (splitTransferGraph q D V v C) (V.erase v) q := by
  apply qfree_separated_additions (D := cutGraph D C)
    (X := inN D V v) (T := outN D V v)
    (R := fun x t => x ∈ inN D V v ∧ t ∈ splitSafe q D V v C x)
  · exact qfree_sub (cutGraph_sub D C) (hf.mono_set (erase_subset v V))
  · intro x z h
    exact (of_decide_eq_true h).2.2
  · intro x t h
    obtain ⟨ht, hs⟩ := mem_filter.mp h.2
    exact ⟨h.1, ht, (root_interfaces_retained hq hf hv).1 h.1, hs⟩
  · intro t ht x hx k p
    exact root_head_parent_separation hf hv ht hx
      ((walk_sub (cutGraph_sub D C) p).mono (erase_subset v V))

theorem old_receiver_safe {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    {v x t : ℕ} (hf : QFree D V q) (C : Finset (ℕ × ℕ))
    (ht : t ∈ outN D V v) (hxt : D x t = true) :
    t ∈ splitSafe q D V v C x := by
  refine mem_filter.mpr ⟨ht, ?_⟩
  intro hret
  obtain ⟨_, k, hk, p⟩ := mem_ball.mp hret
  exact hf t (k + 1) (by omega) (by omega)
    (((walk_sub (cutGraph_sub D C) p).mono (erase_subset v V)).snoc (outN_subset ht) hxt)

theorem splitTransfer_parent_heads {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v x : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    {C : Finset (ℕ × ℕ)} (hC : RootCuts D V v C) (hx : x ∈ inN D V v) :
    outN (splitTransferGraph q D V v C) (V.erase v) x =
      outN D (V.erase v) x ∪ splitNew q D V v C x := by
  have hxK := (root_interfaces_retained hq hf hv).1 hx
  have hT := (root_interfaces_retained hq hf hv).2
  ext z
  constructor
  · intro hz
    obtain ⟨_, hzK, h | ⟨_, hs⟩⟩ := of_decide_eq_true (mem_outN.mp hz).2
    · exact mem_union_left _ (mem_outN.mpr ⟨hzK, (cutGraph_sub D C) _ _ h⟩)
    · by_cases he : D x z = true
      · exact mem_union_left _ (mem_outN.mpr ⟨hzK, he⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hs, fun h => he (mem_outN.mp h).2⟩)
  · intro hz
    rcases mem_union.mp hz with ho | hn
    · obtain ⟨hzK, hxz⟩ := mem_outN.mp ho
      exact mem_outN.mpr ⟨hzK, decide_eq_true ⟨hxK, hzK, Or.inl
        (decide_eq_true ⟨hxz, fun hc => (hC x z hc).2.2.2.1 hx⟩)⟩⟩
    · have hs := (mem_sdiff.mp hn).1
      have hzK := hT (mem_filter.mp hs).1
      exact mem_outN.mpr ⟨hzK, decide_eq_true ⟨hxK, hzK, Or.inr ⟨hx, hs⟩⟩⟩

theorem splitTransfer_other_heads {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {v x : ℕ} {C : Finset (ℕ × ℕ)} (hx : x ∈ V.erase v)
    (hn : x ∉ inN D V v) :
    outN (splitTransferGraph q D V v C) (V.erase v) x =
      outN D V x \ cutHeads V C x := by
  ext z
  simp only [mem_outN, splitTransferGraph, decide_eq_true_eq, cutGraph, mem_sdiff,
    cutHeads, mem_filter]
  constructor
  · rintro ⟨hz, _, _, ⟨he, hcut⟩ | ⟨hp, _⟩⟩
    · exact ⟨⟨(mem_erase.mp hz).2, he⟩, fun h => hcut h.2⟩
    · exact (hn hp).elim
  · rintro ⟨⟨hzV, he⟩, hcut⟩
    have hzK : z ∈ V.erase v := mem_erase.mpr ⟨fun hz => hn
      (mem_inN.mpr ⟨(mem_erase.mp hx).2, hz ▸ he⟩), hzV⟩
    exact ⟨hzK, hx, hzK, Or.inl ⟨he, fun hc => hcut ⟨hzV, hc⟩⟩⟩

end LeanCH.BR.WeightedSD

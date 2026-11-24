import LeanCH.BR.BRWeightedSingletonReceiver

namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- No freshness or nonloop assumption is needed: safe old arcs satisfy the
same return exclusion, while loops fail it. -/
theorem qfree_insert_iff_no_short_return {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (i j : V) :
    QFree (insertArc D i j) V q ↔ i.val∉ball D V j (q-1) := by
  constructor
  · intro hs hb
    obtain ⟨_,n,hn,w⟩ := mem_ball.mp hb
    exact hs i (n+1) (by omega) (by omega)
      (.step j.property (by simp [insertArc]) (walk_sub (insertArc_mono D i j) w))
  · exact qfree_insertArc hf i j

/-- Bounded-walk form of exact return distance q, using this host's diameter. -/
theorem qfree_insert_iff_last_return_layer {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hdiam : ∀x∈V,∀y∈V,y∈ball D V x q) (i j : V) :
    QFree (insertArc D i j) V q ↔
      Walk D V j i q ∧ ∀n<q,¬Walk D V j i n := by
  rw [qfree_insert_iff_no_short_return hq hf i j]
  constructor
  · intro hn
    obtain ⟨_,n,hnb,w⟩ := mem_ball.mp (hdiam j j.property i i.property)
    have he : n=q := by
      by_contra hne
      exact hn (mem_ball.mpr ⟨i.property,n,by omega,w⟩)
    refine ⟨he ▸ w,?_⟩
    intro m hm wm
    exact hn (mem_ball.mpr ⟨i.property,m,by omega,wm⟩)
  · rintro ⟨_,hno⟩ hb
    obtain ⟨_,n,hn,w⟩ := mem_ball.mp hb
    exact hno n (by omega) w

/-- Exact conflict test for two individually safe insertions, with possibly
zero-length crossed segments. No disjointness, diameter, degree or saturation. -/
theorem two_insertions_unsafe_iff_cross_returns {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (i j k l : V)
    (hs1 : QFree (insertArc D i j) V q) (hs2 : QFree (insertArc D k l) V q) :
    (¬QFree (insertArc (insertArc D i j) k l) V q) ↔
      ∃m n,m+n+2≤q ∧ Walk D V j k m ∧ Walk D V l i n := by
  constructor
  · intro hbad
    by_contra hno
    apply hbad
    apply qfree_insertArc hs1 k l
    rintro hb
    obtain ⟨_,s,hs,w⟩ := mem_ball.mp hb
    have hsplit : ∀a b,insertArc D i j a b=true→D a b=true ∨ (a=i.val ∧ b=j.val) := by
      intro a b he
      by_cases hh : a=i.val ∧ b=j.val
      · exact Or.inr hh
      · exact Or.inl (by simpa only [insertArc,hh,ite_false] using he)
    rcases walk_split hsplit w with wold|⟨m1,m2,hm,w1,w2⟩
    · exact hs2 k (s+1) (by omega) (by omega)
        (.step l.property (by simp [insertArc]) (walk_sub (insertArc_mono D k l) wold))
    · rcases walk_split hsplit w2 with wold|⟨m3,m4,hm2,w3,_⟩
      · exact hno ⟨m2,m1,by omega,wold,w1⟩
      · exact hs1 i (m3+1) (by omega) (by omega)
          (.step j.property (by simp [insertArc]) (walk_sub (insertArc_mono D i j) w3))
  · rintro ⟨m,n,hm,w1,w2⟩ hs
    have hsub : ∀a b,D a b=true→insertArc (insertArc D i j) k l a b=true :=
      fun a b e=>insertArc_mono _ k l a b (insertArc_mono D i j a b e)
    have e1 : insertArc (insertArc D i j) k l i j=true :=
      insertArc_mono _ k l i j (by simp [insertArc])
    have e2 : insertArc (insertArc D i j) k l k l=true := by simp [insertArc]
    have wc : Walk (insertArc (insertArc D i j) k l) V i i (m+(n+1)+1) :=
      .step j.property e1 ((walk_sub hsub w1).append (.step l.property e2 (walk_sub hsub w2)))
    exact hs i _ (by omega) (by omega) wc

/-- Saturation compares any genuinely fresh safe completion with restoration.
The two actual paths lie in the SAME deletion. No diameter or source laws. -/
theorem saturated_completion_position {q : ℕ} (hq : 1≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (B G i j : V) (hBG : D B G=true) (hnew : ¬D i j=true)
    (hs : QFree (insertArc (eraseArc D B G) i j) V q) :
    ∃a b,a+b+2≤q ∧ Walk (eraseArc D B G) V j B a ∧ Walk (eraseArc D B G) V G i b := by
  have hrestore : insertArc (eraseArc D B G) B G=D := by
    funext x y
    by_cases he : x=B.val ∧ y=G.val
    · rcases he with ⟨rfl,rfl⟩; simp [insertArc,hBG]
    · simp [insertArc,eraseArc,he]
  have hr : QFree (insertArc (eraseArc D B G) B G) V q := hrestore.symm ▸ hf
  have hbad : ¬QFree (insertArc (insertArc (eraseArc D B G) B G) i j) V q := by
    rw [hrestore,qfree_insert_iff_no_short_return hq hf i j]
    exact fun hn=>hn (hsat j j.property i i.property hnew)
  obtain ⟨b,a,hab,wb,wa⟩ := (two_insertions_unsafe_iff_cross_returns hq B G i j hr hs).mp hbad
  exact ⟨a,b,by omega,wa,wb⟩

end LeanCH.BR.WeightedSD


import checkpoints.shen_extension.TallBankTransfer
import checkpoints.shen_extension.SharedSuccessorEquality

namespace LeanCH.BR.TallBankTransfer

open Finset BRq2 BRq3 DotClonePairCompletion

/-- The even-order budget when every floor row has a tall child and each
child's parents have the same actual second layer. The existing successor accounting charges
physical pairs within the fibres. -/
theorem equality_of_child_fibres
    {D : CH.Digraph} {V : Finset ℕ} {q k B : ℕ}
    (free : QFree D V q) (lo : 2 ≤ k) (fit : k + k ≤ q)
    (reg : ∃ r, OutEq r D V) (order : V.card = B + B)
    (floor : ∀ x ∈ V, B ≤ (ball D V x k).card)
    (child : ℕ → ℕ)
    (tall : ∀ x ∈ V, (ball D V x k).card = B →
      child x ∈ V ∧ B < (ball D V (child x) k).card)
    (fibres : ∀ x ∈ V, ∀ y ∈ V, (ball D V x k).card = B →
      (ball D V y k).card = B → child x = child y →
      ball D V x 2 \ ball D V x 1 = ball D V y 2 \ ball D V y 1) :
    let S := V.filter (fun x => (ball D V x k).card = B)
    let T := V \ S
    S.card = B ∧ S.image child = T ∧
    (∀ x ∈ T, (ball D V x k).card = B + 1) ∧
    ∀ x ∈ V, ∀ y ∈ V, x ≠ y → y ∈ ball D V x k ∨ x ∈ ball D V y k := by
  classical
  obtain ⟨r, regular⟩ := reg
  let S := V.filter (fun x => (ball D V x k).card = B)
  let T := V \ S
  have sv : S ⊆ V := filter_subset _ _
  have sr (x) (hx : x ∈ S) : (ball D V x k).card = B := (mem_filter.mp hx).2
  have absent (u) (hu : u ∈ V) (v) (hv : v ∈ V)
      (uo : (ball D V u k).card = B) (vo : (ball D V v k).card = B)
      (ne : u ≠ v) (same : child u = child v) : v ∉ ball D V u k :=
    (same_second_layer_incomparable free regular lo (by omega) hu hv ne
      (fibres u hu v hv uo vo same)).1
  obtain ⟨sc, tc, empty, scores⟩ := OneSpareGrowth.shared_successor_equality
    free fit (by omega : V.card = 2 * B) floor child tall absent
  change S.card = B at sc
  change T.card = B at tc
  have cover (u) (hu : u ∈ V) (v) (hv : v ∈ V) (ne : u ≠ v) :
      v ∈ ball D V u k ∨ u ∈ ball D V v k := by
    by_contra! h
    have uv : (u, v) ∈ orderedIncomparable D V k :=
      mem_filter.mpr ⟨mem_offDiag.mpr ⟨hu, hv, ne⟩, h⟩
    rw [empty] at uv
    exact notMem_empty _ uv
  have image : S.image child = T := by
    have inj : Set.InjOn child ↑S := by
      intro u hu v hv eq
      by_contra ne
      rcases cover u (sv hu) v (sv hv) ne with uv | vu
      · exact absent u (sv hu) v (sv hv) (sr u hu) (sr v hv) ne eq uv
      · exact absent v (sv hv) u (sv hu) (sr v hv) (sr u hu) (Ne.symm ne) eq.symm vu
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      obtain ⟨cv, cp⟩ := tall x (sv hx) (sr x hx)
      exact mem_sdiff.mpr ⟨cv, fun h => (Nat.ne_of_lt cp) (sr _ h).symm⟩
    · rw [card_image_of_injOn inj, sc, tc]
  exact ⟨sc, image, scores, cover⟩

/-- The fibre accounting and the return use the same child assignment and
the same graph. The final head can be any tall head with a short walk to
the assigned child. -/
theorem no_balanced_child_cover
    {D : CH.Digraph} {V : Finset ℕ} {q k B : ℕ}
    (free : QFree D V q) (lo : 2 ≤ k) (fit : k + k ≤ q)
    (reg : ∃ r, OutEq r D V) (order : V.card = B + B) (positive : 0 < B)
    (floor : ∀ x ∈ V, B ≤ (ball D V x k).card)
    (child : ℕ → ℕ)
    (tall : ∀ x ∈ V, (ball D V x k).card = B →
      child x ∈ outN D V x ∧ B < (ball D V (child x) k).card)
    (fibres : ∀ x ∈ V, ∀ y ∈ V, (ball D V x k).card = B →
      (ball D V y k).card = B → child x = child y →
      ball D V x 2 \ ball D V x 1 = ball D V y 2 \ ball D V y 1)
    (gain : ∀ x ∈ V, ∀ y ∈ V, (ball D V x k).card = B →
      (ball D V y k).card = B → x ≠ y →
      y ∈ ball D V x k → y ∈ ball D V (child x) (k - 1))
    (tail : ∀ x ∈ V, (ball D V x k).card = B →
      ∃ z ∈ outN D V x, z ≠ child x ∧ B < (ball D V z k).card ∧
        child x ∈ ball D V z k) : False := by
  classical
  let S := V.filter (fun x => (ball D V x k).card = B)
  let T := V \ S
  have sv : S ⊆ V := filter_subset _ _
  have sr (x) (hx : x ∈ S) : (ball D V x k).card = B := (mem_filter.mp hx).2
  obtain ⟨sc, image, _, cover⟩ := equality_of_child_fibres free lo fit reg order floor child
    (fun x hx eq => ⟨(mem_outN.mp (tall x hx eq).1).1,(tall x hx eq).2⟩) fibres
  change S.card = B at sc
  change S.image child = T at image
  obtain ⟨u,hu⟩ := card_pos.mp (sc.symm ▸ positive)
  obtain ⟨z, hz, different, hTall, walk⟩ := tail u (sv hu) (sr u hu)
  have zt : z ∈ T := mem_sdiff.mpr ⟨(mem_outN.mp hz).1, fun hs => (Nat.ne_of_lt hTall) (sr z hs).symm⟩
  obtain ⟨w, hw, rfl⟩ := mem_image.mp (image.symm ▸ zt)
  exact no_child_return free fit child
    (fun x hx => (tall x (sv hx) (sr x hx)).1)
    (fun x hx y hy => cover x (sv hx) y (sv hy))
    (fun x hx y hy => gain x (sv hx) y (sv hy) (sr x hx) (sr y hy))
    hu hw different.symm hz walk

#print axioms equality_of_child_fibres
#print axioms no_balanced_child_cover
end LeanCH.BR.TallBankTransfer

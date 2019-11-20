Require Export TypeTheory.PathCategories.Auxiliary.

Local Open Scope cat.
Declare Scope pathcat.
Local Open Scope pathcat.
 

Definition equivs_fibs_data (C : category) : UU :=
        (∏ a b : C , hsubtype (a --> b)) (* the equivalences *)
        ×
        (∏ a b : C , hsubtype (a --> b)). (* the fibrations *)


Definition category_equivs_fibs_data : UU :=
  ∑ C : category , equivs_fibs_data C.

Definition make_category_equivs_fibs_data (C : category)
           (equivs : ∏ A B : C , hsubtype (A --> B))
           (fibs   : ∏ A B : C , hsubtype (A --> B))
           : category_equivs_fibs_data
  := tpair _ C (make_dirprod equivs fibs).

Definition category_from_category_equivs_fibs_data  (C : category_equivs_fibs_data ) : category := pr1 C.
Coercion category_from_category_equivs_fibs_data  : category_equivs_fibs_data  >-> category.

Definition is_equivalence {C : category_equivs_fibs_data } {A B : C} (f : A --> B) := (pr1 (pr2 C)) A B f.
Definition equivalences {C : category_equivs_fibs_data } (A B : C) := ∑ f : A --> B , is_equivalence f.
Definition make_equivalence {C : category_equivs_fibs_data} {A B : C} (f : A --> B) (isequiv_f : is_equivalence f) : equivalences A B := tpair _ f isequiv_f.
Definition mor_from_equivalence {C : category_equivs_fibs_data } {A B : C} (f : equivalences A B) : A --> B := pr1 f.
Coercion mor_from_equivalence : equivalences >-> precategory_morphisms.

Definition is_fibration {C : category_equivs_fibs_data} {A B : C} (f : A --> B) := (pr2 (pr2 C)) A B f.
Definition fibrations {C : category_equivs_fibs_data} (A B : C) := ∑ f : A --> B , is_fibration f.
Definition make_fibration {C : category_equivs_fibs_data} {A B : C} (f : A --> B) (isfib_f : is_fibration f) : fibrations A B := tpair _ f isfib_f.
Definition mor_from_fibration {C : category_equivs_fibs_data} {A B : C} (fib : fibrations A B) : precategory_morphisms A B:= pr1 fib.
Coercion mor_from_fibration : fibrations >-> precategory_morphisms.

Notation "a ~~> b" := (equivalences a b) (at level 55) : pathcat.

Notation "a -|> b" := (fibrations a b) (at level 55) : pathcat.

Definition is_trivial_fibration {C : category_equivs_fibs_data} {A B : C} (f : A --> B) := hconj (is_fibration f) (is_equivalence f).
Definition trivial_fibrations {C : category_equivs_fibs_data} (A B : C) := ∑ (f : A --> B) ,  (is_trivial_fibration f).
Definition make_trivial_fibration {C : category_equivs_fibs_data} {A B : C} (f : A --> B) (isfib_f : is_fibration f) (isequiv_f : is_equivalence f) : trivial_fibrations A B := (f,,isfib_f,,isequiv_f).
Definition mor_from_trivial_fibration {C : category_equivs_fibs_data} {A B : C} (f : trivial_fibrations A B) : A --> B := pr1 f.
Coercion mor_from_trivial_fibration : trivial_fibrations >-> precategory_morphisms.

Definition fib_from_trivfib {C : category_equivs_fibs_data} {A B : C} (f : trivial_fibrations A B) : fibrations A B := make_fibration f (pr1 (pr2 f)).
Coercion fib_from_trivfib : trivial_fibrations >-> fibrations.
Definition equiv_from_trivfib {C : category_equivs_fibs_data} {A B : C} (f : trivial_fibrations A B) :equivalences A B := make_equivalence f (pr2 (pr2 f)).
Coercion equiv_from_trivfib : trivial_fibrations >-> equivalences.

Notation "a ~|> b" := (trivial_fibrations a b) (at level 55) : pathcat.

Definition is_category_equivs_fibs  (C : category_equivs_fibs_data ) : UU :=
  (∏ (A B : C) (f : A --> B) , is_iso f → is_trivial_fibration f) (* iso's are trivial *)
  ×
  (∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z) , is_fibration f → is_fibration g → is_fibration (g ∘ f)) (* fibrations are closed under composition *)
  ×
  (∏ (X Y Z W : C) (f : X --> Y) (g : Y --> Z) (h : Z --> W) , is_equivalence (g ∘ f) → is_equivalence (h ∘ g) → is_equivalence f × is_equivalence g × is_equivalence h × is_equivalence (h ∘ g ∘ f)) (* equivalences satisfy 2-out-of-6 *).

Definition make_is_category_equivs_fibs {C : category_equivs_fibs_data}
           (isos_are_trivs : ∏ (A B : C) (f : A --> B) , is_iso f → is_trivial_fibration f)
           (fibs_closed_composition : ∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z) , is_fibration f → is_fibration g → is_fibration (g ∘ f))
           (equivs_two_out_of_six : ∏ (X Y Z W : C) (f : X --> Y) (g : Y --> Z) (h : Z --> W) , is_equivalence (g ∘ f) → is_equivalence (h ∘ g) → is_equivalence f × is_equivalence g × is_equivalence h × is_equivalence (h ∘ g ∘ f)) : is_category_equivs_fibs C := (isos_are_trivs,,fibs_closed_composition,,equivs_two_out_of_six).

Definition category_equivs_fibs := ∑ X , is_category_equivs_fibs X.
Definition make_category_equivs_fibs (C : category_equivs_fibs_data) (H : is_category_equivs_fibs C) : category_equivs_fibs := (C,,H).
Definition category_equivs_fibs_data_from_category_equivs_fibs (C : category_equivs_fibs) := pr1 C.
Coercion category_equivs_fibs_data_from_category_equivs_fibs : category_equivs_fibs >-> category_equivs_fibs_data.

Definition iso_is_trivial_fibration {C : category_equivs_fibs} {A B : C} (f : A --> B) (iso_f : is_iso f) : is_trivial_fibration f := (pr1 (pr2 C)) A B f iso_f.

Definition fibrations_closed_composition {C : category_equivs_fibs} {X Y Z : C} (f : X --> Y) (g : Y --> Z) (fib_f : is_fibration f) (fib_g : is_fibration g) := (pr1 (pr2 (pr2 C))) X Y Z f g fib_f fib_g.

Definition two_out_of_six_fst {C : category_equivs_fibs} {X Y Z W : C} (f : X --> Y) (g : Y --> Z) (h : Z --> W) (is_equiv_gf : is_equivalence (g ∘ f)) (is_equiv_hg : is_equivalence (h ∘ g)) : is_equivalence f := pr1 (pr2 (pr2 (pr2 C)) X Y Z W f g h is_equiv_gf is_equiv_hg).
Definition two_out_of_six_snd {C : category_equivs_fibs} {X Y Z W : C} (f : X --> Y) (g : Y --> Z) (h : Z --> W) (is_equiv_gf : is_equivalence (g ∘ f)) (is_equiv_hg : is_equivalence (h ∘ g)) : is_equivalence g := pr1 (pr2 (pr2 (pr2 (pr2 C)) X Y Z W f g h is_equiv_gf is_equiv_hg)).
Definition two_out_of_six_trd {C : category_equivs_fibs} {X Y Z W : C} (f : X --> Y) (g : Y --> Z) (h : Z --> W) (is_equiv_gf : is_equivalence (g ∘ f)) (is_equiv_hg : is_equivalence (h ∘ g)) : is_equivalence h := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C)) X Y Z W f g h is_equiv_gf is_equiv_hg))).
Definition two_out_of_six_all {C : category_equivs_fibs} {X Y Z W : C} (f : X --> Y) (g : Y --> Z) (h : Z --> W) (is_equiv_gf : is_equivalence (g ∘ f)) (is_equiv_hg : is_equivalence (h ∘ g)) : is_equivalence (h ∘ g ∘ f) := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)) X Y Z W f g h is_equiv_gf is_equiv_hg))).

Lemma equivs_two_out_of_three {C : category_equivs_fibs} {X Y Z : C} (f : X --> Y) (g : Y --> Z) : ((is_equivalence f) ∧ (is_equivalence g)) ∨ ((is_equivalence f) ∧ (is_equivalence (g ∘ f))) ∨ ((is_equivalence g) ∧ (is_equivalence (g ∘ f))) → (is_equivalence f) ∧ (is_equivalence g) ∧ (is_equivalence (g ∘ f)).
Proof.
  assert (S1 : is_equivalence f ∧ is_equivalence g → is_equivalence f ∧ is_equivalence g ∧ is_equivalence (g ∘ f)).
  { intros.
    destruct X0.
    split.
    + exact pr1.
    + split.
      * exact pr2.
      * rewrite (! (id_left g)).
        apply two_out_of_six_all.
        -- rewrite (id_right f).
           exact pr1.
        -- rewrite (id_left g).
           exact pr2.
  }
  assert (S2 : is_equivalence f ∧ is_equivalence (g ∘ f) → is_equivalence f ∧ is_equivalence g ∧ is_equivalence (g ∘ f)).
  { intros.
    destruct X0.
    split.
    - exact pr1.
    - split.
      + apply (two_out_of_six_trd (identity X) f g).
        * rewrite (id_left f).
          exact pr1.
        * exact pr2.
      + exact pr2.
  }
  assert (S3 : is_equivalence g ∧ is_equivalence (g ∘ f) → is_equivalence f ∧ is_equivalence g ∧ is_equivalence (g ∘ f)).
  { intros.
    destruct X0.
    split.
    - apply (two_out_of_six_fst f g (identity _)).
      + exact pr2.
      + rewrite (id_right g).
        exact pr1.
    - split.
      + exact pr1.
      + exact pr2.
  }
  assert (S4 : coprod (is_equivalence f ∧ is_equivalence (f · g)) (is_equivalence g ∧ is_equivalence (f · g)) → is_equivalence f ∧ is_equivalence g ∧ is_equivalence (f · g)).
  { intro.
    induction X0.
    - apply (S2 a).
    - apply (S3 b).
  }
  pose (hinhuniv S4).
  assert (S5 : coprod (is_equivalence f ∧ is_equivalence g) ((is_equivalence f ∧ is_equivalence (f · g)) ∨ (is_equivalence g ∧ is_equivalence (f · g))) → is_equivalence f ∧ is_equivalence g ∧ is_equivalence (f · g)).
  { intros.
    induction X0.
    - apply (S1 a).
    - apply (h b).
  }
  apply (hinhuniv S5).
Qed.

(*TODOLemma section_of_equiv_is_equiv {C : category_equivs_fibs} {X Y : C} (f : X ~~> Y) (s : Y --> X) (is_section_s : is_section f s) : is_section s.*)

Definition equivalences_closed_composition {C : category_equivs_fibs} {X Y Z : C} (f : X --> Y) (g : Y --> Z) (is_equiv_f : is_equivalence f) (is_equiv_g : is_equivalence g) : is_equivalence (g ∘ f) := pr2 (pr2 (equivs_two_out_of_three f g (hdisj_in1 (is_equiv_f,,is_equiv_g)))).

Definition trivfibs_closed_composition {C : category_equivs_fibs} {X Y Z : C} (f : X --> Y) (g : Y --> Z) (is_trivfib_f : is_trivial_fibration f) (is_trivfib_g : is_trivial_fibration g) : is_trivial_fibration (g ∘ f) := (fibrations_closed_composition f g (pr1 is_trivfib_f) (pr1 is_trivfib_g),,equivalences_closed_composition f g (pr2 is_trivfib_f) (pr2 is_trivfib_g)).

Definition any_pr1_fib_if_pr1_fib {C : category_equivs_fibs} {A B I : C} {f : A --> I} {p : B --> I} (P Q : Pullback f p) (is_fib_pr1_P : is_fibration (PullbackPr1 P)): is_fibration (PullbackPr1 Q).
Proof.
  pose (pullbackiso Q P).
  destruct t as [[g g_iso] [eq1 eq2]].
  pose (pr1 (iso_is_trivial_fibration g (is_iso_from_is_z_iso _ g_iso))).
  rewrite (! eq1).
  apply fibrations_closed_composition.
  - exact h.
  - apply is_fib_pr1_P.
Qed.

Definition any_pr1_equiv_if_pr1_equiv {C : category_equivs_fibs} {A B I : C} {f : A --> I} {p : B --> I} (P Q : Pullback f p) (is_equiv_pr1_P : is_equivalence (PullbackPr1 P)): is_equivalence (PullbackPr1 Q).
Proof.
  pose (pullbackiso Q P).
  destruct t as [[g g_iso] [eq1 eq2]].
  pose (iso_is_trivial_fibration g (is_iso_from_is_z_iso _ g_iso)).
  rewrite (! eq1).
  apply equivalences_closed_composition.
  - exact (pr2 h).
  - apply is_equiv_pr1_P.
Qed.
Definition any_pr1_trivfib_if_pr1_trivfib {C : category_equivs_fibs} {A B I : C} {f : A --> I} {p : B --> I} (P Q : Pullback f p) (is_trivfib_pr1_P : is_trivial_fibration (PullbackPr1 P)): is_trivial_fibration (PullbackPr1 Q) := (any_pr1_fib_if_pr1_fib P Q (pr1 is_trivfib_pr1_P),,any_pr1_equiv_if_pr1_equiv P Q (pr2 is_trivfib_pr1_P)).


Definition is_prepathcategory (C : category_equivs_fibs) : UU :=
  (∑ (T : Terminal C) , ∏ A (f : A --> T) , is_fibration f) (* C has a terminal object T and all maps to T are fibrations *)
  ×
  (∏ (A B I : C) (f : A --> I) (p : B -|> I) , ∑ P : Pullback f p, is_fibration (PullbackPr1 P)) (* The pullback of a fibrations along any map exists and is a fibration *)
  ×
  (∏ (A B I : C) (f : A --> I) (p : B ~|> I) , ∏ P : Pullback f p, is_trivial_fibration (PullbackPr1 P)) (* The pullback of a trivial fibration along any map is a trivial fibration *)
  ×
  (∏ (A B : C) (f : A ~|> B) , ∑ s : B --> A , is_section f s) (* Every trivial fibration has a section *).

Definition make_is_prepathcategory {C : category_equivs_fibs}
           (terminal : ∑ (T : Terminal C) , ∏ A (f : A --> T) , is_fibration f)
           (pullback_along_fibs : ∏ (A B I : C) (f : A --> I) (p : B -|> I) , ∑ P : Pullback f p, is_fibration (PullbackPr1 P))
           (pullback_along_trivfibs_is_fibs : ∏ (A B I : C) (f : A --> I) (p : B ~|> I) , ∏ P : Pullback f p, is_trivial_fibration (PullbackPr1 P))
           (trivfibs_have_sections : ∏ (A B : C) (f : A ~|> B) , ∑ s : B --> A , is_section f s) : is_prepathcategory C := (terminal,,pullback_along_fibs,,pullback_along_trivfibs_is_fibs,,trivfibs_have_sections).
Definition prepathcategory : UU := ∑ X , is_prepathcategory X.
Definition make_prepathcategory (C : category_equivs_fibs) (H : is_prepathcategory C) := (C,,H).

Definition category_equivs_fibs_data_from_prepathcategory (C : prepathcategory) := pr1 C.
Coercion category_equivs_fibs_data_from_prepathcategory : prepathcategory >-> category_equivs_fibs.


Definition is_prepathcategory_compact (C : category_equivs_fibs) :=
  (∑ (T : Terminal C) , ∏ A (f : A --> T) , is_fibration f)
  ×
  (∏ (A B I : C) (f : A --> I) (p : B -|> I) , ∑ P : Pullback f p, is_fibration (PullbackPr1 P) × (is_equivalence p → is_equivalence (PullbackPr1 P)))
  ×
  (∏ (A B : C) (f : A ~|> B) , ∑ s : B --> A , is_section f s).

Definition make_is_prepathcategory_compact (C : category_equivs_fibs)
  (terminal : ∑ (T : Terminal C) , ∏ A (f : A --> T) , is_fibration f)
  (pullbacks : ∏ (A B I : C) (f : A --> I) (p : B -|> I) , ∑ P : Pullback f p, is_fibration (PullbackPr1 P) × (is_equivalence p → is_equivalence (PullbackPr1 P)))
  (sections : ∏ (A B : C) (f : A ~|> B) , ∑ s : B --> A , is_section f s) : is_prepathcategory_compact C := (terminal,,pullbacks,,sections).

Definition is_prepathcategory_from_compact {C : category_equivs_fibs} (H : is_prepathcategory_compact C) : is_prepathcategory C.
Proof.
  destruct H as [terminal [pullbacks sections]].
  use make_is_prepathcategory.
  - exact terminal.
  - intros.
    destruct (pullbacks _ _ _ f p) as [P [is_fib is_equiv]].
    use tpair.
    + exact P.
    + exact is_fib.
  - intros.
    destruct (pullbacks _ _ _ f p) as [Q [is_fib is_equiv]].
    split.
    + apply (any_pr1_fib_if_pr1_fib Q P).
      exact is_fib.
    + apply (any_pr1_equiv_if_pr1_equiv Q P).
      apply is_equiv.
      apply p.
  - exact sections.
Defined.

Definition makeprepathcategory
           (C : category)
           (equivs : ∏ a b : C , hsubtype (a --> b))
           (fibs : ∏ a b : C , hsubtype (a --> b))
           (C_pre := make_category_equivs_fibs_data C equivs fibs)
           (isos_are_trivs : ∏ (A B : C_pre) (f : A --> B) , is_iso f → is_trivial_fibration f)
           (fibs_closed_composition : ∏ (X Y Z : C_pre) (f : X --> Y) (g : Y --> Z) , is_fibration f → is_fibration g → is_fibration (g ∘ f))
           (equivs_two_out_of_six_fst : ∏ (X Y Z W : C_pre) (f : X --> Y) (g : Y --> Z) (h : Z --> W) , is_equivalence (g ∘ f) → is_equivalence (h ∘ g) → is_equivalence f)
           (equivs_two_out_of_six_snd : ∏ (X Y Z W : C_pre) (f : X --> Y) (g : Y --> Z) (h : Z --> W) , is_equivalence (g ∘ f) → is_equivalence (h ∘ g) → is_equivalence g)
           (equivs_two_out_of_six_trd : ∏ (X Y Z W : C_pre) (f : X --> Y) (g : Y --> Z) (h : Z --> W) , is_equivalence (g ∘ f) → is_equivalence (h ∘ g) → is_equivalence h)
           (equivs_two_out_of_six_all : ∏ (X Y Z W : C_pre) (f : X --> Y) (g : Y --> Z) (h : Z --> W) , is_equivalence (g ∘ f) → is_equivalence (h ∘ g) → is_equivalence (h ∘ g ∘ f))
           (T : Terminal C)
           (maps_to_T_are_fibs : ∏ (A : C_pre) (f : A --> T) , is_fibration f)
           (pullback_fib_along_mor : ∏ (A B I : C_pre) (f : A --> I) (p : B -|> I) , Pullback f p)
           (pullback_maybetriv_fib_along_mor_is_maybetriv_fib : ∏ (A B I : C_pre) (f : A --> I) (p : B -|> I) , is_fibration (PullbackPr1 (pullback_fib_along_mor A B I f p)) × (is_equivalence p → is_equivalence (PullbackPr1 (pullback_fib_along_mor A B I f p))))
           (trivfibs_has_sections : ∏ (A B : C_pre) (f : A ~|> B) , ∑ (s : B --> A) , is_section f s) : prepathcategory.
Proof.
  use make_prepathcategory.
  - use make_category_equivs_fibs.
    + exact C_pre.
    + use make_is_category_equivs_fibs.
      * exact isos_are_trivs.
      * exact fibs_closed_composition.
      * intros.
        exact (equivs_two_out_of_six_fst X Y Z W f g h X0 X1,,equivs_two_out_of_six_snd X Y Z W f g h X0 X1,,equivs_two_out_of_six_trd X Y Z W f g h X0 X1,,equivs_two_out_of_six_all X Y Z W f g h X0 X1).
  - apply is_prepathcategory_from_compact.
    use make_is_prepathcategory_compact.
    + exists T.
      exact maps_to_T_are_fibs.
    + intros.
      exists (pullback_fib_along_mor A B I f p).
      apply pullback_maybetriv_fib_along_mor_is_maybetriv_fib.
    + exact trivfibs_has_sections.
Qed.

Definition terminal_object (C : prepathcategory) : Terminal C := pr1 (pr1 (pr2 C)).
Definition terminal_morphism {C : prepathcategory} (A : C) : A --> terminal_object C := TerminalArrow (terminal_object C) A.
Definition terminal_morphism_is_fibration {C : prepathcategory} (A : C) : is_fibration (terminal_morphism A) := pr2 (pr1 (pr2 C)) A (terminal_morphism A).
Definition terminal_fibration {C : prepathcategory} (A : C) : A -|> terminal_object C := make_fibration (terminal_morphism A) (terminal_morphism_is_fibration A).

Definition pullback_fib_along_mor {C : prepathcategory} {A B I : C} (f : A --> I) (p : B -|> I) : Pullback f p := pr1 (pr1 (pr2 (pr2 C)) A B I f p).
Definition pullback_fib_along_mor_is_fib {C : prepathcategory} {A B I : C} (f : A --> I) (p : B -|> I) : is_fibration (PullbackPr1 (pullback_fib_along_mor f p)) := pr2 (pr1 (pr2 (pr2 C)) A B I f p).
Definition any_pullback_fib_along_mor_is_fib {C : prepathcategory} {A B I : C} {f : A --> I} {p : B -|> I} (P : Pullback f p) : is_fibration (PullbackPr1 P) := any_pr1_fib_if_pr1_fib _ P(pullback_fib_along_mor_is_fib f p).
Definition fibration_pullback_pr1 {C : prepathcategory} {A B I : C} {f : A --> I} {p : B -|> I} (P : Pullback f p) : P -|> A := make_fibration (PullbackPr1 P) (any_pullback_fib_along_mor_is_fib P).

Lemma any_pullback_mor_along_fib_is_fib {C : prepathcategory} {A B I : C} {p : A -|> I} {f : B --> I} (P : Pullback p f) : is_fibration (PullbackPr2 P).
Proof.
  pose (is_symmetric_isPullback (homset_property C) _ (pr22 P)).
  unfold PullbackPr2.
  pose (make_Pullback _ _ _ _ _ _ i).
  apply (any_pullback_fib_along_mor_is_fib p0).
Qed.
Definition fibration_pullback_pr2 {C : prepathcategory} {A B I : C} {p : A -|> I} {f : B --> I} (P : Pullback p f) : P -|> B := make_fibration (PullbackPr2 P) (any_pullback_mor_along_fib_is_fib P).


Definition pullback_trivfib_along_mor {C : prepathcategory} {A B I : C} (f : A --> I) (p : B ~|> I) : Pullback f p := pullback_fib_along_mor f p.
Definition pullback_trivfib_along_mor_is_trivfib {C : prepathcategory} {A B I : C} (f : A --> I) (p : B ~|> I) : is_trivial_fibration (PullbackPr1 (pullback_trivfib_along_mor f p)) := pr1 (pr2 (pr2 (pr2 C))) A B I f p  (pullback_trivfib_along_mor f p).
Definition any_pullback_trivfib_along_mor_is_trivfib {C : prepathcategory} {A B I : C} {f : A --> I} {p : B ~|> I} (P : Pullback f p) : is_trivial_fibration (PullbackPr1 P) := any_pr1_trivfib_if_pr1_trivfib _ P (pullback_trivfib_along_mor_is_trivfib f p).

Definition trivfib_pullback {C : prepathcategory} {A B I : C} (f : A --> I) (p : B ~|> I) (P : Pullback f p) : P ~|> A := make_trivial_fibration (PullbackPr1 P) (pr1 (any_pullback_trivfib_along_mor_is_trivfib P)) (pr2 (any_pullback_trivfib_along_mor_is_trivfib P)).

Lemma any_pullback_mor_along_trivfib_is_trivfib {C : prepathcategory} {A B I : C} {p : A ~|> I} {f : B --> I} (P : Pullback p f) : is_trivial_fibration (PullbackPr2 P).
Proof.
  pose (is_symmetric_isPullback (homset_property C) _ (pr22 P)).
  unfold PullbackPr2.
  pose (make_Pullback _ _ _ _ _ _ i).
  apply (any_pullback_trivfib_along_mor_is_trivfib p0).
Qed.
Definition trivial_fibration_pullback_pr2 {C : prepathcategory} {A B I : C} (p : A ~|> I) (f : B --> I) (P : Pullback p f) : P ~|> B := make_trivial_fibration (PullbackPr2 P) (pr1 (any_pullback_mor_along_trivfib_is_trivfib P)) (pr2 (any_pullback_mor_along_trivfib_is_trivfib P)).


Definition binproduct {C : prepathcategory} (A B : C) : BinProduct C A B := binproduct_from_pullback_over_terminal (pullback_fib_along_mor (terminal_morphism A) (terminal_fibration B)).
Definition binproduct_pr1_is_fib {C : prepathcategory} (A B : C) : is_fibration (BinProductPr1 C (binproduct A B)):= pullback_fib_along_mor_is_fib (terminal_morphism A) (terminal_fibration B).
Definition any_binproduct_pr1_is_fib {C: prepathcategory} {A B : C} (P : BinProduct C A B) : is_fibration (BinProductPr1 C P).
Proof.
  pose (f := BinProductArrow _ (binproduct A B) (BinProductPr1 _ _) (BinProductPr2 C P)).
  pose (g := BinProductArrow _ P (BinProductPr1 C (binproduct A B)) (BinProductPr2 _ _)).
  assert (is_iso f).
  apply (is_iso_qinv _ g).
  split.
  apply pathsinv0.
  apply BinProduct_endo_is_identity.
  rewrite (! (assoc f g (BinProductPr1 C P))).
  unfold g; rewrite BinProductPr1Commutes.
  unfold f; rewrite BinProductPr1Commutes.
  auto.
  rewrite (! (assoc f g (BinProductPr2 C P))).
  unfold g; rewrite BinProductPr2Commutes.
  unfold f; rewrite BinProductPr2Commutes.
  auto.
  apply pathsinv0.
  apply BinProduct_endo_is_identity.
  rewrite (! (assoc g f (BinProductPr1 C (binproduct A B)))).
  unfold f; rewrite BinProductPr1Commutes.
  unfold g; rewrite BinProductPr1Commutes.
  auto.
  rewrite (! (assoc g f (BinProductPr2 C (binproduct A B)))).
  unfold f; rewrite BinProductPr2Commutes.
  unfold g; rewrite BinProductPr2Commutes.
  auto.
  pose (pr1 (iso_is_trivial_fibration f X)).
  rewrite (! (BinProductPr1Commutes C A B (binproduct A B)) P (BinProductPr1 C P) (BinProductPr2 C P)).
  apply fibrations_closed_composition.
  exact h.
  apply binproduct_pr1_is_fib.
Qed.
Definition binproduct_pr2_is_fib {C : prepathcategory} (A B : C) : is_fibration (BinProductPr2 C (binproduct A B)) := any_pullback_mor_along_fib_is_fib (p:=terminal_fibration A) (pullback_fib_along_mor (terminal_morphism A) (terminal_fibration B)).
Definition any_binproduct_pr2_is_fib {C : prepathcategory} {A B : C} (P : BinProduct C A B) : is_fibration (BinProductPr2 C P).
Proof.
  pose (f := BinProductArrow _ (binproduct A B) (BinProductPr1 _ _) (BinProductPr2 C P)).
  pose (g := BinProductArrow _ P (BinProductPr1 C (binproduct A B)) (BinProductPr2 _ _)).
  assert (is_iso f).
  apply (is_iso_qinv _ g).
  split.
  apply pathsinv0.
  apply BinProduct_endo_is_identity.
  rewrite (! (assoc f g (BinProductPr1 C P))).
  unfold g; rewrite BinProductPr1Commutes.
  unfold f; rewrite BinProductPr1Commutes.
  auto.
  rewrite (! (assoc f g (BinProductPr2 C P))).
  unfold g; rewrite BinProductPr2Commutes.
  unfold f; rewrite BinProductPr2Commutes.
  auto.
  apply pathsinv0.
  apply BinProduct_endo_is_identity.
  rewrite (! (assoc g f (BinProductPr1 C (binproduct A B)))).
  unfold f; rewrite BinProductPr1Commutes.
  unfold g; rewrite BinProductPr1Commutes.
  auto.
  rewrite (! (assoc g f (BinProductPr2 C (binproduct A B)))).
  unfold f; rewrite BinProductPr2Commutes.
  unfold g; rewrite BinProductPr2Commutes.
  auto.
  pose (pr1 (iso_is_trivial_fibration f X)).
  rewrite (! (BinProductPr2Commutes C A B (binproduct A B)) P (BinProductPr1 C P) (BinProductPr2 C P)).
  apply fibrations_closed_composition.
  exact h.
  apply binproduct_pr2_is_fib.
Qed.

Definition binproduct_pr1_fibration {C : prepathcategory} {A B : C} (P : BinProduct C A B) : P -|> A := make_fibration (BinProductPr1 C P) (any_binproduct_pr1_is_fib P).
Definition binproduct_pr2_fibration {C : prepathcategory} {A B : C} (P : BinProduct C A B) : P -|> B := make_fibration (BinProductPr2 C P) (any_binproduct_pr2_is_fib P).

Section PathObjects.
  Context (C : precategory_equivs_fibs_data).
  Hypotheses H :  (∏ A : C , Product bool C (λ _ , A)).
  Hypotheses has_H : (∏ A : C , ∥ Product bool C (λ _ , A) ∥).

  Definition pathobject_data (A : C) :=
    ∑ PA , (A --> PA) × (PA --> self_product C H A).

  Definition make_pathobject_data (A : C) (PA : C) (r : A --> PA) (st : PA --> self_product C H A) : pathobject_data A := tpair _ PA (r,,st).
  Definition object_from_pathobject_data {A : C} (PA : pathobject_data A) := pr1 PA.
  Coercion object_from_pathobject_data : pathobject_data >-> ob.

  Definition rmap {A : C} (PA : pathobject_data A) : A --> PA := pr1 (pr2 PA).
  Definition stmap {A : C} (PA : pathobject_data A): PA --> self_product C H A := pr2 (pr2 PA).
  Definition smap {A : C} (PA : pathobject_data A) : PA --> A := ProductPr bool C (H A) true ∘ pr2 (pr2 PA).
  Definition tmap {A : C} (PA : pathobject_data A) : PA --> A := ProductPr bool C (H A) false ∘ pr2 (pr2 PA).

  Definition is_pathobject (A : C) (PA : pathobject_data A) :=
    (equivalences A PA (rmap PA)) × (fibrations PA (self_product C H A) (stmap PA)) × ((stmap PA) ∘ (rmap PA) = diagonal C H A).

  Lemma isaprop_is_pathobject (A : C) (PA : pathobject_data A) (hs : has_homsets C) : isaprop (is_pathobject A PA).
  Proof.
    apply isofhleveltotal2.
    apply propproperty.
    intro.
    apply isofhleveltotal2.
    apply propproperty.
    intro.
    apply hs.
  Qed.

  Definition pathobject (A : C) := total2 (is_pathobject A).
  Definition has_pathobject (A : C) := ∥ pathobject A ∥. (* incorrect? need to use has_H? *)
  Definition make_pathobject (A : C) (PA : pathobject_data A) (isPA : is_pathobject A PA) := (PA,,isPA).
  Definition pathobject_data_from_pathobject {A : C} (PA : pathobject A) := pr1 PA.
  Coercion pathobject_data_from_pathobject : pathobject >-> pathobject_data.

  Definition is_equivelance_rmap (A : C) (PA : pathobject A) : equivalences A PA (rmap PA) := pr1 (pr2 PA).
  Definition is_fibration_stmap (A : C) (PA : pathobject A) : fibrations PA (self_product C H A) (stmap PA) := pr1 (pr2 (pr2 PA)).
  Definition factor_diagonal (A : C) (PA : pathobject A) := pr2 (pr2 (pr2 PA)).

End PathObjects.

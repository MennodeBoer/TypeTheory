(**
  [TypeTheory.ALV2.TypeCat_ComprehensionCat]

  Part of the [TypeTheory] library (Ahrens, Lumsdaine, Voevodsky, 2015–present).
*)

(**
This module defines a comprehension category induced by a (non-split) type category.

Main definition is

- [typecat_to_comprehension_cat] - comprehension category induced by a type category;

Important parts are:

- [typecat_disp] - displayed category induced by a type category (or rather by its object extension substructure);
- [typecat_disp_is_disp_univalent] - induced displayed category is univalent when [typecat_idtoiso_triangle] is an equivalence;
- [cleaving_typecat_disp] - induced displayed category is a fibration;

- [typecat_disp_functor] - a comprehension functor induced by a type category;
- [typecat_disp_functor_ff] - induced displayed functor is fully faithful;
- [typecat_disp_functor_is_cartesian] - induced displayed functor is cartesian.

*)

Require Import UniMath.MoreFoundations.PartA.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.TypeCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.

Section Auxiliary.

  (* TODO: move upstream? *)
  Lemma isPullback_swap
        {C : precategory}
        {a b c d : C} {f : b --> a} {g : c --> a}
        {p1 : d --> b} {p2 : d --> c} {H : p1 · f = p2 · g}
        (pb : isPullback f g p1 p2 H)
  : isPullback _ _ _ _ (! H).
  Proof.
    use make_isPullback.
    intros e h k H'.
    use (iscontrweqf _ (pb e k h (! H'))).
    use (weqtotal2 (idweq _)).
    intros ?. apply weqdirprodcomm.
  Defined.

  (* TODO: move upstream? *)
  Definition pr1_transportb
             {A : UU} {B : A → UU} (P : ∏ a : A, B a → UU) {a a' : A}
             (e : a = a') (xs : ∑ b : B a', P a' b)
    : pr1 (transportb (λ x : A, ∑ b : B x, P x b) e xs) =
      transportb (λ x : A, B x) e (pr1 xs).
  Proof.
    induction e.
    apply idpath.
  Defined.

  (* TODO: move upstream? *)
  Lemma weqtotaltoforall3 {X : UU}
        (P1 : X → UU)
        (P2 : ∏ x : X, P1 x → UU)
        (P3 : ∏ (x : X) (y : P1 x), P2 x y → UU)
    : (∑ (p1 : ∏ x : X, P1 x) (p2 : ∏ x : X, P2 x (p1 x)), ∏ x : X, P3 x (p1 x) (p2 x))
        ≃ (∏ x : X, ∑ (p1 : P1 x) (p2 : P2 x p1), P3 x p1 p2).
  Proof.
    eapply weqcomp.
    apply (weqtotal2asstol
             (λ p1, ∏ x : X, P2 x (p1 x))
             (λ p12, ∏ x : X, P3 x (pr1 p12 x) (pr2 p12 x))
          ).
    eapply weqcomp.
    use weqtotal2. 3: apply weqtotaltoforall.
    - exact (λ p12, ∏ x : X, P3 x (pr1 (p12 x)) (pr2 (p12 x))).
    - intros x. apply idweq.

    - eapply weqcomp.
      apply (weqtotaltoforall
               (λ x : X, ∑ y : P1 x, P2 x y)
               (λ (x : X) p12, P3 x (pr1 p12) (pr2 p12))
            ).
      apply weqonsecfibers.
      intros x.
      apply weqtotal2asstor.
  Defined.

  (* TODO: move upstream? *)
  Lemma iscontr_total2
        {X : UU} {P : X → UU}
    : iscontr X → (∏ x : X, iscontr (P x)) → iscontr (∑ (x : X), P x).
  Proof.
    intros X_contr P_contr.
    use tpair.
    - exists (pr1 X_contr). apply P_contr.
    - intros xp.
      use total2_paths_f.
      + apply X_contr.
      + apply P_contr.
  Defined.

  Definition disp_ff_functor_to_on_objects
             {C : category}
             (D' : disp_cat C)
    : UU
    := ∑ (obd : C → UU)
       , ∏ (Γ : C), obd Γ → D' Γ.

  Check weqtotaltoforall.

  Definition disp_ff_functor_on_morphisms_sop
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
    : UU
    := ∑ (mord : ∏ Γ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
         (functor_mord : ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
                         , (mord _ _ A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
       , ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
       , isweq (functor_mord Γ Γ' A A' f).

  Definition disp_ff_functor_on_morphisms_pos
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
    : UU
    := ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ'),
      ∑ (mord : UU), mord ≃ (pr2 D _ A -->[ f ] pr2 D _ A').

  Definition disp_ff_functor_on_morphisms_sop_pos_weq
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
    : disp_ff_functor_on_morphisms_sop D ≃ disp_ff_functor_on_morphisms_pos D.
  Proof.
    eapply weqcomp.
    apply (weqtotaltoforall3
             (λ Γ, ∏ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
             (λ Γ mord, ∏ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
              , (mord _ A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
             (λ Γ mord functor_mord, 
              ∏ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
              , isweq (functor_mord Γ' A A' f))).
    apply weqonsecfibers. intros Γ.

    eapply weqcomp.
    apply (weqtotaltoforall3
             (λ Γ', (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU)
             (λ Γ' mord, ∏ (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
              , (mord A A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
             (λ Γ' mord functor_mord, 
              ∏ (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
              , isweq (functor_mord A A' f))).
    apply weqonsecfibers. intros Γ'.

    eapply weqcomp.
    apply (weqtotaltoforall3
             (λ A, (pr1 D Γ') → (Γ --> Γ') → UU)
             (λ A mord, ∏ (A' : pr1 D Γ') (f : Γ --> Γ')
              , (mord A' f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
             (λ A mord functor_mord, 
              ∏ (A' : pr1 D Γ') (f : Γ --> Γ')
              , isweq (functor_mord A' f))).
    apply weqonsecfibers. intros A.

    eapply weqcomp.
    apply (weqtotaltoforall3
             (λ A', (Γ --> Γ') → UU)
             (λ A' mord, ∏ (f : Γ --> Γ')
              , (mord f) -> (pr2 D _ A -->[ f ] pr2 D _ A'))
             (λ A' mord functor_mord, 
              ∏ (f : Γ --> Γ')
              , isweq (functor_mord f))).
    apply weqonsecfibers. intros A'.

    eapply weqcomp.
    apply (weqtotaltoforall3
             (λ f, UU)
             (λ f mord, mord -> (pr2 D _ A -->[ f ] pr2 D _ A'))
             (λ f mord functor_mord, isweq functor_mord)).
    apply idweq.
  Defined.

  Definition disp_ff_functor_on_morphisms_pos_iscontr
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
    : iscontr (disp_ff_functor_on_morphisms_pos D).
  Proof.
    apply impred_iscontr. intros Γ.
    apply impred_iscontr. intros Γ'.
    apply impred_iscontr. intros A.
    apply impred_iscontr. intros A'.
    apply impred_iscontr. intros f.
    use (@iscontrweqf (∑ mord : UU, mord = pr2 D Γ A -->[f] pr2 D Γ' A')).
    - use (weqtotal2 (idweq _)). intros mord. apply univalenceweq.
    - apply iscontrcoconustot.
  Defined.

  Definition disp_ff_functor_on_morphisms_pos_isaprop
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
    : isaprop (disp_ff_functor_on_morphisms_pos D).
  Proof.
    apply isapropifcontr, disp_ff_functor_on_morphisms_pos_iscontr.
  Defined.

  Definition disp_ff_functor_on_morphisms_id_pos
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
             (mor_weq : disp_ff_functor_on_morphisms_pos D)
    : UU
    := ∏ (Γ : C) (A : pr1 D Γ),
       ∑ (mor_id : pr1 (mor_weq Γ Γ A A (identity Γ))),
       pr1 (pr2 (mor_weq Γ Γ A A (identity Γ))) mor_id
       = transportb (mor_disp (pr2 D Γ A) (pr2 D Γ A))
                    (functor_id (functor_identity C) Γ) (id_disp (pr2 D Γ A)).

  Definition disp_ff_functor_on_morphisms_id_pos_iscontr
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
             (mor_weq : disp_ff_functor_on_morphisms_pos D)
             (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
    : iscontr (disp_ff_functor_on_morphisms_id_pos D mor_weq).
  Proof.
    apply impred_iscontr. intros Γ.
    apply impred_iscontr. intros A.
    set (mord := pr1 (mor_weq Γ Γ A A (identity Γ))).
    set (mord_weq := pr2 (mor_weq Γ Γ A A (identity Γ))).
    use (@iscontrweqf (∑ mor_id : mord, mor_id = invweq mord_weq
                                    (transportb (mor_disp (pr2 D Γ A) (pr2 D Γ A))
                                                (functor_id (functor_identity C) Γ) (id_disp (pr2 D Γ A))))).
    - use (weqtotal2 (idweq _)). intros mor_id. simpl.
      use weq_iso.
      + intros p. apply (maponpaths mord_weq p @ homotweqinvweq mord_weq _).
      + intros p. apply (! homotinvweqweq mord_weq _ @ maponpaths (invmap mord_weq) p).
      + intros p. apply mor_isaset.
      + intros p. apply (@homsets_disp _ D').
    - apply iscontrcoconustot.
  Defined.

  Definition disp_ff_functor_on_morphisms_comp_pos
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
             (mor_weq : disp_ff_functor_on_morphisms_pos D)
    : UU
    := ∏ (Γ Γ' Γ'' : C)
         (A : pr1 D Γ) (A' : pr1 D Γ') (A'' : pr1 D Γ'')
         (f : Γ --> Γ') (g : Γ' --> Γ'')
         (ff : pr1 (mor_weq Γ Γ' A A' f))
         (gg : pr1 (mor_weq Γ' Γ'' A' A'' g)),
       ∑ (mor_comp : pr1 (mor_weq Γ Γ'' A A'' (f ;; g))),
       pr2 (mor_weq Γ Γ'' A A'' (f ;; g)) mor_comp
       = transportb _ (functor_comp (functor_identity C) f g)
                    (comp_disp (pr2 (mor_weq _ _ _ _ _) ff) (pr2 (mor_weq _ _ _ _ _) gg)).

  Definition disp_ff_functor_on_morphisms_comp_pos_iscontr
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
             (mor_weq : disp_ff_functor_on_morphisms_pos D)
             (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
    : iscontr (disp_ff_functor_on_morphisms_comp_pos D mor_weq).
  Proof.
    apply impred_iscontr. intros Γ.
    apply impred_iscontr. intros Γ'.
    apply impred_iscontr. intros Γ''.
    apply impred_iscontr. intros A.
    apply impred_iscontr. intros A'.
    apply impred_iscontr. intros A''.
    apply impred_iscontr. intros f.
    apply impred_iscontr. intros g.
    apply impred_iscontr. intros ff.
    apply impred_iscontr. intros gg.
    set (mord := pr1 (mor_weq Γ Γ'' A A'' (f ;; g))).
    set (mord_weq := pr2 (mor_weq Γ Γ'' A A'' (f ;; g))).
    use (@iscontrweqf (∑ mor_comp : mord,
       mor_comp
       = invweq mord_weq (transportb _ (functor_comp (functor_identity C) f g)
                    (comp_disp (pr2 (mor_weq _ _ _ _ _) ff) (pr2 (mor_weq _ _ _ _ _) gg))))).
    - use (weqtotal2 (idweq _)). intros mor_id. simpl.
      use weq_iso.
      + intros p. apply (maponpaths mord_weq p @ homotweqinvweq mord_weq _).
      + intros p. apply (! homotinvweqweq mord_weq _ @ maponpaths (invmap mord_weq) p).
      + intros p. apply mor_isaset.
      + intros p. apply (@homsets_disp _ D').
    - apply iscontrcoconustot.
  Defined.

  Definition disp_ff_functor_source_mor_isaset
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
             (mor_weq : disp_ff_functor_on_morphisms_pos D)
    : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)).
  Proof.
    intros Γ Γ' f A A'.
    set (w := pr2 (mor_weq Γ Γ' A A' f)).
    use (isofhlevelweqf 2 (invweq w)).
    apply (@homsets_disp _ D').
  Defined.

  Definition disp_ff_functor_source_mor_isaset_iscontr
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
             (mor_weq : disp_ff_functor_on_morphisms_pos D)
    : iscontr (∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f))).
  Proof.
    apply iscontraprop1.
    - apply impred_isaprop. intros Γ.
      apply impred_isaprop. intros Γ'.
      apply impred_isaprop. intros A.
      apply impred_isaprop. intros A'.
      apply impred_isaprop. intros f.
      apply isapropisaset.
    - apply disp_ff_functor_source_mor_isaset.
  Defined.

  Definition disp_ff_functor_on_morphisms_idcomp_pos
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
    : UU
    := ∑ (mor_weq : disp_ff_functor_on_morphisms_pos D)
         (mor_isaset : ∏ Γ Γ' f (A : pr1 D Γ) (A' : pr1 D Γ'), isaset (pr1 (mor_weq _ _ A A' f)))
         (mor_id : disp_ff_functor_on_morphisms_id_pos D mor_weq)
       , disp_ff_functor_on_morphisms_comp_pos D mor_weq.

  Definition disp_ff_functor_on_morphisms_idcomp_pos_iscontr
             {C : category} {D' : disp_cat C}
             (D : disp_ff_functor_to_on_objects D')
    : iscontr (disp_ff_functor_on_morphisms_idcomp_pos D).
  Proof.
    apply iscontr_total2.
    - apply disp_ff_functor_on_morphisms_pos_iscontr.
    - intros mor_weq. apply iscontr_total2.
      + apply disp_ff_functor_source_mor_isaset_iscontr.
      + intros mor_isaset.
        apply iscontr_total2.
        * apply disp_ff_functor_on_morphisms_id_pos_iscontr.
          apply mor_isaset.
        * intros ?.
          apply disp_ff_functor_on_morphisms_comp_pos_iscontr.
          apply mor_isaset.
  Defined.

  (* Types for parts of a fully faithful functor that rely on morphisms *)
  Section disp_ff_functor_to_on_morphisms.

    Context {C : category} {D' : disp_cat C}.
    Context (D : disp_ff_functor_to_on_objects D').

    Definition disp_ff_functor_source_mor : UU
      := ∏ (Γ Γ' : C), (pr1 D Γ) → (pr1 D Γ') → (Γ --> Γ') → UU.

    Definition disp_ff_functor_source_id_comp
               (mord : disp_ff_functor_source_mor) : UU
      := disp_cat_id_comp C (pr1 D,, mord).

    Definition disp_ff_functor_source_axioms
               (mord : disp_ff_functor_source_mor)
               (id_comp_d : disp_ff_functor_source_id_comp mord)
      : UU
      := disp_cat_axioms C ((pr1 D ,, mord) ,, id_comp_d).

    Definition disp_ff_functor_on_morphisms
               (mord : disp_ff_functor_source_mor)
      : UU
      := ∏ x y (xx : pr1 D x) (yy : pr1 D y) (f : x --> y)
         , (mord _ _ xx yy f) -> (pr2 D _ xx -->[ f ] pr2 D _ yy).
          
    Definition disp_ff_functor_axioms
               (mord : disp_ff_functor_source_mor)
               (id_comp_d : disp_ff_functor_source_id_comp mord)
               (axioms_d : disp_ff_functor_source_axioms mord id_comp_d)
               (functor_mord : disp_ff_functor_on_morphisms mord)
      : UU
      := @disp_functor_axioms
           C C (functor_identity _)
           (((pr1 D ,, mord) ,, id_comp_d) ,, axioms_d) D'
           (pr2 D ,, functor_mord).
               
    Definition disp_ff_functor_ff
               (mord : disp_ff_functor_source_mor)
               (functor_mord : disp_ff_functor_on_morphisms mord)
      : UU
      := ∏ Γ Γ' (A : pr1 D Γ) (A' : pr1 D Γ') (f : Γ --> Γ')
         , isweq (functor_mord Γ Γ' A A' f).

    Definition disp_ff_functor_to_on_morphisms'
               (mord : disp_ff_functor_source_mor)
      : UU
      := ∑ (id_comp_d : disp_ff_functor_source_id_comp mord)
           (axioms_d : disp_ff_functor_source_axioms mord id_comp_d)
           (functor_mord : disp_ff_functor_on_morphisms mord)
           (functor_axioms_d : disp_ff_functor_axioms mord id_comp_d axioms_d functor_mord)
         , disp_ff_functor_ff mord functor_mord.

    Definition disp_ff_functor_to_on_morphisms
      : UU
      := ∑ (mord : disp_ff_functor_source_mor)
         , disp_ff_functor_to_on_morphisms' mord.

  End disp_ff_functor_to_on_morphisms.

  Definition disp_ff_functor_to
             {C : category} (D' : disp_cat C)
    : UU
    := ∑ (D : disp_ff_functor_to_on_objects D'), disp_ff_functor_to_on_morphisms D.

  (* Accessors for parts of a fully faithful functor that rely on morphisms *)
  Section disp_ff_functor_accessors.

    Definition source_disp_cat_of_disp_ff_functor
                {C : category} {D' : disp_cat C}
                (D : disp_ff_functor_to D')
        : disp_cat C.
    Proof.
        set (axioms_d := pr1 (pr2 (pr2 (pr2 D)))).
        exact (((pr1 (pr1 D),, _),, _) ,, axioms_d).
    Defined.

    Definition disp_functor_of_disp_ff_functor
                {C : category} {D' : disp_cat C}
                (D : disp_ff_functor_to D')
        : disp_functor (functor_identity _) (source_disp_cat_of_disp_ff_functor D) D'.
    Proof.
        set (functor_axioms_d := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))).
        exact ((pr2 (pr1 D) ,, _) ,, functor_axioms_d).
    Defined.

    Coercion disp_functor_of_disp_ff_functor : disp_ff_functor_to >-> disp_functor.

    Definition disp_ff_functor_is_ff
                {C : category} {D' : disp_cat C}
                (D : disp_ff_functor_to D')
        : disp_functor_ff (disp_functor_of_disp_ff_functor D)
        := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))).

  End disp_ff_functor_accessors.

End Auxiliary.

Section TypeCat_ObjExt.

  (* Object extension structure is part of the definition of type category that includes:
   * - the type family [ty_typecat] : C → UU;
   * - for every Γ : C and A : Ty(Γ):
   *   - context extension [Γ ◂ A];
   *   - for every morphism f : Γ' --> Γ, reindexing mapping [reind_typecat];
   *   - projection morphism [dpr_typecat_obj_ext]: Γ ◂ A --> Γ.
   *)
  Definition typecat_obj_ext_structure (C : precategory) 
    := ∑ TC : typecat_structure1 C,
              ∏ Γ (A : TC Γ), Γ ◂ A --> Γ.

  Definition typecat1_from_typecat_obj_ext (C : precategory)
             (TC : typecat_obj_ext_structure C) 
    : typecat_structure1 _  := pr1 TC.
  Coercion typecat1_from_typecat_obj_ext : typecat_obj_ext_structure >-> typecat_structure1.

  Definition dpr_typecat_obj_ext {C : precategory}
             {TC : typecat_obj_ext_structure C} {Γ} (A : TC Γ)
    : (Γ ◂ A) --> Γ
    := pr2 TC Γ A.
  
  Definition typecat_obj_ext_from_typecat (C : precategory) (TC : typecat_structure C) 
    : typecat_obj_ext_structure _  := (pr1 TC ,, @dpr_typecat _ TC).
  Coercion typecat_obj_ext_from_typecat : typecat_structure >-> typecat_obj_ext_structure.

End TypeCat_ObjExt.

Local Notation "'π' A" := (dpr_typecat_obj_ext A) (at level 5).

Section TypeCat_Comp_Ext_Compare.

  Context {C : precategory}.
  Context (TC : typecat_obj_ext_structure C).

  Definition typecat_comp_ext_compare
             {Γ : C} {A B : TC Γ}
    : (A = B) → Γ ◂ A --> Γ ◂ B.
  Proof.
    intros p. induction p.
    apply identity.
  Defined.

  Definition typecat_idtoiso_dpr
             {Γ : C} {A B : TC Γ}
             (p : A = B)
    : idtoiso (maponpaths (λ B, Γ ◂ B) p) ;; π B = π A.
  Proof.
    induction p. apply id_left.
  Defined.

  Definition typecat_iso_triangle
             {Γ : C} (A B : TC Γ)
    := ∑ (i : iso (Γ ◂ A) (Γ ◂ B)),
       i ;; π B = π A.

  Definition typecat_iso_triangle_swap
             {Γ : C} {A B : TC Γ}
    : typecat_iso_triangle A B → typecat_iso_triangle B A.
  Proof.
    intros tr.
    exists (iso_inv_from_iso (pr1 tr)).
    etrans. apply maponpaths, pathsinv0, (pr2 tr).
    etrans. apply assoc.
    etrans. apply maponpaths_2, iso_after_iso_inv.
    apply id_left.
  Defined.

  Definition typecat_idtoiso_triangle
             {Γ : C} (A B : TC Γ)
    : (A = B) → typecat_iso_triangle A B.
  Proof.
    intros p. induction p.
    use tpair.
    - apply identity_iso.
    - apply id_left.
  Defined.

End TypeCat_Comp_Ext_Compare.

Section TypeCat_Disp.

  (* Type category (or rather its object extension part)
   * induces a displayed category over C with
   * - objects over Γ : C being types A : Ty(Γ)
   * - morphisms from A' to A over f : Γ' --> Γ being a morphism
         ff : Γ.A' --> Γ.A making the square with projections and f commute.
   *)
  Definition typecat_disp_ob_mor
             {C : precategory} (TC : typecat_obj_ext_structure C)
  : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - apply TC.
    - intros Γ' Γ A' A f.
      exact (∑ ff : Γ' ◂ A' --> Γ ◂ A,
                    ff ;; π A = π A' ;; f).
  Defined.

  Definition typecat_disp_id_comp
             {C : precategory} (TC : typecat_obj_ext_structure C)
    : disp_cat_id_comp _ (typecat_disp_ob_mor TC).
    split.
    + intros Γ A; cbn in *.
      use tpair.
      * apply identity.
      * cbn. etrans. apply id_left. apply pathsinv0, id_right.
    + intros ? ? ? ? ? ? ? ? ff gg; cbn in *.
      use tpair.
      * apply (pr1 ff ;; pr1 gg).
      * simpl.
        etrans. apply assoc'.
        etrans. apply maponpaths, (pr2 gg).
        etrans. apply assoc.
        etrans. apply maponpaths_2, (pr2 ff).
        apply assoc'.
  Defined.

  Definition typecat_disp_data
             {C : precategory} (TC : typecat_obj_ext_structure C)
    : disp_cat_data C
    := (typecat_disp_ob_mor TC,, typecat_disp_id_comp TC).

  (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L78-L107  *)
  Definition typecat_disp_axioms
             {C : category} (TC : typecat_obj_ext_structure C)
    : disp_cat_axioms _ (typecat_disp_data TC).
  Proof.
    repeat apply tpair; intros; try apply homset_property.
    - (* id_left_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply id_left.
      apply pathsinv0.
      etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* id_right_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply id_right.
      apply pathsinv0.
      etrans. refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* assoc_disp *) 
      apply subtypePath.
      { intro. apply homset_property. }
      etrans. apply assoc.
      apply pathsinv0.
      etrans. unfold mor_disp.
      refine (pr1_transportf (C⟦_,_⟧) _ _ _ _ _ _ ).
      use transportf_const.
    - (* homsets_disp *)
      apply (isofhleveltotal2 2).
      + apply homset_property.
      + intro. apply isasetaprop. apply homset_property.
  Defined.

  Definition typecat_disp
             {C : category} (TC : typecat_obj_ext_structure C)
    : disp_cat C
    := (typecat_disp_data TC,, typecat_disp_axioms TC).

  Section TypeCat_Disp_is_univalent.

    Context {C : category}.
    Context (TC : typecat_obj_ext_structure C).

    Definition typecat_is_triangle_to_idtoiso_fiber_disp
               {Γ : C} (A B : TC Γ)
      : typecat_iso_triangle _ A B → @iso_disp C (typecat_disp TC) _ _ (identity_iso Γ) A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ Γ ◂ A, Γ ◂ B ⟧ ).
      set (iB_A     := pr2 tr : i ;; π B = π A).

      set (tr' := typecat_iso_triangle_swap TC tr).
      set (inv_i    := pr1 (pr1 tr') : C ⟦ Γ ◂ B, Γ ◂ A ⟧).
      set (inv_iA_B := pr2 tr' : inv_i ;; π A = π B).

      set (i_inv_i  := iso_inv_after_iso (pr1 tr) : i ;; inv_i = identity _).
      set (inv_i_i  := iso_after_iso_inv (pr1 tr) : inv_i ;; i = identity _).

      repeat use tpair.
      - exact i.
      - etrans. apply iB_A. apply pathsinv0, id_right.
      - exact inv_i.
      - simpl. etrans. apply inv_iA_B. apply pathsinv0, id_right.
      - use total2_paths_f.
        2: apply homset_property.
        etrans. apply inv_i_i.
        apply pathsinv0.
        etrans. apply (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ B, Γ ◂ B ⟧), _)).
        apply (maponpaths (λ f, f _) (transportb_const _ _)).
      - use total2_paths_f.
        2: apply homset_property.
        etrans. apply i_inv_i.
        apply pathsinv0.
        etrans. apply (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ A, Γ ◂ A ⟧), _)).
        apply (maponpaths (λ f, f _) (transportb_const _ _)).
    Defined.

    Definition idtoiso_fiber_disp_to_typecat_is_triangle
               {Γ : C} (A B : TC Γ)
      : @iso_disp C (typecat_disp TC) _ _ (identity_iso Γ) A B → typecat_iso_triangle _ A B.
    Proof.
      intros tr.
      set (i        := pr1 (pr1 tr) : C ⟦ Γ ◂ A, Γ ◂ B ⟧ ).
      set (iB_A     := pr2 (pr1 tr) : i ;; π B = π A ;; identity _).
      set (inv_i    := pr1 (pr1 (pr2 tr)) : C ⟦ Γ ◂ B, Γ ◂ A ⟧).
      set (inv_iA_B := pr2 (pr1 (pr2 tr))
                       : inv_i ;; π A = π B ;; identity _).
      set (inv_i_i  := maponpaths pr1 (pr1 (pr2 (pr2 tr))) : _).
      set (i_inv_i  := maponpaths pr1 (dirprod_pr2 (pr2 (pr2 tr))) : _).

      repeat use tpair.
      - exact i.
      - apply is_iso_from_is_z_iso.
        repeat use tpair.
        + apply inv_i.
        + etrans. apply i_inv_i.
          etrans.
          use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ A, Γ ◂ A ⟧), _)).
          simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
        + etrans. apply inv_i_i.
          etrans.
          use (pr1_transportb (λ _ (_ : C ⟦ Γ ◂ B, Γ ◂ B ⟧), _)).
          simpl. apply (maponpaths (λ f, f _) (transportb_const _ _)).
      - etrans. apply iB_A. apply id_right.
    Defined.

    Definition typecat_is_triangle_idtoiso_fiber_disp_isweq
               {Γ : C} (A B : TC Γ)
      : isweq (typecat_is_triangle_to_idtoiso_fiber_disp A B).
    Proof.
      use isweq_iso.
      - apply idtoiso_fiber_disp_to_typecat_is_triangle.
      - intros tr.
        use total2_paths_f.
        + apply eq_iso, idpath.
        + apply homset_property.
      - intros tr.
        apply eq_iso_disp.
        use total2_paths_f.
        + apply idpath.
        + apply homset_property.
    Defined.

    Definition typecat_is_triangle_idtoiso_fiber_disp_weq
               {Γ : C} (A B : TC Γ)
      : typecat_iso_triangle _ A B ≃ @iso_disp C (typecat_disp TC) _ _ (identity_iso Γ) A B
    := (_,, typecat_is_triangle_idtoiso_fiber_disp_isweq A B).

    Definition typecat_disp_is_disp_univalent
               (w' : ∏ (Γ : C) (A B : TC Γ), isweq (typecat_idtoiso_triangle _ A B))
      : is_univalent_disp (typecat_disp TC).
    Proof.
      apply is_univalent_disp_from_fibers.
      intros Γ A B.
      set (f := typecat_is_triangle_idtoiso_fiber_disp_weq A B).
      set (g := (typecat_idtoiso_triangle _ A B,, w' _ A B)).
      use weqhomot.
      - apply (weqcomp g f).
      - intros p. induction p.
        use total2_paths_f.
        + use total2_paths_f.
          * apply idpath.
          * apply homset_property.
        + apply proofirrelevance.
          apply isaprop_is_iso_disp.
    Defined.

  End TypeCat_Disp_is_univalent.

  Section TypeCat_Disp_Cleaving.

    Context {C : category}.
    Context (TC : typecat_structure C).

    (* NOTE: copied with slight modifications from https://github.com/UniMath/TypeTheory/blob/ad54ca1dad822e9c71acf35c27d0a39983269462/TypeTheory/Displayed_Cats/DisplayedCatFromCwDM.v#L114-L143 *)
    Definition pullback_is_cartesian
               {Γ Γ' : C} {f : Γ' --> Γ}
               {A  : typecat_disp TC Γ} {A' : typecat_disp TC Γ'} (ff : A' -->[f] A)
      : (isPullback _ _ _ _ (pr2 ff)) -> is_cartesian ff.
    Proof.
      intros Hpb Δ g B hh.
      eapply iscontrweqf.
      2: { 
        use Hpb.
        + exact (Δ ◂ B).
        + exact (pr1 hh).
        + simpl in B. refine (dpr_typecat B ;; g).
        + etrans. apply (pr2 hh). apply assoc.
      }
      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      - intro. apply isapropdirprod; apply homset_property.
      - intro. apply (isofhleveltotal2 1). 
        + apply homset_property.
        + intros. apply homsets_disp.
      - intros gg; split; intros H.
        + exists (pr2 H).
          apply subtypePath.
          intro; apply homset_property.
          exact (pr1 H).
        + split.
          * exact (maponpaths pr1 (pr2 H)).
          * exact (pr1 H).
    Defined.

    Lemma cleaving_typecat_disp : cleaving (typecat_disp TC).
    Proof.
      intros Γ Γ' f A.
      unfold cartesian_lift.
      exists (reind_typecat A f).
      use tpair.
      + use tpair.
        * use q_typecat.
        * apply dpr_q_typecat.
      + apply pullback_is_cartesian.
        apply (isPullback_swap (reind_pb_typecat A f)).
    Defined.
  End TypeCat_Disp_Cleaving.

End TypeCat_Disp.

Section TypeCat_Disp_Functor.

  Context {C : category}.

  Definition typecat_disp_functor_data
             (TC : typecat_obj_ext_structure C)
    : disp_functor_data
        (functor_identity C)
        (typecat_disp TC) (disp_codomain C).
  Proof.
    use tpair.
    - intros Γ A. exists (Γ ◂ A). apply dpr_typecat_obj_ext.
    - intros Γ' Γ A' A f ff. apply ff.
  Defined.

  Definition typecat_disp_functor_axioms
             (TC : typecat_obj_ext_structure C)
    : disp_functor_axioms (typecat_disp_functor_data TC).
  Proof.
    use make_dirprod.
    - intros Γ A. cbn.
      apply maponpaths.
      apply homset_property.
    - intros Γ Δ Γ' A B A' f g ff gg.
      apply maponpaths.
      use total2_paths_f.
      + apply idpath.
      + apply homset_property.
  Defined.

  Definition typecat_disp_functor
             (TC : typecat_obj_ext_structure C)
    : disp_functor (functor_identity C) (typecat_disp TC) (disp_codomain C)
    := (typecat_disp_functor_data TC ,, typecat_disp_functor_axioms TC).

  Definition typecat_disp_functor_ff
             (TC : typecat_obj_ext_structure C)
    : disp_functor_ff (typecat_disp_functor TC).
  Proof.
    unfold disp_functor_ff.
    intros Γ Γ' A A' f.
    use isweq_iso.
    - apply idfun.
    - intros ff.
      use total2_paths_f.
      + apply idpath.
      + apply homset_property.
    - intros ff.
      use total2_paths_f.
      + apply idpath.
      + apply homset_property.
  Defined.

  Section TypeCat_Disp_Functor_is_cartesian.

    Definition typecat_disp_functor_is_cartesian
               (TC : typecat_structure C)
    : is_cartesian_disp_functor (typecat_disp_functor TC).
    Proof.
      use cartesian_functor_from_cleaving.
      { apply (cleaving_typecat_disp TC). }
      intros Γ Γ' f A.
      intros Δ g k hh.
      use iscontrweqf.
      3: {
        use (reind_pb_typecat A f (pr1 k)).
        - apply (pr2 k ;; g).
        - apply (pr1 hh).
        - etrans. apply assoc'. apply (! pr2 hh).
      }

      eapply weqcomp.
      2: apply weqtotal2asstol.
      apply weq_subtypes_iff.
      - intro. apply isapropdirprod; apply homset_property.
      - intro. apply (isofhleveltotal2 1). 
        + apply homset_property.
        + intros. apply homsets_disp.
      - intros gg; split; intros H.
        + exists (pr1 H).
          apply subtypePath.
          intro; apply homset_property.
          exact (pr2 H).
        + split.
          * exact (pr1 H).
          * exact (maponpaths pr1 (pr2 H)).
    Defined.

  End TypeCat_Disp_Functor_is_cartesian.

End TypeCat_Disp_Functor.

(* TODO: move upstream *)
Definition comprehension_cat := ∑ (C : category), (comprehension_cat_structure C).

Coercion category_of_comprehension_cat (C : comprehension_cat) := pr1 C.
Coercion structure_of_comprehension_cat (C : comprehension_cat) := pr2 C.

Section ComprehensionCat_TypeCat.
  Context {C : category}.
  Context (CC : comprehension_cat_structure C).

  Let D := pr1 CC : disp_cat C.
  Let cleaving_D   := pr1 (pr2 CC) : cleaving D.
  Let comprehension_functor
    := pr1 (pr2 (pr2 CC))
       : disp_functor _ D (disp_codomain C).
  Let comprehension_functor_is_cartesian
    := pr2 (pr2 (pr2 CC))
       : is_cartesian_disp_functor comprehension_functor.

  Definition ty_from_comprehension_cat : C → UU
    := ob_disp D.

  Definition ext_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
    : C
    := pr1 (comprehension_functor Γ A).

  Definition reind_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : ty_from_comprehension_cat Γ'
    := pr1 (cleaving_D Γ Γ' f A).

  Definition typecat1_from_comprehension_cat
    : typecat_structure1 C.
  Proof.
    repeat use tpair.
    - exact ty_from_comprehension_cat.
    - exact ext_from_comprehension_cat.
    - exact reind_from_comprehension_cat.
  Defined.

  Definition dpr_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
    : ext_from_comprehension_cat Γ A --> Γ
    := pr2 (comprehension_functor Γ A).
  
  Definition typecat_obj_ext_structure_from_comprehension_cat
    : typecat_obj_ext_structure C
    := (typecat1_from_comprehension_cat ,, dpr_from_comprehension_cat).

  Definition q_square_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : comprehension_functor Γ' (reind_from_comprehension_cat _ A _ f)
                            -->[ f ] comprehension_functor Γ A
    := disp_functor_on_morphisms comprehension_functor
                                 (pr1 (pr2 (cleaving_D Γ Γ' f A))).

  Definition q_square_from_comprehension_cat_is_cartesian
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : is_cartesian (q_square_from_comprehension_cat _ A _ f).
  Proof.
    apply comprehension_functor_is_cartesian.
    apply cartesian_lift_is_cartesian.
  Defined.
  
  Definition q_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : ext_from_comprehension_cat
        Γ' (reind_from_comprehension_cat Γ A Γ' f)
        --> ext_from_comprehension_cat Γ A
    := pr1 (q_square_from_comprehension_cat _ A _ f).

  Definition dpr_q_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : q_from_comprehension_cat _ A _ f ;; dpr_from_comprehension_cat _ A
      = dpr_from_comprehension_cat _ (reind_from_comprehension_cat _ A _ f) ;; f
    := pr2 (q_square_from_comprehension_cat _ A _ f).

  Definition pullback_from_comprehension_cat
             (Γ : C) (A : ty_from_comprehension_cat Γ)
             (Γ' : C) (f : Γ' --> Γ)
    : isPullback _ _ _ _ (!dpr_q_from_comprehension_cat _ A _ f).
  Proof.
    intros Δ g k H.
    eapply iscontrweqf.
    2: {
      use (q_square_from_comprehension_cat_is_cartesian _ A _ f).
      - exact Γ'.
      - exact (identity _).
      - apply (Δ,, g).
      - use tpair.
        + apply k.
        + etrans. apply pathsinv0, H.
          apply pathsinv0, maponpaths, id_left.
    }
    apply invweq.
    eapply weqcomp.
    2: apply weqtotal2asstol.
    apply weq_subtypes_iff.
    - intro. apply isapropdirprod; apply homset_property.
    - intro. apply (isofhleveltotal2 1). 
      + apply homset_property.
      + intros. apply homsets_disp.
    - intros gg; split; intros H'.
      + use tpair.
        * etrans. apply (pr1 H').
          apply pathsinv0, id_right.
        * apply subtypePath.
          intro; apply homset_property.
          exact (pr2 H').
      + split.
        * etrans. apply (pr1 H'). apply id_right.
        * etrans. apply (maponpaths pr1 (pr2 H')). apply idpath.
  Defined.

  Definition typecat_structure_from_comprehension_cat
    : typecat_structure C.
  Proof.
    exists typecat1_from_comprehension_cat.
    repeat use tpair.
    - exact dpr_from_comprehension_cat.
    - exact q_from_comprehension_cat.
    - exact dpr_q_from_comprehension_cat.
    - exact pullback_from_comprehension_cat.
  Defined.
                 
End ComprehensionCat_TypeCat.

Section TypeCat_ComprehensionCat.

  Definition typecat_to_comprehension_cat_structure
             {C : category}
  : typecat_structure C → comprehension_cat_structure C.
  Proof.
    intros TC.
    exists (typecat_disp TC).
    exists (cleaving_typecat_disp _).
    exists (typecat_disp_functor _).
    apply typecat_disp_functor_is_cartesian.
  Defined.

  Definition typecat_to_comprehension_cat
    : typecat → comprehension_cat.
  Proof.
    intros TC.
    exists (pr1 TC).
    apply (typecat_to_comprehension_cat_structure (pr2 TC)).
  Defined.

  Definition typecat_from_comprehension_cat
    : comprehension_cat → typecat.
  Proof.
    intros CC.
    exists (pr1 CC).
    apply (typecat_structure_from_comprehension_cat (pr2 CC)).
  Defined.
    
  Definition fully_faithful_comprehension_cat_structure
             {C : category} (CC : comprehension_cat_structure C)
    := disp_functor_ff (pr1 (pr2 (pr2 CC))).

  Print disp_cat_ob_mor.

  Print cleaving.
  Check cartesian_lift.

  Definition typecat_obj_ext_structure_disp_ff_functor_to_codomain_weq
             (C : category)
    : typecat_obj_ext_structure C ≃ disp_ff_functor_to (disp_codomain C).
  Proof.
    (* TODO *)
  Abort.

  Definition ff_comprehension_cat_structure (C : category) : UU
    := ∑ (F : disp_ff_functor_to (disp_codomain C)),
       cleaving (source_disp_cat_of_disp_ff_functor F)
       × is_cartesian_disp_functor F. 

  Definition typecat_ff_comprehension_cat_structure_weq (C : category)
    : typecat_structure C ≃ ff_comprehension_cat_structure C.
  Proof.
    (* TODO *)
  Abort.

  Definition ff_comprehension_cat : UU
    := ∑ (C : category), ff_comprehension_cat_structure C.

  Definition typecat_ff_comprehension_cat_weq (C : category)
    : typecat ≃ ff_comprehension_cat.
  Proof.
    (* TODO *)
  Abort.

End TypeCat_ComprehensionCat.

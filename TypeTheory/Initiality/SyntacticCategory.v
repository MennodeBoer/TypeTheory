(** This file defines the syntactic category of our toy type theory, and the logical structure on it.

As a matter of organisation: all concrete lemmas involving derivations should live upstream in [TypingLemmas]; this file should simply package them up into the appropriate categorical structure. *)

Require Import UniMath.All.

Require Import TypeTheory.ALV1.TypeCat.
Require Import TypeTheory.Initiality.SplitTypeCat_Maps.
Require Import TypeTheory.Initiality.SplitTypeCat_Structure.
Require Import TypeTheory.Initiality.Syntax.
Require Import TypeTheory.Initiality.SyntaxLemmas.
Require Import TypeTheory.Initiality.Typing.
Require Import TypeTheory.Initiality.TypingLemmas.

Local Open Scope judgement.

Section Auxiliary.
 (* we’ll need some material here about quotients:
  particularly, [lemmas.setquotprpathsandR] from [PAdics], I guess? *)

  (* Upstream issues to possibly raise about [setquot]:
  - should [pr1] of [eqrel] coerce to [hrel], not directly to [Funclass]?
  - should [QuotientSet.setquotfun2] replace [setquotfun2]? *)

  (** Variant of [setquotuniv] with the [isaset] hypothesis separated out,
  for easier interactive use with [use], analogous to [setquotunivprop']. *)
  Definition setquotuniv' {X : UU} {R : hrel X} {Y : UU}
      (isaset_Y : isaset Y) (f : X -> Y) (f_respects_R : iscomprelfun R f)
    : setquot R -> Y.
  Proof.
    use (setquotuniv _ (_,,_)); assumption.
  Defined.

  (** TODO: is [setquot_rect], the general dependent universal property of [setquot], really not provided in the library somewhere?

  Here we put it together from [setquotuniv] (the non-dependent version) and [setquotunivprop] (the version for hprop-valued predicates). Unfortunately, that means it doesn’t compute, since [setquotunivprop] doesn’t.  With a bit more thought, could we give a version that computes nicely like [setquotuniv]? *)
  Definition setquot_rect_aux {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : ∑ (f : forall xx, P xx), forall x, f (setquotpr R x) = d x.
  Proof.
    transparent assert (f_nondep : (setquot R -> ∑ xx, P xx)).
    { use setquotuniv'.
      - apply isaset_total2; try assumption. apply isasetsetquot.
      - intros x. exact (_,, d x).
      - intros x y r. refine (total2_paths_f _ _). apply (d_respects_R _ _ r).
    }
    transparent assert (f_commutes : (forall xx, pr1 (f_nondep xx) = xx)).
    { use setquotunivprop'.
      - intros; apply isasetsetquot.
      - intros x. apply idpath.
    }
    exists (fun xx => transportf _ (f_commutes xx) (pr2 (f_nondep xx))).
    intros x. eapply pathscomp0. 2: { apply idpath_transportf. }
    apply maponpaths_2. apply isasetsetquot.
  Qed.

  Definition setquot_rect {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall xx, P xx
  := pr1 (setquot_rect_aux P isaset_P d d_respects_R).

  Definition setquot_comp {X:UU} {R:eqrel X}
      (P : setquot R -> UU) (isaset_P : forall xx, isaset (P xx))
      (d : forall x:X, P (setquotpr R x))
      (d_respects_R : forall (x y:X) (r : R x y),
          transportf _ (iscompsetquotpr _ _ _ r) (d x) = d y)
    : forall x, (setquot_rect P isaset_P d d_respects_R) (setquotpr R x) = d x
  := pr2 (setquot_rect_aux P isaset_P d d_respects_R).

End Auxiliary.

(** The construction of the syntactic type-category is rather trickier than one might hope, because of the need to quotient by some form of context equality — which, as ever when quotienting objects of a category, is quite fiddly.

For just the _category_ this is unnecessary, but for the _type-category_, it is unavoidable: types must be modulo equality, in order to form a presheaf, but then so must contexts, in order for context extension to be well-defined. *)

Section Context_Equality.
(* Probably this (or some of it) should be upstreamed to with the other “auxiliary judgements” in [TypingLemmas]. *)

  Definition wellformed_context_of_length (n : nat) : UU
  := ∑ (Γ : context_of_length n), [! |- Γ !].

  Coercion context_of_wellformed_context {n} (Γ : wellformed_context_of_length n)
    : context_of_length n
  := pr1 Γ.

  Definition derivation_wellformed_context
             {n} (Γ : wellformed_context_of_length n)
    : [! |- Γ !]
  := pr2 Γ.

  (** We only compare contexts of the same length for equality.

  Two contexts are equal if they _both_ believe all their types are
  equal.

  Note 1: one direction wouldn’t suffice, for general type theories.
  E.g.  in ETT with the reflection rule, define a predicate [P] over
  [nat] with [ P 0 ] false, and [ P 1 ] true.  Then [ P 0 ] proves
  that [ 0 === 1 : nat ] and hence that [ P 0 === P 1 ], but [ P 1 ]
  doesn’t prove this, so for the contexts [ x0 : P 0 ] and [ x0 : P 1
  ], one direction of the below conditions will hold, but not both.

  Note 2: this is a _flat_ form of context equality, not stratified,
  analogous to [ [! |f- Γ !] ] not [ [! |f- Γ !] ].  As such, we don’t
  expect it to give a contextual category: a context may (up to
  equality) be built up from types in several different ways.  For
  initiality, we will at some point have to remedy this: either by
  taking the contextual core of what this gives, or some other way. *)
  Definition derivation_cxteq {n} (Γ Δ : context_of_length n) : UU
  :=   (forall i, [! Γ |- Γ i === Δ i !])
     × (forall i, [! Δ |- Δ i === Γ i !])
     × (forall i, [! Γ |- Δ i !])     (* This should probably not be necessary? *)
     × (forall i, [! Δ |- Γ i !])     (* This should probably not be necessary? *)
  .
  
  Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                    (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.

  (** While the definition of this relation works for arbitrary raw contexts,
  the proof that it is an equivalence relation requires restriction to well-
  formed contexts. *)
  Definition derivable_cxteq_hrel {n} : hrel (wellformed_context_of_length n)
  := fun Γ Δ => ∥ derivation_cxteq Γ Δ ∥.

  Lemma derivation_cxteq_refl (n : ℕ) (Γ : wellformed_context_of_length n) :
    [! |- Γ === Γ !].
  Proof.
    repeat split; intros i; try apply derive_tyeq_refl; 
    apply (flat_from_context_judgement (pr2 Γ)).
  Qed.

  Lemma derivation_cxteq_sym (n : ℕ) (Γ Δ : wellformed_context_of_length n) :
    [! |- Γ === Δ !] → [! |- Δ === Γ !].
  Proof.
    now intros [H1 [H2 [H3 H4]]].
  Qed.

  Lemma foo (n : ℕ) (Γ Δ : wellformed_context_of_length n) (A : ty_expr n) :
    [! |- Γ === Δ !] → [! Γ |- A !] → [! Δ |- A !].
  Proof.
    intros [H1 [H2 [H3 H4]]] ΓA.
    rewrite <- (@subst_idmap_ty _ A).
    apply (@subst_derivation (ty_judgement Γ A) ΓA Δ (pr2 Δ)).
    cbn.
    intros i.
    unfold idmap_raw_context.
    rewrite subst_idmap_ty.
    apply (@derive_tm_conv Δ (Δ i) (Γ i)); auto.
    - apply (flat_from_context_judgement (pr2 Δ)).
    (* - apply (bar _ _ _ _ (H2 i)). *)
    - apply derive_var.
      + apply (pr2 Δ).
      + apply flat_from_context_judgement, (pr2 Δ).
  Qed.

  Lemma foo2 (n : ℕ) (Γ Δ : wellformed_context_of_length n) (A B : ty_expr n) :
    [! |- Γ === Δ !] → [! Γ |- A === B !] → [! Δ |- A === B !].
  Admitted.
  
  (* This is a mess... should be cleaned once the above has been cleaned *)
  Lemma  derivation_cxteq_trans (n : ℕ) (Γ Δ Θ : wellformed_context_of_length n) :
    [! |- Γ === Δ !] → [! |- Δ === Θ !] → [! |- Γ === Θ !].
  Proof.
    intros H1 H2.
    assert (H3 := derivation_cxteq_sym n Γ Δ H1).
    assert (H4 := derivation_cxteq_sym n Δ Θ H2).
    destruct H1 as [H1 [H1' [H1'' H1''']]].
    destruct H2 as [H2 [H2' [H2'' H2''']]].
    destruct H3 as [H3 [H3' [H3'' H3''']]].
    destruct H4 as [H4 [H4' [H4'' H4''']]].
    repeat split; intro i.
    + eapply derive_tyeq_trans; trivial; simpl in *.
      * apply (flat_from_context_judgement (pr2 Γ)).
      * apply (foo _ _ _ (Θ i) (H3,,H3',,H3'',,H3''')), (H2'' i).
      * eapply (foo2 _ Δ); trivial. apply (H3,,H3',,H3'',,H3''').
    + eapply derive_tyeq_trans; trivial; simpl in *.
      * apply (flat_from_context_judgement (pr2 Θ)).
      * eapply (foo _ Δ); trivial; apply (H2,,H2',,H2'',,H2''').
      * eapply (foo2 _ Δ); trivial; apply (H2,,H2',,H2'',,H2''').
    + eapply (foo _ Δ); trivial; apply (H3,,H3',,H3'',,H3''').
    + eapply (foo _ Δ); trivial; apply (H2,,H2',,H2'',,H2''').
  Qed.
  
  Lemma derivable_cxteq_is_eqrel n : iseqrel (@derivable_cxteq_hrel n).
  Proof.
    repeat split.
    - intros Γ Δ Θ; apply hinhfun2, derivation_cxteq_trans.
    - intros Γ; apply hinhpr, derivation_cxteq_refl.
    - intros Γ Δ; apply hinhfun, derivation_cxteq_sym.
  Qed.

  Definition derivable_cxteq {n} : eqrel (wellformed_context_of_length n)
  := (_,,derivable_cxteq_is_eqrel n).

  (* TODO: maybe weaken assumption [e_Γ] (only one direction should be needed). *)
  Lemma derivation_idmap_gen
      {n} {Γ Γ' : context_of_length n}
      (d_Γ : [! |- Γ !]) (d_Γ' : [! |- Γ' !])
      (e_Γ : [! |- Γ === Γ' !])
    : [! |- idmap_raw_context Γ ::: Γ ---> Γ' !].
  Proof.
  Admitted.

End Context_Equality.

Notation "[! |- Δ === Γ !]" := (derivation_cxteq Δ Γ)
                    (format "[!  |-  Δ  ===  Γ  !]") : judgement_scope.

Section Contexts_Modulo_Equality.

  Definition context_of_length_mod_eq n := setquot (@derivable_cxteq n).

  Definition context_mod_eq
  := ∑ (n:nat), context_of_length_mod_eq n.

  Local Definition length : context_mod_eq -> nat := pr1.

  Definition context_class {n} (Γ : wellformed_context_of_length n)
    : context_mod_eq
  := (n,, setquotpr _ Γ).
  Coercion context_class : wellformed_context_of_length >-> context_mod_eq.

  Definition context_representative (ΓΓ : context_mod_eq) : UU
  := ∑ (Γ : wellformed_context_of_length (length ΓΓ)), setquotpr _ Γ = (pr2 ΓΓ).
  Coercion context_representative : context_mod_eq >-> UU.

  Definition context_representative_as_context
      {ΓΓ} (Γ : context_representative ΓΓ)
    : wellformed_context_of_length (length ΓΓ)
  := pr1 Γ.
  Coercion context_representative_as_context
    : context_representative >-> wellformed_context_of_length.

  Lemma cxteq_context_representatives {ΓΓ : context_mod_eq} (Γ Γ' : ΓΓ)
    : ∥ derivation_cxteq Γ Γ' ∥.
  Proof.
    refine (lemmas.setquotprpathsandR (derivable_cxteq) Γ Γ' _).
    exact (pr2 Γ @ ! pr2 Γ').
  Defined.

  Lemma take_context_representative
      (ΓΓ : context_mod_eq) {X:UU} (h_X : isaprop X)
      (f : context_representative ΓΓ -> X)
    : X.
  Proof.
    refine (factor_through_squash _ f _). { assumption. }
    destruct ΓΓ as [n ΓΓ]. generalize ΓΓ.
    apply setquotunivprop'.
    { intros; apply isapropishinh. }
    intros Γ; apply hinhpr. exists Γ; auto.
  Defined.

End Contexts_Modulo_Equality.

Section Context_Maps.

  (** Note: the truncation of the derivation part is mathematically redundant,
  since we will later quotient anyway.  However, it lets us get better
  computational behaviour on the map part, in compositions etc. *)
  Local Definition map (ΓΓ ΔΔ : context_mod_eq) : UU
    := ∑ (f : raw_context_map (length ΓΓ) (length ΔΔ)),
       forall (Γ : ΓΓ) (Δ : ΔΔ), ∥ [! |- f ::: Γ ---> Δ !] ∥.

  (* TODO: lemma that here (and in later similar definitions) it’s sufficient to show typing for _some_ representative, to get it for all representatives. *)

  Definition raw_of_context_map {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ) : raw_context_map _ _
  := pr1 f.
  Coercion raw_of_context_map : map >-> raw_context_map.

  Local Definition map_derivable {ΓΓ ΔΔ} (f : map ΓΓ ΔΔ)
    : forall (Γ : ΓΓ) (Δ : ΔΔ), ∥ [! |- f ::: Γ ---> Δ !] ∥
  := pr2 f.

  Local Definition mapeq_hrel {ΓΓ ΔΔ} (f g : map ΓΓ ΔΔ)
  := ∀ (Γ : ΓΓ) (Δ : ΔΔ), ∥ [! |- f === g ::: Γ ---> Δ !] ∥.

  Local Definition mapeq_is_eqrel (ΓΓ ΔΔ : context_mod_eq)
    : iseqrel (@mapeq_hrel ΓΓ ΔΔ).
  Admitted.

  Local Definition mapeq_eqrel ΓΓ ΔΔ : eqrel (map ΓΓ ΔΔ)
  := (_,,mapeq_is_eqrel ΓΓ ΔΔ).

  Local Definition map_mod_eq (ΓΓ ΔΔ : context_mod_eq) : UU
  := setquot (mapeq_eqrel ΓΓ ΔΔ).

  Local Definition map_representative {ΓΓ ΔΔ} (ff : map_mod_eq ΓΓ ΔΔ) : UU
  := ∑ (f : map ΓΓ ΔΔ), setquotpr _ f = ff.
  Coercion map_representative : map_mod_eq >-> UU.

  Local Definition map_representative_as_map
      {ΓΓ ΔΔ} {ff : map_mod_eq ΓΓ ΔΔ} (f : map_representative ff)
    : map ΓΓ ΔΔ
  := pr1 f.
  Coercion map_representative_as_map : map_representative >-> map.

  Local Definition compose
      {ΓΓ ΔΔ ΘΘ} (ff : map_mod_eq ΓΓ ΔΔ) (gg : map_mod_eq ΔΔ ΘΘ)
    : map_mod_eq ΓΓ ΘΘ.
  Proof.
    revert ff gg. use QuotientSet.setquotfun2; [ | split].
    - (* construction of the composite *)
      intros f g. exists (comp_raw_context f g); intros Γ Θ.
      (* TODO: perhaps try to condense and [abstract] the following. *)
      apply (take_context_representative ΔΔ). { apply isapropishinh. }
      intros Δ.
      apply (squash_to_prop (map_derivable f Γ Δ)). { apply isapropishinh. }
      intros d_f.
      apply (squash_to_prop (map_derivable g Δ Θ)). { apply isapropishinh. }
      intros d_g.
      apply hinhpr. refine (derivation_comp_raw_context _ d_f d_g);
        auto using derivation_wellformed_context.
    - (* respecting equality in [f] *)
      intros f f' g e_f Γ Θ. cbn.
      apply (take_context_representative ΔΔ). { apply isapropishinh. } intros Δ.
      specialize (e_f Γ Δ); revert e_f.
      apply factor_through_squash. { apply isapropishinh. } intros e_f.
      apply (squash_to_prop (map_derivable f Γ Δ)). { apply isapropishinh. }
      intros d_f.
      apply (squash_to_prop (map_derivable f' Γ Δ)). { apply isapropishinh. }
      intros d_f'.
      apply (squash_to_prop (map_derivable g Δ Θ)). { apply isapropishinh. }
      intros d_g.
      apply hinhpr; simple refine (comp_raw_context_cong_l _ _ _ e_f _);
        auto using derivation_wellformed_context.
    - (* respecting equality in [g] *)
      cbn; intros f g g' e_g Γ Θ.
      apply (take_context_representative ΔΔ). { apply isapropishinh. }
      intros Δ.
      specialize (e_g Δ Θ); revert e_g.
      apply factor_through_squash. { apply isapropishinh. } intros e_g.
      apply (squash_to_prop (map_derivable f Γ Δ)). { apply isapropishinh. }
      intros d_f.
      apply hinhpr; simple refine (comp_raw_context_cong_r _ _ e_g);
        auto using derivation_wellformed_context.
  Defined.

  Local Definition idmap ΓΓ : map_mod_eq ΓΓ ΓΓ.
  Proof.
    refine (setquotpr _ _).
    exists (idmap_raw_context _).
    intros Γ Γ'.
    apply (squash_to_prop (cxteq_context_representatives Γ Γ')).
    { apply isapropishinh. }
    intros e_Γ; apply hinhpr;
      eauto using derivation_idmap_gen, derivation_wellformed_context.
  Defined.

  (* TODO: “empty” and “extension” context maps. *)

End Context_Maps.

Section Category.

  (* TODO: lemmas on associativity etc.  Should be immediate from the
  similar lemmas on raw ones in [SyntaxLemmas]. *)

  Lemma idmap_left {ΓΓ ΔΔ : context_mod_eq} (f : map_mod_eq ΓΓ ΔΔ) :
    compose (idmap _) f = f.
  Admitted.

  Lemma idmap_right {ΓΓ ΔΔ : context_mod_eq} (f : map_mod_eq ΓΓ ΔΔ) :
    compose f (idmap _) = f.
  Admitted.

  Lemma compose_assoc {ΓΓ0 ΓΓ1 ΓΓ2 ΓΓ3 : context_mod_eq} (f : map_mod_eq ΓΓ0 ΓΓ1)
    (g : map_mod_eq ΓΓ1 ΓΓ2) (h : map_mod_eq ΓΓ2 ΓΓ3) :
    compose f (compose g h) = compose (compose f g) h.    
  Admitted.
  
  Definition syntactic_category : category.
  Proof.
    use mk_category.
    - use mk_precategory_one_assoc.
      + use ((context_mod_eq,,map_mod_eq),,_).
        exists idmap.
        intros Γ Δ Θ.
        apply compose.
      + repeat split; simpl.
        * intros ΓΓ ΔΔ f.
          exact (idmap_left f).
        * intros ΓΓ ΔΔ f.
          exact (idmap_right f).
        * intros ΓΓ0 ΓΓ1 ΓΓ2 ΓΓ3 f g h.
          apply (compose_assoc f g h).
    - admit.
  Admitted.

End Category.

Section Split_Typecat.

  Definition syntactic_typecat : split_typecat.
  Admitted.

End Split_Typecat.

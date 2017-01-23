(** Definitions of various kinds of _fibraitions_, using displayed categories. *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.category_hset.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.

Set Automatic Introduction.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.
(*
Local Open Scope hide_transport_scope.
*)
(** Fibratons, opfibrations, and isofibrations are all displayed categories with extra lifting conditions. 

Classically, these lifting conditions are usually taken by default as mere existence conditions; when they are given by operations, one speaks of a _cloven_ fibration, etc.

We make the cloven version the default, so [is_fibration] etc are the cloven notions, and call the mere-existence versions _un-cloven_. 

(This conventional is provisional and and might change in future.) *)

(** * Isofibrations *)

(** The easiest to define are _isofibrations_, since they do not depend on a definition of (co-)cartesian-ness (because all displayed isomorphisms are cartesian). *)

Section Isofibrations.

(** Given an iso φ : c' =~ c in C, and an object d in D c,
there’s some object d' in D c', and an iso φbar : d' =~ d over φ.
*)

Definition is_isofibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (i : iso c' c) (d : D c),
          Σ d' : D c', iso_disp i d' d.

Definition is_uncloven_isofibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (i : iso c' c) (d : D c),
          ∃ d' : D c', iso_disp i d' d.

(** As with fibrations, there is an evident dual version.  However, in the iso case, it is self-dual: having forward (i.e. cocartesian) liftings along isos is equivalent to having backward (cartesian) liftings. *)

Definition is_op_isofibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (i : iso c c') (d : D c),
          Σ d' : D c', iso_disp i d d'.

Lemma is_isofibration_iff_is_op_isofibration 
    {C : Precategory} (D : disp_precat C)
  : is_isofibration D <-> is_op_isofibration D.
Proof.
  (* TODO: give this! *)
Abort.

End Isofibrations.

(** * Fibrations *)
Section Fibrations.

Definition is_cartesian {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : UU
:= forall c'' (g : c'' --> c') (d'' : D c'') (hh : d'' -->[g;;f] d),
  ∃! (gg : d'' -->[g] d'), gg ;; ff = hh.

(** See also [cartesian_factorisation'] below, for when the map one wishes to factor is not judgementally over [g;;f], but over some equal map. *)
Definition cartesian_factorisation {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c') {d'' : D c''} (hh : d'' -->[g;;f] d)
  : d'' -->[g] d'
:= pr1 (pr1 (H _ g _ hh)).

Definition cartesian_factorisation_commutes
    {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c') {d'' : D c''} (hh : d'' -->[g;;f] d)
  : cartesian_factorisation H g hh ;; ff = hh
:= pr2 (pr1 (H _ g _ hh)).

(** This is essentially the third access function for [is_cartesian], but given in a more usable form than [pr2 (H …)] would be. *)
Definition cartesian_factorisation_unique
    {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} {g : c'' --> c'} {d'' : D c''} (gg gg' : d'' -->[g] d')
  : (gg ;; ff = gg' ;; ff) -> gg = gg'.
Proof.
  revert gg gg'.
  assert (goal' : forall gg : d'' -->[g] d',
                    gg = cartesian_factorisation H g (gg ;; ff)).
  {
    intros gg.
    exact (maponpaths pr1
      (pr2 (H _ g _ (gg ;; ff)) (gg,,idpath _))).
  }
  intros gg gg' Hggff.
  eapply pathscomp0. apply goal'.
  eapply pathscomp0. apply maponpaths, Hggff.
  apply pathsinv0, goal'.
Qed.

Definition cartesian_factorisation' {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c')
    {h : c'' --> c} {d'' : D c''} (hh : d'' -->[h] d)
    (e : (g ;; f = h)%mor)
  : d'' -->[g] d'.
Proof.
  simple refine (cartesian_factorisation H g _).
  exact (transportb _ e hh).
Defined.

Definition cartesian_factorisation_commutes'
    {C : Precategory} {D : disp_precat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_cartesian ff)
    {c''} (g : c'' --> c')
    {h : c'' --> c} {d'' : D c''} (hh : d'' -->[h] d)
    (e : (g ;; f = h)%mor)
  : (cartesian_factorisation' H g hh e) ;; ff
  = transportb _ e hh.
Proof.
  apply cartesian_factorisation_commutes.
Qed.

Definition cartesian_lift {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
  : UU
:= Σ (d' : D c') (ff : d' -->[f] d), is_cartesian ff.

Definition object_of_cartesian_lift  {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : D c'
:= pr1 fd.
Coercion object_of_cartesian_lift : cartesian_lift >-> ob_disp.

Definition mor_disp_of_cartesian_lift  {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : (fd : D c') -->[f] d
:= pr1 (pr2 fd).
Coercion mor_disp_of_cartesian_lift : cartesian_lift >-> mor_disp.

Definition cartesian_lift_is_cartesian {C : Precategory} {D : disp_precat C}
    {c} (d : D c) {c' : C} (f : c' --> c)
    (fd : cartesian_lift d f)
  : is_cartesian fd
:= pr2 (pr2 fd).
Coercion cartesian_lift_is_cartesian : cartesian_lift >-> is_cartesian.

(* TODO: should the arguments be re-ordered as in [cartesian_lift]? If so, reorder in [isofibration] etc as well, for consistency. *)
Definition is_fibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (f : c' --> c) (d : D c), cartesian_lift d f.

(* TODO: give access functions! *)

Definition is_uncloven_fibration {C : Precategory} (D : disp_precat C) : UU
:= 
  forall (c c' : C) (f : c' --> c) (d : D c), ∥ cartesian_lift d f ∥.

(** ** Connection with isofibrations *)

Lemma is_iso_from_is_cartesian {C : Precategory} {D : disp_precat C}
    {c c' : C} (i : iso c' c) {d : D c} {d'} (ff : d' -->[i] d)
  : is_cartesian ff -> is_iso_disp i ff.
Proof.
  intros Hff.
  simple refine (_,,_); try split.
  - simple refine
      (cartesian_factorisation' Hff (inv_from_iso i) (id_disp _) _).
    apply iso_after_iso_inv.
  - apply cartesian_factorisation_commutes'.
  - apply (cartesian_factorisation_unique Hff).
    etrans. apply assoc_disp_var.
    rewrite cartesian_factorisation_commutes'.
    etrans. eapply transportf_bind.
      etrans. apply mor_disp_transportf_prewhisker. 
      eapply transportf_bind, id_right_disp.
    apply pathsinv0.
    etrans. apply mor_disp_transportf_postwhisker.
    etrans. eapply transportf_bind, id_left_disp.
    apply maponpaths_2, homset_property.
Qed.

Lemma is_isofibration_from_is_fibration {C : Precategory} {D : disp_precat C}
  : is_fibration D -> is_isofibration D.
Proof.
  intros D_fib c c' f d.
  assert (fd := D_fib _ _ f d).
  exists (fd : D _).
  exists (fd : _ -->[_] _).
  apply is_iso_from_is_cartesian; exact fd.
Defined.

(** ** Uniqueness of cartesian lifts *)

(* TODO: show that when [D] is _univalent_, cartesian lifts are literally unique, and so any uncloven fibration (isofibration, etc) is in fact cloven. *)
Definition cartesian_lifts_iso {C : Precategory} {D : disp_precat C}
    {c} {d : D c} {c' : C} {f : c' --> c} (fd fd' : cartesian_lift d f)
  : iso_disp (identity_iso c') fd fd'.
Proof.
  simple refine (_,,(_,,_)).
  - exact (cartesian_factorisation' fd' (identity _) fd (id_left _)). 
  - exact (cartesian_factorisation' fd (identity _) fd' (id_left _)).
  - cbn; split.
    + apply (cartesian_factorisation_unique fd').
      etrans. apply assoc_disp_var.
      rewrite cartesian_factorisation_commutes'.
      etrans. eapply transportf_bind, mor_disp_transportf_prewhisker.
      rewrite cartesian_factorisation_commutes'.
      etrans. apply transport_f_f.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker. 
      rewrite id_left_disp.
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.      
    + apply (cartesian_factorisation_unique fd).
      etrans. apply assoc_disp_var.
      rewrite cartesian_factorisation_commutes'.
      etrans. eapply transportf_bind, mor_disp_transportf_prewhisker.
      rewrite cartesian_factorisation_commutes'.
      etrans. apply transport_f_f.
      apply pathsinv0.
      etrans. apply mor_disp_transportf_postwhisker. 
      rewrite id_left_disp.
      etrans. apply transport_f_f.
      apply maponpaths_2, homset_property.
Defined.

Definition cartesian_lifts_iso_commutes {C : Precategory} {D : disp_precat C}
    {c} {d : D c} {c' : C} {f : c' --> c} (fd fd' : cartesian_lift d f)
  : (cartesian_lifts_iso fd fd') ;; fd'
  = transportb _ (id_left _) (fd : _ -->[_] _).
Proof.
  cbn. apply cartesian_factorisation_commutes'.
Qed.

(** In a displayed _category_ (i.e. _univalent_), cartesian lifts are literally unique, if they exist; that is, the type of cartesian lifts is always a proposition. *) 
Definition isaprop_cartesian_lifts
    {C : Precategory} {D : disp_precat C} (D_cat : is_category_disp D)
    {c} (d : D c) {c' : C} (f : c' --> c)
  : isaprop (cartesian_lift d f).
Proof.
  apply invproofirrelevance; intros fd fd'.
  use total2_paths.
  { apply (isotoid_disp D_cat (idpath _)); cbn.
    apply cartesian_lifts_iso. }
  apply subtypeEquality.
  { intros ff. repeat (apply impred; intro).
    apply isapropiscontr. }
  etrans.
    refine (@functtransportf_2 (D c') _ _ (fun x => pr1) _ _ _ _). 
  cbn. etrans. apply transportf_precompose_disp.
  rewrite idtoiso_isotoid_disp.
  refine (pathscomp0 (maponpaths _ _) (transportfbinv _ _ _)). 
  apply (precomp_with_iso_disp_is_inj (cartesian_lifts_iso fd fd')).
  etrans. apply assoc_disp.
  etrans. eapply transportf_bind, cancel_postcomposition_disp.
    refine (inv_mor_after_iso_disp _).
  etrans. eapply transportf_bind, id_left_disp.
  apply pathsinv0.
  etrans. apply mor_disp_transportf_prewhisker.
  etrans. eapply transportf_bind, cartesian_lifts_iso_commutes.
  apply maponpaths_2, homset_property.  
Defined.

Definition univalent_fibration_is_cloven
    {C : Precategory} {D : disp_precat C} (D_cat : is_category_disp D)
  : is_uncloven_fibration D -> is_fibration D.
Proof.
  intros D_fib c c' f d.
  apply (squash_to_prop (D_fib c c' f d)).
  apply isaprop_cartesian_lifts; assumption.
  auto.
Defined.
 
End Fibrations.

(** a proof principle for use with discrete fibrations *)
(** TODO: upstream *)
Lemma eq_exists_unique (A : UU) (B : A → UU) (H : iscontr (Σ a : A, B a)) 
  : Π a, B a → a = pr1 (iscontrpr1 H).
Proof.
  intros a b.
  assert (g : ((a,,b) : total2 B) 
                = 
              ( (pr1 (iscontrpr1 H),, pr2 (iscontrpr1 H)) : total2 B)).
  { etrans. apply (pr2 H). apply tppr. }
  apply (maponpaths pr1 g).
Defined.

Section Discrete_Fibrations.

Definition is_discrete_fibration {C : Precategory} (D : disp_precat C) : UU
:= 
  (forall (c c' : C) (f : c' --> c) (d : D c),
          ∃! d' : D c', d' -->[f] d)
  ×
  (forall c, isaset (D c)).

Definition discrete_fibration C : UU
  := Σ D : disp_precat C, is_discrete_fibration D.

Coercion disp_precat_from_discrete_fibration C (D : discrete_fibration C)
  : disp_precat C := pr1 D.
Definition unique_lift {C} {D : discrete_fibration C} {c c'} 
           (f : c' --> c) (d : D c) 
  : ∃! d' : D c', d' -->[f] d 
  := pr1 (pr2 D) c c' f d.
Definition isaset_fiber_discrete_fibration {C} (D : discrete_fibration C)
           (c : C) : isaset (D c) := pr2 (pr2 D) c.

(** TODO: move upstream *)
Lemma pair_inj {A : UU} {B : A -> UU} (is : isaset A) {a : A}
   {b b' : B a} : (a,,b) = (a,,b') -> b = b'.
Proof.
  intro H.
  use (invmaponpathsincl _ _ _ _ H).
  apply isofhlevelffib. intro. apply is.
Defined.

Lemma disp_mor_unique_disc_fib C (D : discrete_fibration C) 
  : Π (c c' : C) (f : c --> c') (d : D c) (d' : D c')
      (ff ff' : d -->[f] d'), ff = ff'.
Proof.
  intros.
  assert (XR := unique_lift f d').
  assert (foo : ((d,,ff) : Σ d0, d0 -->[f] d') = (d,,ff')).
  { apply proofirrelevance. 
    apply isapropifcontr. apply XR.
  } 
  apply (pair_inj (isaset_fiber_discrete_fibration _ _ ) foo).
Defined.

Definition fibration_from_discrete_fibration C (D : discrete_fibration C)
  : is_fibration D.
Proof.
  intros c c' f d.
  mkpair.
  - exact (pr1 (iscontrpr1 (unique_lift f d))).
  - mkpair.
    + exact (pr2 (iscontrpr1 (unique_lift f d))).
    + intros c'' g db hh.
      set (ff := pr2 (iscontrpr1 (unique_lift f d))  ). cbn in ff.
      set (d' := pr1 (iscontrpr1 (unique_lift f d))) in *.
      set (ggff := pr2 (iscontrpr1 (unique_lift (g;;f) d))  ). cbn in ggff.
      set (d'' := pr1 (iscontrpr1 (unique_lift (g;;f) d))) in *.
      set (gg := pr2 (iscontrpr1 (unique_lift g d'))). cbn in gg.
      set (d3 := pr1 (iscontrpr1 (unique_lift g d'))) in *. 
      assert (XR : ((d'',, ggff) : Σ r, r -->[g;;f] d) = (db,,hh)).
      { apply proofirrelevance. apply isapropifcontr. apply (pr2 D). }
      assert (XR1 : ((d'',, ggff) : Σ r, r -->[g;;f] d) = (d3 ,,gg;;ff)).
      { apply proofirrelevance. apply isapropifcontr. apply (pr2 D). }      
      assert (XT := maponpaths pr1 XR). cbn in XT.
      assert (XT1 := maponpaths pr1 XR1). cbn in XT1.
      generalize XR.
      generalize XR1; clear XR1.
      destruct XT.
      generalize gg; clear gg.
      destruct XT1.
      intros gg XR1 XR0.
      apply iscontraprop1.
      * apply invproofirrelevance.
        intros. apply subtypeEquality.
        { intro. apply homsets_disp. }
        apply disp_mor_unique_disc_fib.
      * exists gg.
        cbn. 
        assert (XX := pair_inj (isaset_fiber_discrete_fibration _ _ ) XR1).
        assert (YY := pair_inj (isaset_fiber_discrete_fibration _ _ ) XR0).
        etrans. apply (!XX). apply YY.
Defined.



Section Equivalence_disc_fibs_presheaves.

(* GOAL: correspondence between discrete fibrations and presheaves.

Outline via categories:

- show that the fibers of a discrete fibration are (discrete categories on) sets, and that the disp morphism types are props;
- define the category of discrete fibrations over C, using [functor_over_id] for morphisms, and with [homset_property] coming from the previous point;
- construct equivalence of cats; probably easiest by explicit functors and natural isos (not by “ess split” plus “full and faithful”); 
- show [disc_fib_precat C] is univalent (possibly _using_ the above equivalence of cats, to get “isos of displayed cats are weq to isos btn associated presheaves”?);
- conclude equivalence of types.

More direct equivalence of types:

- ?

 *)


(** TODO: the whole section needs cleaning *)


Variable C : Precategory.

Definition precat_of_discrete_fibs_ob_mor : precategory_ob_mor.
Proof.
  exists (discrete_fibration C).
  intros a b. exact (functor_over (functor_identity _ ) a b).
Defined.

Definition precat_of_discrete_fibs_data : precategory_data.
Proof.
  exists precat_of_discrete_fibs_ob_mor.
  split.
  - intro.
    exact (@functor_over_identity _ _ ).
  - intros ? ? ? f g. exact (functor_over_composite f g ).
Defined.

Definition precat_axioms_of_discrete_fibs : is_precategory precat_of_discrete_fibs_data.
Proof.
  repeat split; intros.
  - apply subtypeEquality.
    { intro. apply isaprop_functor_over_axioms. } 
    use total2_paths.
    + apply idpath.
    + apply idpath.
  - apply subtypeEquality.
    { intro. apply isaprop_functor_over_axioms. } 
    use total2_paths.
    + apply idpath.
    + apply idpath.
  - apply subtypeEquality.
    { intro. apply isaprop_functor_over_axioms. } 
    use total2_paths.
    + apply idpath.
    + apply idpath.
Qed.

Definition precat_of_discrete_fibs : precategory 
  := (_ ,, precat_axioms_of_discrete_fibs).

Lemma has_homsets_precat_of_discrete_fibs : has_homsets precat_of_discrete_fibs.
Proof.
  intros f f'. 
  apply (isofhleveltotal2 2).
  - apply (isofhleveltotal2 2).
    + do 2 (apply impred; intro).
      apply isaset_fiber_discrete_fibration. 
    + intro. do 6 (apply impred; intro).
      apply homsets_disp.
  - intro. apply isasetaprop. apply isaprop_functor_over_axioms.
Qed.  

Definition Precat_of_discrete_fibs : Precategory 
  := ( precat_of_discrete_fibs ,, has_homsets_precat_of_discrete_fibs).

(** ** Functor from discrete fibrations to presheaves *)

(** *** Functor on objects *)

(* TODO: split into data and properties *)
Definition preshv_from_disc_fib_ob (D : discrete_fibration C) : preShv C.
Proof.
  mkpair.
  - mkpair.
    + intro c. exists (D c). apply  isaset_fiber_discrete_fibration.
    + intros c' c f x. cbn in *.
      exact (pr1 (iscontrpr1 (unique_lift f x))).
  - split.
    + intro c; cbn.
      apply funextsec; intro x. simpl.
      apply pathsinv0. apply eq_exists_unique.
      apply id_disp.
    + intros c c' c'' f g. cbn in *.
      apply funextsec; intro x.
      apply pathsinv0. 
      apply eq_exists_unique.
      eapply comp_disp.
      * apply (pr2 (iscontrpr1 (unique_lift g _))). 
      * apply (pr2 (iscontrpr1 (unique_lift f _ ))).
Defined.

(** *** Functor on morphisms *)

Definition foo : functor_data Precat_of_discrete_fibs (preShv C).
Proof.
  exists preshv_from_disc_fib_ob.
  intros D D' a.
  mkpair.
  - intro c. simpl.
    exact (pr1 a c).
  - intros x y f. cbn in *.
    apply funextsec. intro d.
    apply eq_exists_unique.
    apply #a.
    apply (pr2 (iscontrpr1 (unique_lift f _ ))).
Defined.

(** *** Functor properties *)

Definition bar : is_functor foo.    
Proof.
  split.
  - intro D. apply nat_trans_eq. { apply has_homsets_HSET. } 
    intro c . apply idpath.
  - intros D E F a b. apply nat_trans_eq. { apply has_homsets_HSET. } 
    intro c. apply idpath.
Qed.

Definition functor_Disc_Fibs_to_preShvs : functor _ _ 
  := ( _ ,, bar).

(** ** Functor from presheaves to discrete fibrations *)

(** *** Functor on objects *)

(* TODO: split into data and properties *)
Definition disp_precat_from_preshv (D : preShv C) : disp_precat C.
Proof.
  mkpair.
  + mkpair.
    * exists (fun c => pr1hSet (pr1 D c)).
      intros x y c d f. exact (functor_on_morphisms (pr1 D) f d = c).
    * (* we even opacify identity and composition, since they are propositional *)
      abstract ( 
          split;
        [
          intros; cbn in *; apply (toforallpaths _ _ _ (functor_id D x ) _ ) |]
        ;
          intros ? ? ? ? ? ? ? ? X X0; cbn in *; 
          etrans; [apply (toforallpaths _ _ _ (functor_comp D _ _ _  g f ) _ ) |];
          cbn; etrans; [ apply maponpaths; apply X0 |]; (* here maponpaths depends on cbn *)
          apply X
       ) 
         .
  +  abstract ( 
    cbn; repeat split; cbn; intros; try apply setproperty;
         apply isasetaprop; apply setproperty 
     ) 
        .
Defined.

Definition disc_fib_from_preshv (D : preShv C) : discrete_fibration C.
Proof.
  mkpair.
  - apply (disp_precat_from_preshv D).
  - cbn.
    split.
    + intros c c' f d. simpl.
      use unique_exists.
      * apply (functor_on_morphisms (pr1 D) f d).
      * apply idpath.
      * intro. apply setproperty. 
      * intros. apply pathsinv0. assumption.
    + intro. simpl. apply setproperty.
Defined.

(** *** Functor on morphisms *)

Definition foo' : functor_data (preShv C) Precat_of_discrete_fibs.
Proof.
  mkpair.
  - apply disc_fib_from_preshv. 
  - intros F G a.
    mkpair.
    + mkpair.
      * intros c. apply (pr1 a c). 
      *  abstract ( 
            intros x y X Y f H;
            assert (XR := nat_trans_ax a);
            apply pathsinv0; etrans; [|apply (toforallpaths _ _ _ (XR _ _ f))];
            cbn; apply maponpaths, (!H)
          ) 
          .
    +  abstract (      
          repeat split; intros; apply setproperty
         ) 
        .
Defined.
    
(** *** Functor properties *)

Definition bar' : is_functor foo'.    
Proof.
  split.
  - intro F. 
    apply subtypeEquality. { intro. apply isaprop_functor_over_axioms. }
    cbn. 
    apply subtypeEquality. { intro. do 6 (apply impred; intro). 
                             apply setproperty. }
    cbn. apply idpath.
  - intros F G H a b.
    apply subtypeEquality. { intro. apply isaprop_functor_over_axioms. }
    cbn. 
    apply subtypeEquality. { intro. do 6 (apply impred; intro). 
                             apply setproperty. }
    cbn. apply idpath.
Qed.


Definition functor_preShvs_to_Disc_Fibs : functor _ _ 
  := ( _ ,, bar').

Definition cr : nat_trans (functor_composite functor_preShvs_to_Disc_Fibs
                                             functor_Disc_Fibs_to_preShvs) 
                          (functor_identity _ ).
Proof.
  mkpair.
  - intro F.
    cbn. mkpair.
    + cbn. intro c; apply idfun.
    + intros c c' f. cbn in *. apply idpath.
  - intros F G a. cbn in *.
    apply nat_trans_eq. { apply has_homsets_HSET. }
    cbn. intro c. apply idpath.
Defined.

Definition rc : nat_trans (functor_composite functor_Disc_Fibs_to_preShvs
                                             functor_preShvs_to_Disc_Fibs) 
                          (functor_identity _ ).
Proof.
  mkpair.
  - intro D.
    cbn. 
    mkpair.
    + mkpair.
      * cbn. intro c; apply idfun.
      * intros c c' x y f H. cbn. 
        unfold idfun.
        set (XR := pr2 (iscontrpr1 (unique_lift f y))). cbn in XR.
        apply (transportf (fun t => t -->[f] y) H XR).
    + split; cbn; unfold idfun.
      * intros x y.
        apply  disp_mor_unique_disc_fib.
      * intros x y z xx yy zz f g ff gg.
        apply disp_mor_unique_disc_fib.
  - intros c c' f. cbn in *.
    apply subtypeEquality. { intro. apply isaprop_functor_over_axioms. }
    cbn.
    use total2_paths.
    + cbn. apply idpath.
    + cbn. 
      do 6 (apply funextsec; intro). 
      apply disp_mor_unique_disc_fib.     
Defined.

(** TODO:
    Both natural transformations are pointwise given by 
    the identity function. It is hence easy to show
    that they are isos, if a bit annoying to write down.
*)

End Equivalence_disc_fibs_presheaves.

End Discrete_Fibrations.

Section Opfibrations.

(* TODO: add definitions analogous to in [Fibrations].  For constructions/theorems: think about whether it’s possible to recover them by duality, instead of repeating all proofs?? *)

End Opfibrations.
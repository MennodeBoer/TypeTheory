
(**

 Ahrens, Lumsdaine, Voevodsky, 2015 - 2016

*)

Require Export Systems.Auxiliary.
Require Export Systems.UnicodeNotations.
Require Export UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.more_on_pullbacks.
Require Export UniMath.CategoryTheory.UnicodeNotations.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.yoneda.



Undelimit Scope transport.


Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

(*
Local Notation "< h , k >" := (PullbackArrow _ _ h k _ ) : pullback_scope.
Open Scope pullback_scope.
*)

Local Definition preShv C := [C^op , HSET , pr2 is_category_HSET].


Section fix_a_category.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "'Yo'" := (yoneda C hsC).
Local Notation "'Yo^-1'" :=  (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).

Local Definition yy {F : preShv C} {c : C} : ((F : functor _ _) c : hSet) ≃ _ ⟦ Yo c, F⟧.
Proof.
  apply invweq.
  apply yoneda_weq.
Defined.

Lemma yy_natural (F : preShv C) (c : C) (A : (F:functor _ _) c : hSet) 
                  c' (f : C⟦c', c⟧) :
        yy (# (F : functor _ _) f A) = # Yo f ;; yy A.
Proof.
  assert (XTT := is_natural_yoneda_iso_inv _ hsC F _ _ f).
  apply (toforallpaths _ _ _ XTT).
Qed.

(** * Type of type structures *)

Definition type_structure : UU :=
  Σ Ty : preShv C,
        ∀ (Γ : C) (A : (Ty : functor _ _ ) Γ : hSet ), Σ (ΓA : C), C⟦ΓA, Γ⟧.

Definition TY (X : type_structure) : preShv _ := pr1 X.

Definition comp_ext {X : type_structure} Γ A : C := pr1 (pr2 X Γ A).
Notation "Γ ◂ A" := (comp_ext Γ A) (at level 30).
Definition π {X : type_structure} {Γ} A : C ⟦Γ ◂ A, Γ⟧ := pr2 (pr2 X _ A).

Lemma idtoiso_π {X : type_structure} (Γ : C) (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A')
  :
    idtoiso (maponpaths (λ B, Γ ◂ B) e) ;; π _ = π _ .
Proof.
  induction e.
  apply id_left.
Qed.

(** * Type of families structures over a type structure *)

Section some_structures.

Context {X : type_structure}.

Definition families_data_structure : UU :=
  Σ Tm : preShv C, _ ⟦ Tm, TY X ⟧ × (∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), _ ⟦Yo (Γ ◂ A) , Tm⟧ ).

Definition TM (Y : families_data_structure) : preShv C := pr1 Y.
Definition pp Y : _ ⟦TM Y, TY X⟧ := pr1 (pr2 Y).
Definition Q Y {Γ} A : _ ⟦ _ , TM Y⟧ := pr2 (pr2 Y) Γ A.

Lemma idtoiso_Q Y Γ (A A' : (TY X : functor _ _ ) Γ : hSet) (e : A = A') : 
  #Yo (idtoiso (maponpaths (fun B => Γ ◂ B) e )) ;; Q Y _ = Q Y _ . 
Proof.
  induction e. 
  etrans. apply cancel_postcomposition. apply functor_id.
  apply id_left.
Defined.

Definition families_prop_structure (Y : families_data_structure) :=
  ∀ Γ (A : (TY X : functor _ _ ) Γ : hSet), 
        Σ (e : #Yo (π A) ;; yy A = Q Y A ;; pp Y), isPullback _ _ _ _ e.

Definition families_structure : UU :=
  Σ Y : families_data_structure, families_prop_structure Y.
Coercion families_data_from_families (Y : families_structure) : _ := pr1 Y.


(** * Type of split comprehension structures over a types structure *)

Notation "A [ f ]" := (# (TY X : functor _ _ ) f A) (at level 4).

Definition comprehension_structure : UU :=
  Σ q : ∀ {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
           C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧, 
    (∀ Γ Γ' (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet), 
        Σ e :  π _ ;; f = q f A ;; π _ , isPullback _ _ _ _ e).

Definition qq (Y : comprehension_structure) {Γ Γ'} (f : C ⟦Γ', Γ⟧)
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : C ⟦Γ' ◂ A [ f ], Γ ◂ A⟧
  := pr1 Y _ _ f A.

Definition idtoiso_qq (Y : comprehension_structure) {Γ Γ'} (f f' : C ⟦Γ', Γ⟧)
              (e : f = f')
              (A : (TY X:functor _ _ ) Γ : hSet) 
  : idtoiso (maponpaths (comp_ext Γ') (maponpaths (λ k : C⟦Γ', Γ⟧, #(TY X : functor _ _ ) k A) e))
                ;; qq Y f' A = qq Y f A.
Proof.
  induction e.
  apply id_left.
Qed.

Definition pullback_from_comp (Y : comprehension_structure) 
  {Γ Γ'} (f : C⟦Γ', Γ⟧) (A : (TY X:functor _ _ ) Γ : hSet) : 
        Σ e : π _ ;; f = qq Y f A ;; π _ , isPullback _ _ _ _ e
:= pr2 Y _ _ f A.

Definition is_split_comprehension_structure (Y : comprehension_structure) : UU
  := 
    (∀ Γ A, qq Y (identity Γ) A = idtoiso (maponpaths (fun B => Γ ◂ B) 
                                                      (toforallpaths _ _ _ (functor_id (TY X) _ ) _ )) )
 ×
   (∀ Γ Γ' Γ'' (f : C⟦Γ', Γ⟧) (g : C ⟦Γ'', Γ'⟧) (A : (TY X:functor _ _ ) Γ : hSet),
       qq Y (g ;; f) A = idtoiso (maponpaths (fun B => Γ'' ◂ B)
                                             (toforallpaths _ _ _ (functor_comp (TY X) _ _ _  f g) A))
                          ;; qq Y g (A [f]) 
                          ;; qq Y f A).

(* Since [Ty X] is always an hset, the splitness properties hold with any equality replacing the canonical ones. This is sometimes handy, one may want to opacify the canonical equalities in later proofs. *)
Lemma split_comprehension_structure_comp_general
  {Y : comprehension_structure} (Z : is_split_comprehension_structure Y)
  {Γ Γ' Γ'' : C}
  {f : C ⟦ Γ', Γ ⟧} {g : C ⟦ Γ'', Γ' ⟧} {A : ((TY X : functor _ _) Γ : hSet)}
  (p : # (TY X : functor C^op HSET) (g ;; f) A
       = # (TY X : functor C^op HSET) g (# (TY X : functor C^op HSET) f A)) 
: qq Y (g ;; f) A
  = idtoiso
         (maponpaths (λ B : ((pr1 X : functor _ _) Γ'' : hSet), Γ'' ◂ B)
            p) ;; 
       qq Y g (# (TY X : functor _ _) f A) ;; qq Y f A.
Proof.
  eapply pathscomp0. apply (pr2 Z).
  repeat apply (maponpaths (fun h => h ;; _)).
  repeat apply maponpaths. apply uip. exact (pr2 ((TY X : functor _ _) _)).
Qed.

Definition compatible_scomp_families (Y : families_structure)(Z : comprehension_structure) : UU
  := ∀ Γ Γ' A (f : C⟦Γ', Γ⟧) , Q Y A[f] = #(yoneda _ hsC) (qq Z f A) ;; Q Y A.

Definition compatible_fam_structure (Z : comprehension_structure) : UU
  := Σ Y : families_structure, compatible_scomp_families Y Z.

Definition compatible_comp_structure (Y : families_structure) : UU
  := Σ Z : comprehension_structure, compatible_scomp_families Y Z.







Section compatible_fam_structure_from_comp.

Variable Z : comprehension_structure.
Variable ZZ : is_split_comprehension_structure Z.

Definition tm_carrier (Γ : C) : UU :=
  Σ A : (TY X : functor _ _ ) Γ : hSet,
  Σ s : C⟦Γ, Γ ◂ A⟧, s ;; π _ = identity _ .

Lemma isaset_tm_carrier Γ : isaset (tm_carrier Γ).
Proof.
  apply (isofhleveltotal2 2).
  - apply setproperty.
  - intro. apply (isofhleveltotal2 2).
    + apply hsC.
    + intro. apply isasetaprop. apply hsC.
Qed.

Definition tm Γ : hSet := hSetpair _ (isaset_tm_carrier Γ).

Definition tm_on_mor Γ Γ' (f : C⟦Γ',Γ⟧) : tm_carrier Γ → tm_carrier Γ'.
Proof.
  intro Ase.
  exists ((pr1 Ase) [f]).
  eapply pb_of_section.
  - apply (pr2 (pullback_from_comp Z f _ )).
  - apply (pr2 (pr2 Ase)).
Defined.

Definition tm_functor_data : functor_data C^op HSET.
Proof.
  exists tm.
  refine tm_on_mor.
Defined.

Lemma tm_functor_eq {Γ} (t t' : (tm_functor_data Γ : hSet)) 
  (eA : pr1 t = pr1 t')
  (es : (pr1 (pr2 t)) ;; idtoiso (maponpaths (comp_ext Γ) eA) = (pr1 (pr2 t')))
  : t = t'.
Proof.
  destruct t as [A [s e]], t' as [A' [s' e']]; simpl in *.
  use total2_paths; simpl.
    apply eA.
  apply subtypeEquality. intro; apply hsC.
  simpl. eapply pathscomp0. refine (pr1_transportf _ _ _ _ _ eA _).
  simpl. eapply pathscomp0. apply functtransportf.
  eapply pathscomp0. eapply pathsinv0. apply idtoiso_postcompose.
  exact es.
Qed.

Lemma is_functor_tm : is_functor tm_functor_data.
Proof.
  split; [unfold functor_idax | unfold functor_compax].
  - intro Γ. apply funextsec.
    intro t. simpl.
    destruct t as [A [s e]]. cbn.
    use tm_functor_eq; simpl.
    + use (toforallpaths _ _ _ (functor_id (TY X) _ ) A).
    + simpl. rewrite <- (pr1 ZZ).
      match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
      etrans. apply (PullbackArrow_PullbackPr2 XR). apply id_left.
  - intros Γ Γ' Γ'' f g. cbn.
    apply funextsec.
    intro t.
    destruct t as [A [s e]]; simpl in *.
    unfold tm_on_mor. simpl.
    use tm_functor_eq; simpl.
    + abstract (apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _) A)).
    + { cbn.
      apply PullbackArrowUnique; cbn.
      - rewrite <- assoc.  
        rewrite idtoiso_π.
        apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
      - cbn.
        apply (MorphismsIntoPullbackEqual (pr2 (pr2 Z _ _ _ _ ))); simpl.
        + etrans. Focus 2. apply assoc.
          etrans. Focus 2.
            apply maponpaths, @pathsinv0.
            apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
          etrans. Focus 2. apply @pathsinv0, id_right.
          etrans. apply @pathsinv0, assoc.
          etrans. eapply maponpaths, pathsinv0.
            apply (pr1 (pullback_from_comp _ _ _)).
          etrans. apply assoc.
          etrans. Focus 2. apply id_left.
          refine (maponpaths (fun h => h ;; g) _).
          etrans. apply @pathsinv0, assoc.
          etrans. apply maponpaths, idtoiso_π.
          apply (PullbackArrow_PullbackPr1 (mk_Pullback _ _ _ _ _ _ _)).
        + repeat rewrite <- assoc.
          etrans. apply maponpaths. rewrite assoc.
            apply @pathsinv0, split_comprehension_structure_comp_general, ZZ.
          etrans. apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)).
          etrans. apply @pathsinv0, assoc.
          apply (maponpaths (fun h => g ;; h)).
          apply @pathsinv0. apply (PullbackArrow_PullbackPr2 (mk_Pullback _ _ _ _ _ _ _)). }
Qed.

Definition tm_functor : functor _ _  := tpair _ _ is_functor_tm.

Definition pp_carrier (Γ : C^op) : (tm_functor Γ : hSet) → (TY X : functor _ _ ) Γ : hSet.
Proof.
  exact pr1.
Defined.

Lemma is_nat_trans_pp_carrier : is_nat_trans tm_functor (TY X : functor _ _ ) pp_carrier.
Proof.
  intros Γ Γ' f.
  apply idpath.
Defined.

Definition pp_from_comp : preShv C ⟦tm_functor, TY X⟧ := tpair _ _ is_nat_trans_pp_carrier.

Section Q_from_comp.

Variable Γ : C.
Variable A : (TY X : functor _ _ ) Γ : hSet.

Definition Q_from_comp_data :
 ∀ x : C^op, HSET ⟦ (Yo (Γ ◂ A) : functor _ _ ) x, tm_functor x ⟧.
Proof.
  intros Γ' f. simpl in *.
  unfold yoneda_objects_ob in f.
  unfold tm_carrier. mkpair.
  + exact A[f;;π _ ].
  + apply (section_from_diagonal _ (pr2 (pullback_from_comp Z _ _ ))). 
    exists f. apply idpath.
Defined.

Lemma is_nat_trans_Q_from_comp : is_nat_trans _ _ Q_from_comp_data.
Proof.
intros Γ' Γ'' f. simpl.
    apply funextsec. intro g.
    unfold yoneda_objects_ob. cbn.    
    use tm_functor_eq; simpl pr1.
    + etrans. apply (maponpaths (fun k => #(TY X : functor _ _ ) k A) (assoc _ _ _ _ _ _ _ _ )).
      apply (toforallpaths _ _ _ (functor_comp (TY X) _ _ _ _ _ )).
    + apply PullbackArrowUnique.
      * cbn.
        etrans. apply (!assoc _ _ _ _ _ _ _ _ ).
        rewrite idtoiso_π.
        match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => set (XR := HH) end.
        apply (PullbackArrow_PullbackPr1 XR).
      * cbn.
        {
          use (MorphismsIntoPullbackEqual (pr2 (pr2 Z _ _ _ _ ))).
          - etrans. Focus 2. apply assoc.
            match goal with [|- _ = _ ;; (PullbackArrow ?HH _ _ _ _ ;; _ )] =>
                            set (XR := HH) end.
            rewrite (PullbackArrow_PullbackPr1 XR). clear XR.
            etrans. apply (!assoc _ _ _ _ _ _ _ _ ).
            rewrite <- (pr1 (pullback_from_comp Z f _ )).
            etrans. apply assoc.
            etrans. apply assoc4.
            rewrite idtoiso_π.
            match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ ;; _ = _ ] => set (XR := HH) end.
            rewrite (PullbackArrow_PullbackPr1 XR).
            rewrite id_right. apply id_left.
          - etrans. Focus 2. apply assoc.
            match goal with |[|- _ = _ ;; (PullbackArrow ?HH _ _ _ _ ;; _ )] => set (XR := HH) end.
            rewrite (PullbackArrow_PullbackPr2 XR).
            clear XR.
            assert (XT:= pr2 ZZ). simpl in XT.
            specialize (XT _ _ _ (g ;; π _ ) f ).
            specialize (XT A).
            rewrite maponpathscomp0 . 
            rewrite idtoiso_concat.
            simpl.
            match goal with |[ H : ?EE =  _ |- ?DD ;; (?II ;; ?KK) ;; _  ;; _  = _ ] => 
                     set (d := DD); set (i:= II) end.
            rewrite <- assoc.
            rewrite <- assoc.
            etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
            
            etrans. apply maponpaths. apply maponpaths. apply assoc.
            etrans. apply maponpaths. apply maponpaths. 
                        apply (!XT).
            unfold i. clear i. clear XT.
            rewrite idtoiso_qq.
            unfold d; clear d.
            match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _  = _ ] =>
                            set (XR := HH) end.
            apply (PullbackArrow_PullbackPr2 XR). 
        } 
Qed.

Definition Q_from_comp : _ ⟦ Yo (Γ ◂ A), tm_functor⟧ := tpair _ _ is_nat_trans_Q_from_comp.

Definition Q_from_comp_commutes : # Yo (π _ ) ;; yy A = Q_from_comp ;; pp_from_comp.            
Proof.
  apply nat_trans_eq. apply has_homsets_HSET.
  intro Γ'. apply idpath.
Defined.

Definition into_Pb  (Γ' : C)
  (S : HSET)
  (a : HSET ⟦ S, hSetpair (yoneda_objects_ob C Γ Γ') (hsC Γ' Γ) ⟧)
  (b : HSET ⟦ S, tm Γ' ⟧)
  (Hab : a ;; (λ f : C ⟦ Γ', Γ ⟧, # (TY X : functor _ _ ) f A) = b ;; pp_carrier Γ')
:
   HSET ⟦ S, hSetpair (yoneda_objects_ob C (Γ ◂ A) Γ') (hsC Γ' (Γ ◂ A)) ⟧. 
Proof.
(* define the morphism *)
      simpl in *. unfold yoneda_objects_ob in *.
      intro s.
      set (Ase := b s). unfold tm_carrier in Ase.
      set (HabH := ! toforallpaths _ _ _ (Hab) s); simpl in HabH. cbn in HabH.
      set (XX := (pr1 (pr2 Ase))).
      set (YY := maponpaths (fun x => Γ'◂ x) (HabH)). simpl in YY.
      set (iYY := idtoiso YY).
      apply (XX ;; iYY ;; qq Z _ _ ).
Defined.


Lemma isPullback_Q_from_comp_commutes : isPullback _ _ _ _ Q_from_comp_commutes.
Proof.
  apply pb_if_pointwise_pb.
  intro Γ'. simpl.
  unfold yoneda_morphisms_data. 
  apply mk_isPullback.
  intros S a b Hab.
  mkpair.
  - mkpair. 
    + apply (into_Pb _ _ a b Hab).
    + (* show that the defined morphism makes two triangles commute *)
      simpl. split.
      * (* <a,b>(s) . π = a(s)   *)
        apply funextsec. intro s.
        etrans. apply assoc4.
        set (Habs := toforallpaths _ _ _ Hab s). simpl in Habs. cbn in Habs.
        cbn in a. unfold yoneda_objects_ob in a. simpl. 
        rewrite <- assoc.
        rewrite <- assoc.
        assert (XR:= pullback_from_comp Z (a s) A).
        etrans. apply maponpaths. apply maponpaths.
        apply (! (pr1 XR)).
        etrans. apply maponpaths. apply assoc.
        rewrite idtoiso_π.
        rewrite assoc.
        assert (XT:= (pr2 (pr2 (b s)))). simpl in XT.
        unfold pp_carrier.
        simpl. cbn.
        
        etrans. apply (cancel_postcomposition C). apply XT.
        apply id_left.
      * (* <a,b> . Q(A) = b *)
        apply funextsec. intro s.
        {
          use tm_functor_eq.
          - simpl.
            set (XX:= toforallpaths _ _ _ Hab s). cbn in XX.
            etrans. Focus 2. apply XX.
            apply (maponpaths (fun k => # (TY X : functor _ _ ) k A)).
            unfold into_Pb.
            abstract (
            assert (XR:= pullback_from_comp Z (a s) A);
            rewrite <- assoc;
            rewrite <- assoc;
            etrans ; [apply maponpaths; apply maponpaths; apply (! (pr1 XR))|];
            etrans ; [apply maponpaths; apply assoc | idtac];
            rewrite idtoiso_π; rewrite assoc;
            assert (XT:= (pr2 (pr2 (b s)))); simpl in XT;
            unfold pp_carrier;
            simpl; cbn;
            etrans; [apply (cancel_postcomposition C); apply XT | idtac];
            apply id_left ).
          - simpl.
            match goal with |[ |- PullbackArrow ?HH _ _ _ ?ee ;; _ = _ ] => 
                             set (XR:=HH); generalize ee end. 
            intro p.
            assert (XT := PullbackArrow_PullbackPr2 XR). cbn in XT.
            match goal with |[ |- _ ;; ?II = _ ] => 
                             set (i:= II) end. 
            apply iso_inv_to_right.
            apply pathsinv0.
            apply PullbackArrowUnique.
            + etrans. apply maponpaths. cbn. apply idpath.
              clear XT XR. clear i. clear p.
              etrans. apply cancel_postcomposition. apply maponpaths.
              eapply pathsinv0. 
              apply (maponpaths pr1 (idtoiso_inv _ _ _ _ )).
              Search ( _ = ! (maponpaths _ _ )).
              rewrite <- maponpathsinv0.
              rewrite <- assoc.
              etrans. apply maponpaths. apply idtoiso_π.
              apply (pr2 (pr2 (b s))).
            + simpl. cbn.
              etrans. apply cancel_postcomposition. apply maponpaths. eapply pathsinv0. 
              apply (maponpaths pr1 (idtoiso_inv _ _ _ _ )).
              rewrite <- assoc.
              rewrite <- maponpathsinv0.
              Search ( ! ( _ @ _ ) = _ ).
              rewrite pathscomp_inv.
              rewrite maponpathscomp0.
              rewrite idtoiso_concat. simpl.
              repeat rewrite <- assoc.
              etrans. apply maponpaths. apply maponpaths. apply cancel_postcomposition.
                      apply maponpaths. apply maponpaths. apply maponpaths.
                      eapply pathsinv0. 
                      apply (maponpathsinv0  (λ k : C ⟦ Γ', Γ ⟧, # (TY X : functor _ _ ) k A)).
              etrans. apply maponpaths. apply maponpaths. apply idtoiso_qq.
              unfold into_Pb.
              rewrite <- assoc. 
              apply idpath.
        }     
Admitted.

End Q_from_comp.

Definition comp_fam_structure_from_comp : compatible_fam_structure Z.
Proof.
  mkpair.
  - mkpair.
    + mkpair.
      * apply tm_functor.
      * {
          split.
          - apply pp_from_comp.
          - intros. apply Q_from_comp.
        } 
    + unfold families_prop_structure.
      intros.
      exists (Q_from_comp_commutes _ _ ).
      apply isPullback_Q_from_comp_commutes.
  - unfold compatible_scomp_families. 
    intros Γ Γ' A f.
    apply nat_trans_eq. 
    { apply has_homsets_HSET. }
    intro Γ''.
    apply funextsec. intro g. unfold yoneda_objects_ob in g.
    use tm_functor_eq. 
    + unfold yoneda_morphisms_data.
      etrans. Focus 2. eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply (assoc C _ _ _ _ _ _ _ ).
      etrans. Focus 2. eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply maponpaths.
                       apply (pr1 (pullback_from_comp Z _ _ )).
      etrans. Focus 2.  eapply (maponpaths (fun k => #(TY X : functor _ _ ) k A)).
                       apply (!assoc C _ _ _ _ _ _ _ ).
      apply (toforallpaths _ _ _ (!functor_comp (TY X) _ _ _ _ _ ) A).
    + simpl.
      apply PullbackArrowUnique.
      * simpl. cbn.
        etrans. apply (!assoc C _ _ _ _ _ _ _ ).
        etrans. apply maponpaths. apply idtoiso_π.
        match goal with [|- PullbackArrow ?HH _ _ _ _ ;; _  = _ ] =>
                            set (XR := HH) end.
        apply (PullbackArrow_PullbackPr1 XR). 
      * simpl. cbn.
        etrans. apply (!assoc C _ _ _ _ _ _ _ ).
        unfold yoneda_morphisms_data.
        rewrite maponpathscomp0.
        rewrite maponpathscomp0.
        rewrite maponpathscomp0.
        rewrite idtoiso_concat.
        rewrite idtoiso_concat.
        rewrite idtoiso_concat.
        simpl.
        etrans. apply maponpaths. apply assoc4.
        etrans. apply maponpaths. apply cancel_postcomposition. apply assoc. 
        etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
        etrans. apply maponpaths. apply maponpaths. apply idtoiso_qq.
        etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).  
        etrans. apply maponpaths. apply maponpaths.
                apply idtoiso_qq.
        etrans. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
        etrans. apply maponpaths. apply maponpaths.
                apply idtoiso_qq.
        etrans. apply maponpaths. apply maponpaths. apply (pr2 ZZ).
        
        etrans. apply maponpaths. apply maponpaths. apply (!assoc _ _ _ _ _ _ _ _ ).
        etrans. apply maponpaths. apply assoc.
        
        match goal with [|- _ ;; (?I ;; _ ) = _ ] => set (i := I) end.
        assert (XR : i = identity _ ).
        {
          unfold i; clear i.
          apply pathsinv0. 
          etrans. Focus 2. apply (maponpaths pr1 (idtoiso_concat _ _ _ _ _ _ )).
          apply idtoiso_eq_idpath.
          rewrite <- maponpathscomp0.
          apply maponpaths_eq_idpath.
          apply setproperty. (* setproperty should not be needed *)
        }
        rewrite XR. rewrite id_left.
        rewrite assoc.
        match goal with |[ |- PullbackArrow ?HH _ _ _ _  ;; _ ;; _  = _ ] => set (XT:=HH) end.
        
        etrans. apply cancel_postcomposition. apply (PullbackArrow_PullbackPr2 XT).
        apply idpath.
Qed.
    
End compatible_fam_structure_from_comp.


Section canonical_TM.

Variable Z : comprehension_structure.
Variable ZZ : is_split_comprehension_structure Z.
Variable Y : compatible_fam_structure Z.

Definition foo : preShv C  ⟦tm_functor Z ZZ, TM (pr1 Y)⟧.
Proof.
  mkpair.
  - intro Γ. simpl.
    intro Ase. 
    set (XX := # Yo (pr1 (pr2 Ase)) ;; Q (pr1 Y) _ ).
    exact (yoneda_weq _ _ _ _ XX).
  - intros Γ Γ' f.
    apply funextsec. intro t. simpl. cbn.
    unfold yoneda_morphisms_data. simpl.
    rewrite id_left. rewrite id_left.
    destruct t as [A [s e]]. simpl in *.
    assert (XR:= pr2 Y). simpl in XR. unfold compatible_scomp_families in XR.
    specialize (XR _ _ A f).
    assert (XR2 := nat_trans_eq_pointwise XR).
    admit.
Admitted.

Definition bar : preShv C  ⟦TM (pr1 Y), tm_functor Z ZZ⟧.
Proof.
  mkpair.
  - intro Γ. simpl.
    intro s'. set (S' := yy s').
    set (ps := (pp (pr1 Y) : nat_trans _ _ )  _ s').
    assert (XR : S' ;; pp (pr1 Y) = yy ( (pp (pr1 Y) : nat_trans _ _ ) _ s')).
    { 
      apply nat_trans_eq; [ apply has_homsets_HSET | ];
      intro Γ' ;
      apply funextsec;
      intro g; simpl; cbn;
      assert (XR := nat_trans_ax (pp (pr1 Y)) _ _ g);
      apply (toforallpaths _ _ _ XR)
            .
    } 
    exists ps.
    set (Pb := pr2 (pr1 Y) Γ ps). 
    set (T:= section_from_diagonal (pr1 Pb) (pr2 Pb) (S',,XR) ).
    mkpair.
    + apply Yo^-1.
      exact (pr1 T).
    + (
      apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ )));
      etrans ; [ apply functor_comp |];
      etrans ; [ apply cancel_postcomposition ;
         apply(homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC Γ (Γ◂ps) ))) | ];
      simpl;
      match goal with |[ |- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] => 
                       set (XR3:=HH) end;
      rewrite (PullbackArrow_PullbackPr1 XR3);
      apply pathsinv0; apply (functor_id Yo)
       ).
  - intros Γ Γ' f.
    simpl in *.
    apply funextsec; intro; simpl; cbn.
    use (@tm_functor_eq Z).
    + simpl.
      set (XT:= (nat_trans_ax (pp (pr1 Y))) _ _ f ).
      set (XT2 := toforallpaths _ _ _ XT).
      apply XT2.
    + simpl.
      apply PullbackArrowUnique.
      * etrans. apply maponpaths. cbn. apply idpath.
        etrans. apply (!assoc _ _ _ _ _ _  _ _ ).
        rewrite idtoiso_π.
        apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
        etrans ; [ apply functor_comp |].
        match goal with |[ |- _  (_ ?EE) ;; _ = _ ] => set (e := EE) end.

        assert (XR := homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ )) e).
        etrans. apply cancel_postcomposition. apply XR. 
        clear XR ; unfold e; clear e.
        match goal with |[|- PullbackArrow ?HH _ _ _ _ ;; _ = _ ] 
                           => set (XR := HH) end.
        etrans. apply (PullbackArrow_PullbackPr1 XR).
        apply pathsinv0. apply (functor_id Yo).
      * etrans. apply maponpaths. cbn. apply idpath.
        apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
        etrans. apply functor_comp.
        etrans. apply cancel_postcomposition. apply functor_comp.
        match goal with |[ |- _  (_ ?EE) ;; _ ;; _ = _ ] => set (e := EE) end.
        assert (XR := homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ )) e).
        etrans. apply cancel_postcomposition. apply cancel_postcomposition. apply XR. 
        clear XR.
        etrans. Focus 2. eapply pathsinv0. apply functor_comp.
        match goal with |[ |- _ = _ ;; _  (_ ?EE)] => set (e' := EE) end.
        assert (XR := homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ )) e').
        etrans. Focus 2. apply maponpaths. eapply pathsinv0. apply XR.
        
        use (MorphismsIntoPullbackEqual).
        admit.        
Admitted.

Lemma foo_bar : foo ;; bar = identity _ .
Proof.
  apply nat_trans_eq. { apply has_homsets_HSET. }
  intro Γ. apply funextsec; intro Ase.
  destruct Ase as [A [s e]].
  use tm_functor_eq.
  - admit.
  - admit.
Admitted.
    
End canonical_TM.



Section compatible_comp_structure_from_fam.

Variable Y : families_structure.

Section qq_from_fam.

Variables Γ Γ' : C.
Variable f : C⟦Γ', Γ⟧.
Variable A : (TY X : functor _ _) Γ : hSet.

Let Xk := mk_Pullback _ _ _ _ _ (pr1 (pr2 Y Γ A)) (pr2 (pr2 Y Γ A)).

Definition Yo_of_qq : _ ⟦Yo (Γ' ◂ A[f]), Yo (Γ ◂ A) ⟧.
Proof.
  simple refine (PullbackArrow Xk _ _ _ _ ).
  - apply (#Yo (π _) ;; #Yo f ). 
  - apply (Q Y).
  - abstract (
        clear Xk;
        assert (XT:= pr1 (pr2 Y Γ' A[f]));
        eapply pathscomp0; try apply XT; clear XT;
        rewrite <- assoc; apply maponpaths;
        apply pathsinv0, yy_natural
    ).
Defined.

Lemma Yo_of_qq_commutes_1 : # Yo (π _ ) ;; # Yo f = Yo_of_qq ;; # Yo (π _ ) .
Proof.
  apply pathsinv0.
  apply (PullbackArrow_PullbackPr1 Xk).
Qed.

Lemma Yo_of_qq_commutes_2 : Yo_of_qq ;; Q _ A = Q Y _ .
Proof.
  apply (PullbackArrow_PullbackPr2 Xk).
Qed.  

Lemma isPullback_Yo_of_qq : isPullback _ _ _ _ Yo_of_qq_commutes_1.
Proof.
  simple refine (isPullback_two_pullback _ _ _ _ _ _ _ _ _ _ ).
  - apply functor_category_has_homsets.
  - apply (TY X).
  - apply (TM Y).
  - apply (yy A).
  - apply pp.
  - apply Q.
  - apply (pr1 (pr2 Y _ _ )).
  - apply (pr2 (pr2 Y _ _ )).
  - match goal with [|- isPullback _ _ _ _ ?HH ] => generalize HH end.
    rewrite <- yy_natural.
    rewrite Yo_of_qq_commutes_2.
    intro.
    apply (pr2 (pr2 Y _ _ )).
Defined.

Definition qq_fam :  _ ⟦Γ' ◂ A[f] , Γ ◂ A⟧.
Proof.
  apply (invweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
  apply Yo_of_qq.
Defined.

Lemma Yo_qq_fam_Yo_of_qq : # Yo qq_fam = Yo_of_qq.
Proof.
  unfold qq_fam.
  assert (XT := homotweqinvweq
     (weqpair _ (yoneda_fully_faithful _  hsC (Γ'◂ A[f]) (Γ ◂ A)  ))).
  apply XT.
Qed.

Lemma qq_commutes_1 : π _ ;; f = qq_fam ;; π _ .
Proof.
  assert (XT:= Yo_of_qq_commutes_1).
  rewrite <- Yo_qq_fam_Yo_of_qq in XT.
  do 2 rewrite <- functor_comp in XT.
  apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
  apply XT.
Qed.

Definition isPullback_qq : isPullback _ _ _ _ qq_commutes_1.
Proof.
  use (isPullback_preimage_square _ _ _ Yo).
  - apply hsC.
  - apply yoneda_fully_faithful.
  - assert (XT:= isPullback_Yo_of_qq).
    match goal with |[|- isPullback _ _ _ _ ?HHH] => generalize HHH end.
    rewrite Yo_qq_fam_Yo_of_qq.
    intro. assumption.
Qed.

End qq_from_fam.

Definition comp_from_fam : comprehension_structure.
Proof.
  mkpair.
  - intros. apply qq_fam.
  - intros. simpl.
    exists (qq_commutes_1 _ _ _ _ ).
    apply isPullback_qq.
Defined.

Lemma comp_from_fam_compatible_scomp_families : compatible_scomp_families Y comp_from_fam.
Proof.
  intros Γ Γ' A f.
  assert (XR:= Yo_of_qq_commutes_2).
  apply pathsinv0.
  rewrite Yo_qq_fam_Yo_of_qq.
  apply XR.
Qed.

Lemma is_split_comp_from_fam : is_split_comprehension_structure comp_from_fam.
Proof.
  split.
  - intros Γ A. simpl.
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    etrans; [ apply (homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))) | idtac ].    
    apply pathsinv0.
    unfold Yo_of_qq.
    apply PullbackArrowUnique. 
    + etrans. apply maponpaths. cbn. apply idpath. 
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. apply (functor_comp Yo).
      apply maponpaths. rewrite idtoiso_π.
      apply pathsinv0. apply id_right.
    + etrans. apply maponpaths. cbn. apply idpath.
      apply idtoiso_Q.
  - intros.
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    etrans; [ apply (homotweqinvweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))) | idtac ].    
    sym. apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. apply (functor_comp Yo).
      apply maponpaths.
      rewrite <- assoc. rewrite <- qq_commutes_1 .
      repeat rewrite assoc.
      rewrite assoc4.
      etrans. apply cancel_postcomposition. apply maponpaths. eapply pathsinv0. apply qq_commutes_1 .
      apply cancel_postcomposition.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply idtoiso_π.
    + etrans. apply maponpaths. cbn. apply idpath.
      etrans. apply cancel_postcomposition. apply functor_comp.
      rewrite <- assoc.
      rewrite Yo_qq_fam_Yo_of_qq.
      rewrite  Yo_of_qq_commutes_2 .
      etrans. apply cancel_postcomposition. apply functor_comp.
      rewrite <- assoc.
      etrans. apply maponpaths. apply cancel_postcomposition. apply Yo_qq_fam_Yo_of_qq.
      etrans. apply maponpaths. apply Yo_of_qq_commutes_2 .
      apply idtoiso_Q.
Qed.

      
End compatible_comp_structure_from_fam.




(* needs splitness? *)
Lemma iscontr_compatible_fam_structure (Z : comprehension_structure) (ZZ : is_split_comprehension_structure Z)
: iscontr (compatible_fam_structure Z).
Proof.
  exists (comp_fam_structure_from_comp Z ZZ).
  intro t.
  apply subtypeEquality.
  { intro. do 4 (apply impred; intro).
      apply functor_category_has_homsets. 
  }
  destruct t as [t Hcomp]. simpl.
  apply subtypeEquality.
  { intro. unfold families_prop_structure.
    do 2 (apply impred; intro).
    apply isofhleveltotal2. 
    - apply functor_category_has_homsets.
    - intro.  apply isaprop_isPullback.
  } 
  destruct t as [t tprop]. simpl.
  use total2_paths.
  - admit.
  - admit.
Admitted.



(* we are more interested in split such things, but that 
   is easily added; 
   splitness of the construed comprehension structure
   is proved above
*)
Lemma iscontr_compatible_comp_structure (Y : families_structure)
: iscontr (compatible_comp_structure Y).
Proof.
  mkpair.
  - mkpair.
    + apply (comp_from_fam Y).
    + apply comp_from_fam_compatible_scomp_families.
  - intro t.
    apply subtypeEquality.
    { 
      intro. do 4 (apply impred; intro).
      apply functor_category_has_homsets. 
    }
    simpl.
    apply subtypeEquality.
    { 
      intro. do 4 (apply impred; intro).
      apply isofhleveltotal2. 
      - apply hsC.
      - intro. apply isaprop_isPullback.
    } 
    simpl.
    destruct t as [t H]. simpl.
    destruct t as [q h]; simpl.
    apply funextsec. intro Γ.
    apply funextsec; intro Γ'.
    apply funextsec; intro f.
    apply funextsec; intro A.
    
    apply (invmaponpathsweq (weqpair _ (yoneda_fully_faithful _ hsC _ _ ))).
    apply pathsinv0.
    etrans. apply Yo_qq_fam_Yo_of_qq.
    unfold Yo_of_qq.
    apply pathsinv0.
    apply PullbackArrowUnique.
    + etrans. apply maponpaths. cbn. apply idpath.
      rewrite <- functor_comp.
      etrans. eapply pathsinv0. apply (functor_comp Yo).
      apply maponpaths.
      apply pathsinv0. apply (pr1 (h _ _ _ _ )).
    + etrans. apply maponpaths. cbn. apply idpath.
      apply pathsinv0.
      apply H.
Qed.


End some_structures.


End fix_a_category.

Print Assumptions iscontr_compatible_comp_structure.
Print Assumptions iscontr_compatible_fam_structure.

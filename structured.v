Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.choice.
Require Import Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg MathComp.bigop.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.fperm.
Require Import CoqUtils.nominal CoqUtils.string.

Require Import basic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Structured.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Implicit Types (ls : locals) (h : heap).

Definition state := {bound locals * heap}.

Definition stateu : state -> state -> state :=
  mapb2 (fun s1 s2 => (unionm s1.1 s2.1, unionm s1.2 s2.2)).

Notation "s1 * s2" := (stateu s1 s2) : state_scope.

Local Open Scope state_scope.

Lemma stateuE A1 ls1 h1 A2 ls2 h2 :
  mutfresh A1 (ls1, h1) A2 (ls2, h2) ->
  mask A1 (ls1, h1) * mask A2 (ls2, h2) =
  mask (A1 :|: A2) (unionm ls1 ls2, unionm h1 h2).
Proof.
move=> mf; rewrite /stateu /=.
rewrite mapb2E //= => {ls1 h1 ls2 h2 mf} /= pm [[ls1 h1] [ls2 h2]] /=.
by rewrite !renamepE !renamem_union.
Qed.

Lemma rename_stateu pm (s1 s2 : state) :
  rename pm (s1 * s2) = rename pm s1 * rename pm s2.
Proof.
rewrite /stateu rename_mapb2 //=.
move=> {pm s1 s2} pm /= [[ls1 h1] [ls2 h2]] /=.
by rewrite !renamepE !renamem_union.
Qed.

Definition emp : state := mask fset0 (emptym, emptym).

Lemma names_emp : names emp = fset0.
Proof. by rewrite /emp namesbE // fsub0set. Qed.

Lemma stateu0s : left_id emp stateu.
Proof.
rewrite /stateu /=.
apply: bound_left_id=> /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls h] /=; rewrite !union0m.
Qed.

Lemma stateus0 : right_id emp stateu.
Proof.
rewrite /stateu; apply: bound_right_id=> /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls h] /=; rewrite !unionm0.
Qed.

Lemma stateuA : associative stateu.
Proof.
rewrite /stateu; apply: bound_associative => /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls1 h1] [ls2 h2] [ls3 h3] /=; rewrite !unionmA.
Qed.

Lemma new_stateul A (f : name -> state) s :
  finsupp A f ->
  new A f * s = new (A :|: names s) (fun a => f a * s).
Proof.
move=> fs_f; rewrite /stateu /= new_comp2l //=.
move=> /= {s} pm [[ls1 h1] [ls2 h2]] /=.
by rewrite renamepE /= !renamem_union.
Qed.

Lemma new_stateur s A (f : name -> state) :
  finsupp A f ->
  s * new A f = new (names s :|: A) (fun a => s * f a).
Proof.
move=> fs_f; rewrite /stateu /= new_comp2r //=.
move=> /= {s} pm [[ls1 h1] [ls2 h2]] /=.
by rewrite renamepE /= !renamem_union.
Qed.

Definition vars_s (s : state) : {fset string} :=
  expose (mapb (fun s => domm s.1) s).

Lemma vars_sE A ls h : vars_s (mask A (ls, h)) = domm ls.
Proof.
rewrite /vars_s /= mapbE ?exposeE //.
by move=> pm /= {ls h} [ls h] /=; rewrite -renamem_dom.
Qed.

Lemma vars_s_stateu s1 s2 :
  vars_s (s1 * s2) = vars_s s1 :|: vars_s s2.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
by rewrite stateuE // !vars_sE domm_union.
Qed.

Lemma vars_emp : vars_s emp = fset0.
Proof. by rewrite /emp vars_sE domm0. Qed.

Lemma vars_s_hide n s : vars_s (hide n s) = vars_s s.
Proof.
by case: s / boundP=> [A [ls h] sub]; rewrite hideE !vars_sE.
Qed.

Definition pub (s : state) : {fset name} :=
  names (mapb (fun s => domm s.2) s).

Lemma pubE A ls h : pub (mask A (ls, h)) = A :&: names (domm h).
Proof.
rewrite /pub /= mapbE /= 1?maskE 1?namesbE ?fsubsetIr //.
by move=> pm {ls h} /= [ls h]; rewrite renamem_dom.
Qed.

Lemma pubU s1 s2 : pub (s1 * s2) = pub s1 :|: pub s2.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf ? ?].
rewrite stateuE // !pubE domm_union namesfsU fsetIUr.
have P: forall A x B y C, mutfresh A x B y ->
                          fsubset B (names y) ->
                          fsubset C (names x) ->
                          (A :|: B) :&: C = A :&: C.
  move=> T S A x B y C {mf} /and3P [_ _ mf] /fsubsetP subB /fsubsetP subC.
  rewrite fsetIUl fsetUC; apply/eqP/fsubsetP=> n /fsetIP [inB inC].
  rewrite in_fsetI inC andbT.
  move/fsubsetP/(_ n): mf; rewrite in_fsetI (subB _ inB) (subC _ inC).
  by move=> /(_ erefl)/fsetIP [].
rewrite (P _ _ _ _ _ _ _ mf) //; last first.
  by apply/fsubsetU/orP; right; apply/fsubsetUl.
rewrite mutfresh_sym in mf.
rewrite (fsetUC A1) (P _ _ _ _ _ _ _ mf) //.
by apply/fsubsetU/orP; right; apply/fsubsetUl.
Qed.

Lemma pub_names s : fsubset (pub s) (names s).
Proof.
case: s / boundP=> /= [A [ls h] sub].
by rewrite namesbE // pubE fsubsetIl.
Qed.

Lemma pub_emp : pub emp = fset0.
Proof. by rewrite /emp pubE domm0 fset0I. Qed.

Lemma pub_hide n s : pub (hide n s) = pub s :\ n.
Proof.
case: s / boundP=> [A [ls h] sub]; rewrite hideE !pubE.
by apply/eq_fset=> i; rewrite in_fsetD1 !in_fsetI in_fsetD1 andbA.
Qed.

Lemma stateuC s1 s2 :
  fdisjoint (vars_s s1) (vars_s s2) ->
  fdisjoint (pub s1) (pub s2) ->
  s1 * s2 = s2 * s1.
Proof.
case: s1 s2 / bound2P=> [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite !vars_sE !pubE stateuE // stateuE 1?mutfresh_sym // fsetUC.
move=> disv dish; rewrite unionmC // [_ h1 _]unionmC //.
apply: fdisjoint_names_domm.
apply/fdisjointP=> i in_h1; apply/negP=> in_h2.
suff /fsetIP [in1 in2] : i \in A1 :&: A2.
  move/fdisjointP/(_ i): dish; rewrite !in_fsetI in1 in_h1 /= => /(_ erefl).
  by rewrite in2 in_h2.
case/and3P: mf=> [_ _ /fsubsetP]; apply.
by rewrite in_fsetI !in_fsetU /= in_h1 in_h2 !orbT.
Qed.

Definition locval (x : string) (v : value) : state :=
  mask (names v) (setm emptym x v, emptym).

Notation "x ::= v" := (locval x v) (at level 20) : state_scope.

Local Open Scope state_scope.

Lemma vars_s_locval x v : vars_s (x ::= v) = fset1 x.
Proof.
by rewrite /locval vars_sE domm_set domm0 fsetU1E fsetU0.
Qed.

Lemma names_locval x v : names (x ::= v) = names v.
Proof.
rewrite /locval namesbE //; apply/fsubsetU/orP; left=> /=.
apply/fsubsetP=> n inN; apply/namesmP.
have get_x: setm emptym x v x = Some v by rewrite setmE eqxx.
eapply PMFreeNamesVal; eauto.
Qed.

Lemma rename_locval s x v :
  rename s (x ::= v) = x ::= rename s v.
Proof.
rewrite /locval renamebE names_rename renamefsE; congr mask.
by rewrite renamepE /= renamem_set renameT !renamem_empty.
Qed.

Definition blockat (i : name) (vs : seq value) : state :=
  locked (mask (i |: names vs)
               (emptym, mkpartmapf (fun p => nth VNil vs (absz p.2))
                                   [seq (i, Posz n) | n <- iota 0 (size vs)])).

Notation "i :-> vs" := (blockat i vs) (at level 20) : state_scope.

Lemma vars_s_blockat i vs : vars_s (i :-> vs) = fset0.
Proof. by rewrite /blockat -lock vars_sE domm0. Qed.

Lemma pub_blockat i vs :
  pub (i :-> vs) = if vs is [::] then fset0 else fset1 i.
Proof.
rewrite /blockat -lock /= pubE.
rewrite (_ : names (domm _) = if vs is [::] then fset0 else fset1 i).
  case: vs=> [|v vs] /=; first by rewrite fsetI0.
  apply/eqP; rewrite eqEfsubset fsubsetIr /= fsubsetI fsubsetxx andbT.
  by rewrite fsetU1E fsubsetUl.
case: vs=> [|v vs]; first by rewrite domm_mkpartmapf namesfsE /= big_nil.
rewrite domm_mkpartmapf; apply/eqP; rewrite eqEfsubset; apply/andP; split.
  apply/fsubsetP=> i' /namesfsP [p]; rewrite in_mkfset.
  by case: p=> [i'' n] /mapP [n' _ [<- _]].
rewrite /= namesfsE bigcup_fsetU1; apply/fsubsetU/orP; left.
by apply/fsubsetU/orP; left; rewrite fsubsetxx.
Qed.

Lemma names_blockat i vs :
  names (i :-> vs) =
  if nilp vs then fset0 else i |: names vs.
Proof.
rewrite /blockat -lock; case: ifPn=> [/nilP -> /=|vs0n].
  rewrite maskE fsetIUr /= !namesm_empty !fsetI0 fsetU0 namesbE //.
  exact: fsub0set.
rewrite namesbE //; apply/fsubsetU/orP; right=> /=.
apply/fsubsetP=> i' /fsetU1P [{i'}->|].
  rewrite namesmE; apply/fsetUP; left; apply/namesfsP.
  exists (i, Posz 0); last by rewrite in_fsetU in_fset1 eqxx.
  rewrite mem_domm mkpartmapE.
  by case: vs vs0n=> [|v vs] //= _; rewrite eqxx.
case/namessP=> v in_vs inN.
rewrite namesmE; apply/fsetUP; right; apply/namesfsP.
exists v=> //; apply/codommP.
exists (i, Posz (find (pred1 v) vs)).
rewrite mkpartmapfE mem_map; last by move=> n m /= [<-].
rewrite mem_iota leq0n /= add0n -has_find.
have in_vs' : has (pred1 v) vs by rewrite has_pred1.
by rewrite in_vs'; congr Some; apply/eqP/(nth_find VNil in_vs').
Qed.

Lemma rename_blockat s i vs :
  rename s (i :-> vs) = s i :-> rename s vs.
Proof.
rewrite /blockat -!lock renamebE renamefsE imfsetU1 names_rename.
congr mask; rewrite renamepE /= renamem_empty; congr pair.
rewrite renamem_mkpartmapf; apply/eq_partmap=> /= - [i' p].
rewrite !mkpartmapfE renamesE -map_comp /= renameT renames_nth.
by rewrite renamevE size_map.
Qed.

Lemma rename_eval_binop pm b v1 v2 :
  rename pm (eval_binop b v1 v2) =
  eval_binop b (rename pm v1) (rename pm v2).
Proof.
case: b v1 v2 => [] [b1|n1|p1|] [b2|n2|p2|] //=.
by rewrite (can_eq (renameK pm)).
Qed.

Lemma rename_eval_expr pm ls e :
  rename pm (eval_expr true ls e) =
  eval_expr true (rename pm ls) e.
Proof.
elim: e=> [x|n|b e1 IH1 e2 IH2|e IH| |e IH] //=.
- rewrite renamemE /= renameT.
  by case: (ls x)=> [v|] //=.
- by rewrite rename_eval_binop IH1 IH2.
by rewrite -IH; case: eval_expr.
Qed.

Lemma names_stateu s1 s2 :
  fdisjoint (vars_s s1) (vars_s s2) ->
  fdisjoint (pub s1) (pub s2) ->
  names (s1 * s2) = names s1 :|: names s2.
Proof.
case: s1 s2 / bound2P=> [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite !vars_sE !pubE stateuE // => dis1 dis2.
rewrite ![in RHS]namesbE // namesbE //.
have mf': mutfresh A1 (domm h1) A2 (domm h2).
  by apply/(mutfreshS mf); apply/fsubsetU/orP; right; apply/fsubsetUl.
have dis2': fdisjoint (domm h1) (domm h2).
  apply/fdisjoint_names_domm.
  rewrite /fdisjoint -fsubset0; apply/fsubsetP=> i Pi.
  case/and3P: mf'=> [_ _ /fsubsetP/(_ _ Pi)/fsetIP [inA1 inA2]].
  case/fsetIP: Pi=> [in1 in2].
  move/fdisjointP/(_ i): dis2; rewrite !in_fsetI inA1 in1 inA2 in2.
  by move=> /(_ erefl).
rewrite /names /= /prod_names /= !namesm_union_disjoint //.
rewrite -fsetUA [names ls2 :|: _]fsetUC -(fsetUA (names h1)).
by rewrite (fsetUC (names h2)) fsetUA; apply/fsetUSS.
Qed.

Lemma mutfresh_eval_expr A1 ls1 h1 A2 ls2 h2 e p :
  mutfresh A1 (ls1, h1) A2 (ls2, h2) ->
  eval_expr true ls1 e = VPtr p ->
  fdisjoint A1 (A2 :&: names (domm h2)) ->
  h2 p = None.
Proof.
move=> mf eval_e dis; case get_p: (h2 p)=> [v|] //.
move: (eval_expr_names true ls1 e); rewrite eval_e namesvE.
have inNh2: p.1 \in names (domm h2).
  apply/namesfsP; exists p; first by rewrite mem_domm get_p.
  by apply/fsetUP; left; apply/namesnP.
rewrite fsub1set=> inNls1.
have inNs1: p.1 \in names (ls1, h1) by rewrite in_fsetU inNls1.
have inNs2: p.1 \in names (ls2, h2) by rewrite !in_fsetU inNh2 orbT.
case/and3P: mf=> [_ _ /fsubsetP/(_ p.1)].
rewrite in_fsetI inNs1 inNs2=> /(_ erefl) => /fsetIP [inA1 inA2].
by move/fdisjointP/(_ p.1 inA1): dis; rewrite in_fsetI inA2 inNh2.
Qed.

(* Assn *)

Definition bound_assn (x : string) (e : expr) : state -> state :=
  mapb (assn (basic_sem true) x e).

Lemma rename_assn x e : equivariant (assn (basic_sem true) x e).
Proof.
move=> pm /= [ls h] /=.
by rewrite renamepE /= renamem_set rename_eval_expr.
Qed.

Lemma bound_assnE x e A s :
  bound_assn x e (mask A s) = mask A (assn (basic_sem true) x e s).
Proof. by rewrite /bound_assn mapbE //; apply/rename_assn. Qed.

Lemma rename_bound_assn x e : equivariant (bound_assn x e).
Proof. by rewrite /bound_assn; apply/rename_mapb/rename_assn. Qed.

Lemma bound_assn_frame x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_assn x e s1 * s2 = bound_assn x e (s1 * s2).
Proof.
case: s1 s2 / (bound2P s1 s2) => /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE bound_assnE.
have sub1': fsubset (names (setm ls1 x (eval_expr true ls1 e))) (names ls1).
  apply/(fsubset_trans (namesm_set _ _ _)).
  by rewrite fsetU0 fsubUset fsubsetxx /= eval_expr_names.
rewrite stateuE //=; first last.
  apply/(mutfreshEl (rename_assn _ _) mf).
rewrite fsubU1set=> /andP [inD inV]; rewrite stateuE //.
by rewrite bound_assnE //= setm_union eval_expr_unionm.
Qed.

(* Load *)

Definition bound_load x e : state -> option state :=
  @obound _ \o mapb (load (basic_sem true) x e).

Lemma rename_load x e : equivariant (load (basic_sem true) x e).
Proof.
move=> /= pm [ls1 h1] /=.
rewrite -rename_eval_expr; case: eval_expr=> [| |p|] //=.
rewrite renamemE renameK; case: (h1 p)=> [v|] //=.
by rewrite renameoE /= renamepE /= renamem_set.
Qed.

Lemma bound_loadE x e A s :
  bound_load x e (mask A s) = omap (mask A) (load (basic_sem true) x e s).
Proof.
rewrite /bound_load /= mapbE; last exact: rename_load.
by rewrite oboundE.
Qed.

Lemma rename_bound_load x e : equivariant (bound_load x e).
Proof.
apply/equivariant_comp.
  by apply/rename_obound.
by apply/rename_mapb/rename_load.
Qed.

Lemma bound_load_frame_ok x e s1 s1' s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_load x e s1 = Some s1' ->
  bound_load x e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set=> /andP [x_in vars].
rewrite !bound_loadE /=; move: (mutfreshEl (rename_load x e) mf)=> /=.
rewrite stateuE // bound_loadE /= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite unionmE.
case get_p: (h1 p)=> [v|] //= mf'.
by move => - [<-]; rewrite stateuE // ?setm_union.
Qed.

Lemma bound_load_frame_error x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  bound_load x e s1 = None ->
  bound_load x e (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set=> /andP [x_in vars].
rewrite namesbE // pubE=> dis; rewrite bound_loadE /=.
move: (mutfreshEl (rename_load x e) mf)=> /=.
rewrite stateuE // bound_loadE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite unionmE.
case get_p: (h1 p)=> [v|] //= mf' _ {get_p}.
by rewrite (mutfresh_eval_expr mf eval_e).
Qed.

(* Store *)

Definition bound_store e e' : state -> option state :=
  @obound _ \o mapb (store (basic_sem true) e e').

Lemma rename_store e e' : equivariant (store (basic_sem true) e e').
Proof.
move=> /= pm [ls1 h1] /=.
rewrite -rename_eval_expr; case: eval_expr=> [| |p|] //=.
rewrite /updm renamemE renameK; case: (h1 p)=> [v|] //=.
by rewrite renameoE /= renamepE /= renamem_set rename_eval_expr.
Qed.

Lemma bound_storeE e e' A s :
  bound_store e e' (mask A s) = omap (mask A) (store (basic_sem true) e e' s).
Proof.
rewrite /bound_store /= mapbE; last by apply: rename_store.
by rewrite oboundE.
Qed.

Lemma rename_bound_store e e' : equivariant (bound_store e e').
Proof.
apply/equivariant_comp; first by apply/rename_obound.
by apply/rename_mapb/rename_store.
Qed.

Lemma bound_store_frame_ok e e' s1 s1' s2 :
  fsubset (vars_e e :|: vars_e e') (vars_s s1) ->
  bound_store e e' s1 = Some s1' ->
  bound_store e e' (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubUset=> /andP [vars vars'].
rewrite bound_storeE.
move: (mutfreshEl (rename_store e e') mf)=> /=.
rewrite stateuE // bound_storeE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite /updm unionmE.
case get_p: (h1 p)=> [v|] //= mf'.
by move => - [<-]; rewrite stateuE // ?setm_union eval_expr_unionm.
Qed.

Lemma bound_store_frame_error e e' s1 s2 :
  fsubset (vars_e e :|: vars_e e') (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  bound_store e e' s1 = None ->
  bound_store e e' (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubUset=> /andP [vars vars'].
rewrite namesbE // pubE=> dis; rewrite bound_storeE /=.
move: (mutfreshEl (rename_store e e') mf)=> /=.
rewrite stateuE // bound_storeE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite /updm unionmE.
case get_p: (h1 p)=> [v|] //= mf' _.
by rewrite (mutfresh_eval_expr mf eval_e).
Qed.

(* Alloc *)

Definition newblock_def x n i :=
  x ::= VPtr (i, Posz 0) * i :-> nseq n (VNum (Posz 0)).

Lemma rename_newblock_def x n : equivariant (newblock_def x n).
Proof.
move=> /= s i.
rewrite rename_stateu rename_locval rename_blockat renamevE.
have /eq_in_map e: {in nseq n (VNum 0), rename s =1 id}.
  by move=> v /nseqP [-> _].
by rewrite renamesE e map_id.
Qed.

Definition newblock (x : string) (n : nat) : state :=
  new fset0 (newblock_def x n).

Lemma vars_s_newblock x n : vars_s (newblock x n) = fset1 x.
Proof.
rewrite /newblock; move: (fresh _) (freshP fset0)=> i nin.
rewrite (newE nin); last by apply/equivariant_finsupp/rename_newblock_def.
transitivity (vars_s (newblock_def x n i)).
  case: (boundP (newblock_def _ _ _))=> [A [??] ?].
  by rewrite hideE !vars_sE.
by rewrite /newblock_def vars_s_stateu vars_s_locval vars_s_blockat fsetU0.
Qed.

Lemma names_newblock x n : names (newblock x n) = fset0.
Proof.
rewrite /newblock; move: (fresh _) (freshP fset0)=> i nin.
rewrite (newE nin); last by apply/equivariant_finsupp/rename_newblock_def.
rewrite names_hide; apply/eqP; rewrite -fsubset0; apply/fsubsetP=> i'.
move/fsubsetP: (equivariant_names (rename_newblock_def x n) i)=> sub.
rewrite in_fsetD1=> /andP [ne /sub/namesnP ?]; subst i'.
by rewrite eqxx in ne.
Qed.

Lemma pub_newblock x n : pub (newblock x n) = fset0.
Proof.
by apply/eqP; rewrite -fsubset0 -(names_newblock x n) pub_names.
Qed.

Definition eval_nat e (s : locals * heap) :=
  if eval_expr true s.1 e is VNum (Posz n) then Some n
  else None.

Lemma rename_eval_nat e pm s :
  rename pm (eval_nat e s) = eval_nat e (rename pm s).
Proof.
rewrite /eval_nat -rename_eval_expr; case: eval_expr=> //.
by case=> [n|] //.
Qed.

Definition bound_eval_nat e : state -> option nat :=
  locked (@expose _ \o mapb (eval_nat e)).

Lemma bound_eval_natE e A s : bound_eval_nat e (mask A s) = eval_nat e s.
Proof.
rewrite /bound_eval_nat -lock /=.
rewrite mapbE; last exact: rename_eval_nat.
by case: eval_nat=> [n|] //; rewrite exposeE.
Qed.

Lemma rename_bound_eval_nat e : equivariant (bound_eval_nat e).
Proof.
rewrite /bound_eval_nat -lock; apply/equivariant_comp.
  apply/rename_expose.
by apply/rename_mapb/rename_eval_nat.
Qed.

Definition bound_alloc x e (s : state) : option state :=
  if bound_eval_nat e s is Some n then Some (newblock x n * s)
  else None.

Lemma rename_bound_alloc x e : equivariant (bound_alloc x e).
Proof.
move=> pm /= s; rewrite /bound_alloc -rename_bound_eval_nat.
case: bound_eval_nat=> [n|] //=.
rewrite renameoE /= rename_stateu renameT.
rewrite [_ _ (newblock x n)](_ : _ = newblock x n) //.
by apply/names0P/eqP/names_newblock.
Qed.

Lemma bound_alloc_ok x e s1 s1' s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_alloc x e s1 = Some s1' ->
  bound_alloc x e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set => /andP [x_in vars].
rewrite /bound_alloc {1}stateuE // 2!bound_eval_natE /eval_nat /=.
rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] // [<-].
by rewrite stateuA.
Qed.

Lemma bound_alloc_error x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_alloc x e s1 = None ->
  bound_alloc x e (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set => /andP [x_in vars].
rewrite /bound_alloc {1}stateuE // 2!bound_eval_natE /eval_nat /=.
by rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] // [<-].
Qed.

(* Free *)

Definition bound_free e :=
  locked (@obound _ \o mapb (free (basic_sem true) e)).

Lemma rename_free_fun pm h i :
  rename pm (free_fun h i) = free_fun (rename pm h) (rename pm i).
Proof.
rewrite /free_fun; unlock.
rewrite -renamem_curry -renamem_dom mem_imfset_inj; last first.
  by move=> ??; apply: rename_inj.
case: ifP=> //= _.
rewrite renameoE /= renamem_filter; congr Some.
apply: eq_filterm=> p _ /=.
by rewrite (can2_eq (renameKV pm) (renameK pm)).
Qed.

Lemma rename_free e : equivariant (free (basic_sem true) e).
Proof.
move=> /= s [ls h] /=; rewrite -rename_eval_expr.
case: eval_expr=> [| |p|] //=; rewrite renameT.
case: ifP=> // _; rewrite -rename_free_fun.
by case: (free_fun _ _)=> [h'|] //=.
Qed.

Lemma bound_freeE e A s :
  bound_free e (mask A s) = omap (mask A) (free (basic_sem true) e s).
Proof.
rewrite /bound_free -lock /= mapbE; last exact: rename_free.
by rewrite oboundE.
Qed.

Lemma rename_bound_free e : equivariant (bound_free e).
Proof.
move=> pm /= s; rewrite /bound_free -lock.
apply: equivariant_comp; first exact: rename_obound.
by apply/rename_mapb/rename_free.
Qed.

Lemma bound_free_ok e s1 s1' s2 :
  fsubset (vars_e e) (vars_s s1) ->
  fdisjoint (pub s1) (pub s2) ->
  bound_free e s1 = Some s1' ->
  bound_free e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE !pubE => vars dis.
rewrite bound_freeE {1}stateuE // /= bound_freeE /= eval_expr_unionm //.
case eval_e: eval_expr=> [| |p|] //=.
case: ifP=> //= _; rewrite /free_fun -!lock.
rewrite (domm_curry (unionm _ _)) domm_union imfsetU in_fsetU.
rewrite -domm_curry; case: ifP=> //= inD [<-]; congr Some.
rewrite stateuE.
  congr mask; congr pair.
  have dis_h: fdisjoint (names (domm h1)) (names (domm h2)).
    rewrite /fdisjoint -fsubset0; apply/fsubsetP=> n /fsetIP [inD1 inD2].
    case/and3P: mf=> [_ _ /fsubsetP/(_ n)].
    rewrite in_fsetI in_fsetU /= [in X in _ || X]in_fsetU inD1 orbT /=.
    rewrite in_fsetU /= [in X in _ || X]in_fsetU inD2 orbT /= => /(_ erefl).
    case/fsetIP=> [inA1 inA2]; move/eqP: dis=> <-; rewrite !in_fsetI -!andbA.
    by apply/and4P; split.
  rewrite filterm_union //; last by apply/fdisjoint_names_domm.
  congr unionm; apply/eq_partmap=> p'; rewrite filtermE.
  case get_p': (h2 _) => [v|] //=.
  have [Pe|] //= := altP eqP.
  have: p.1 \in names (domm h1).
    move: inD; rewrite domm_curry=> /imfsetP [p'' inD ->].
    by apply/namesfsP; exists p''; last by apply/namesnP.
  move=> /(fdisjointP _ _ dis_h _); rewrite -{}Pe (_ : p'.1 \in _ = true) //.
  apply/namesfsP; exists p'; last by apply/namesnP.
  by apply/dommP; eauto.
apply/(mutfreshS mf); last exact: fsubsetxx.
by apply/fsetUS/namesm_filter.
Qed.

Lemma bound_free_error e s1 s2 :
  fsubset (vars_e e) (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  bound_free e s1 = None ->
  bound_free e (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE namesbE // !pubE => vars dis.
rewrite bound_freeE /= {1}stateuE //= bound_freeE /= eval_expr_unionm //.
case eval_e: eval_expr=> [| |p|] //=.
case: ifP=> //= _; rewrite /free_fun -!lock.
rewrite (domm_curry (unionm _ _)) domm_union imfsetU in_fsetU.
rewrite -domm_curry; case: ifPn=> //= ninD _.
case: ifP=> //= /imfsetP [p' inD ep].
have /and3P [_ _ /fsubsetP/(_ p.1)]: mutfresh A1 ls1 A2 h2.
  by apply/(mutfreshS mf); [apply/fsubsetUl|apply/fsubsetUr].
have inL: p.1 \in names ls1.
  move/fsubsetP: (eval_expr_names true ls1 e); apply.
  by rewrite eval_e in_fsetU; apply/orP; left; apply/namesnP.
have inH: p.1 \in names (domm h2).
  rewrite ep; apply/namesfsP; exists p'=> //.
  by apply/fsetUP; left; apply/namesnP.
rewrite in_fsetI inL in_fsetU inH /= => /(_ erefl)/fsetIP [inA1 inA2].
by move/fdisjointP/(_ p.1 inA1): dis; rewrite in_fsetI inA2 inH.
Qed.

Definition bound_eval_cond e :=
  locked (@expose _ \o mapb (eval_cond (basic_sem true) e)).

Lemma rename_eval_cond e : equivariant (eval_cond (basic_sem true) e).
Proof.
move=> pm [ls h]; rewrite /= -rename_eval_expr.
by case: eval_expr=> //.
Qed.

Lemma bound_eval_condE e A s :
  bound_eval_cond e (mask A s) =
  if eval_expr true s.1 e is VBool b then Some b
  else None.
Proof.
rewrite /bound_eval_cond -lock /= mapbE; last exact: rename_eval_cond.
by rewrite exposeE.
Qed.

Lemma rename_bound_eval_cond e : equivariant (bound_eval_cond e).
Proof.
rewrite /bound_eval_cond -lock.
apply/equivariant_comp.
  by apply/rename_expose.
apply/rename_mapb/rename_eval_cond.
Qed.

Lemma bound_eval_cond_frame e s1 s2 :
  fsubset (vars_e e) (vars_s s1) ->
  bound_eval_cond e (s1 * s2) = bound_eval_cond e s1.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf ? ?].
rewrite vars_sE stateuE // !bound_eval_condE /= => ?.
by rewrite eval_expr_unionm.
Qed.

Definition bound_sem : sem state := {|
  assn := bound_assn;
  load := bound_load;
  store := bound_store;
  alloc := bound_alloc;
  free := bound_free;
  eval_cond := bound_eval_cond
|}.

Lemma rename_result_of_option (T : nominalType) :
  equivariant (@result_of_option T).
Proof. by move=> pm [v|]. Qed.

Lemma result_of_optionD (T : nominalType) o (x : T) :
  result_of_option o = Done x <->
  o = Some x.
Proof. case: o=> [?|] //=; split; congruence. Qed.

Lemma renaming pm s c k :
  rename pm (eval_com bound_sem s c k) =
  eval_com bound_sem (rename pm s) c k.
Proof.
elim: k s c=> [//=|k IH] s c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- by rewrite renamerE rename_bound_assn.
- by rewrite rename_result_of_option rename_bound_load.
- by rewrite rename_result_of_option rename_bound_store.
- by rewrite rename_result_of_option rename_bound_alloc.
- by rewrite rename_result_of_option rename_bound_free.
- by [].
- rewrite -IH; case: eval_com=> // s' /=.
  by rewrite IH.
- rewrite -rename_bound_eval_cond.
  by case: bound_eval_cond => [[|]|] //=.
- rewrite -rename_bound_eval_cond.
  by case: bound_eval_cond => [[|]|] //=.
Qed.

Lemma bound_eval_com_vars s s' c k :
  fsubset (vars_c c) (vars_s s) ->
  eval_com bound_sem s c k = Done s' ->
  vars_s s' = vars_s s.
Proof.
elim: k s s' c => [|k IH] /= s s'; first by [].
case: s / boundP=> /= [A [ls h] subs].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- rewrite fsubU1set !vars_sE=> /andP [Px Pe] [<-].
  rewrite bound_assnE /= !vars_sE domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- rewrite bound_loadE /=.
  case: eval_expr => // p; case: (h p)=> [v|] //=.
  rewrite fsubU1set !vars_sE=> /andP [Px Pe] [<-]; rewrite !vars_sE domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- rewrite bound_storeE !vars_sE /=.
  case: eval_expr => // p; rewrite /updm; case: (h p)=> [v|] //=.
  by rewrite fsubUset=> /andP [Pe Pe'] [<-]; rewrite vars_sE.
- rewrite /bound_alloc bound_eval_natE !vars_sE.
  case: eval_nat => [n|] //; rewrite fsubU1set=> /andP [Px Pe] [<-].
  rewrite vars_s_stateu vars_sE.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; last exact: fsubsetUr.
  by rewrite fsubUset fsubsetxx andbT vars_s_newblock fsub1set.
- rewrite bound_freeE vars_sE /=; case: eval_expr => // p.
  have [|]:= altP eqP=> // _; case: free_fun=> // h'' _ [<-].
  by rewrite vars_sE.
- congruence.
- move=> sub; rewrite vars_sE; case eval_c1: (eval_com _ _ _) => [s''| | ] //.
  move: sub; rewrite fsubUset=> /andP [vars_c1 vars_c2] eval_c2.
  move: (IH _ _ _ vars_c1 eval_c1); rewrite vars_sE=> e.
  rewrite vars_sE -e in vars_c2.
  by rewrite (IH _ _ _ vars_c2 eval_c2).
- rewrite bound_eval_condE; case: eval_expr=> // - b.
  by rewrite 2!fsubUset -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eauto.
rewrite bound_eval_condE; case: eval_expr=> // - [] P; apply: IH.
  by rewrite /= fsetUC -fsetUA fsetUid.
by rewrite fsub0set.
Qed.

Lemma bound_eval_com_pub s s' c k :
  eval_com bound_sem s c k = Done s' ->
  fsubset (pub s') (pub s).
Proof.
elim: k s s' c => [|k IH] /= s s'; first by [].
case: s / boundP=> /= [A [ls h] subs].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- by move=> [<-]; rewrite bound_assnE /= !pubE fsubsetxx.
- rewrite bound_loadE /=; case: eval_expr=> // p.
  by case: (h p)=> // v /= [<-]; rewrite !pubE fsubsetxx.
- rewrite bound_storeE /=; case eval_e: eval_expr=> [| |p|] //=.
  rewrite /updm; case get_p: (h p)=> [v|] //= [<-]; rewrite !pubE.
  rewrite domm_set (_ : p |: domm h = domm h) ?fsubsetxx //.
  apply/eqP; rewrite eqEfsubset fsetU1E fsubsetUr fsubUset fsubsetxx !andbT.
  by apply/fsubsetP=> ? /fset1P ->; rewrite mem_domm get_p.
- rewrite /bound_alloc bound_eval_natE.
  case: eval_nat => [n|] //= [<-].
  by rewrite pubU pub_newblock fset0U fsubsetxx.
- rewrite bound_freeE pubE /=; case: eval_expr => // p.
  case: ifP=> //= _; rewrite /free_fun -lock.
  case: ifP=> //= _ [<-]; rewrite pubE; apply/fsetIS.
  by apply/namesfs_subset/domm_filter.
- move=> [<-]; apply/fsubsetxx.
- case eval_c1: eval_com=> [s''| |] //= eval_c2.
  by apply/(fsubset_trans (IH _ _ _ eval_c2)); eauto.
- by rewrite bound_eval_condE; case: eval_expr=> // - b; eauto.
by rewrite bound_eval_condE; case: eval_expr=> // - [] P; eauto.
Qed.

Lemma eval_com_hide n s c k :
  eval_com bound_sem (hide n s) c k =
  match eval_com bound_sem s c k with
  | Done s' => Done (hide n s')
  | Error => Error
  | NotYet => NotYet
  end.
Proof.
elim: k s c => /= [|k IH] //= s.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- rewrite /bound_assn hide_mapb //.
  exact: rename_assn.
- rewrite /bound_load /= -hide_mapb; last exact: rename_load.
  by rewrite obound_hide result_of_option_omap.
- rewrite /bound_store /= -hide_mapb; last exact: rename_store.
  by rewrite obound_hide result_of_option_omap.
- rewrite /bound_alloc /bound_eval_nat -lock /=.
  rewrite -hide_mapb; last exact: rename_eval_nat.
  rewrite hideT; case: (expose _)=> //= sz.
  rewrite /stateu /= hide_mapb2r //=.
    by move=> s' [[ls1 h1] [ls2 h2]]; rewrite !renamepE /= !renamem_union.
  by rewrite names_newblock in_fset0.
- rewrite /bound_free -lock /= -hide_mapb; last exact: rename_free.
  by rewrite obound_hide result_of_option_omap.
- by rewrite IH; case: eval_com.
- rewrite /bound_eval_cond -lock /= -hide_mapb; last exact: rename_eval_cond.
  by rewrite hideT; case: (expose _).
rewrite /bound_eval_cond -lock /= -hide_mapb; last exact: rename_eval_cond.
by rewrite hideT; case: (expose _).
Qed.

Lemma restriction_ok A (s s' : name -> state) c k :
  finsupp A s -> finsupp A s' ->
  (forall n, n \notin A -> eval_com bound_sem (s n) c k = Done (s' n)) ->
  eval_com bound_sem (new A s) c k = Done (new A s').
Proof.
move=> fs_s fs_s' e; move: (fresh _) (freshP A)=> n ninA.
by rewrite (newE ninA) // (newE ninA) // eval_com_hide e.
Qed.

Lemma restriction_error A (s : name -> state) c k :
  finsupp A s ->
  (forall n, n \notin A -> eval_com bound_sem (s n) c k = Error) ->
  eval_com bound_sem (new A s) c k = Error.
Proof.
move=> fs_s e; move: (fresh _) (freshP A)=> n ninA.
by rewrite (newE ninA) // eval_com_hide e.
Qed.

Lemma restriction_loop A (s : name -> state) c k :
  finsupp A s ->
  (forall n, n \notin A -> eval_com bound_sem (s n) c k = NotYet) ->
  eval_com bound_sem (new A s) c k = NotYet.
Proof.
move=> fs_s e; move: (fresh _) (freshP A)=> n ninA.
by rewrite (newE ninA) // eval_com_hide e.
Qed.

Theorem frame_ok s1 s1' s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (pub s1) (pub s2) ->
  eval_com bound_sem s1 c k = Done s1' ->
  eval_com bound_sem (s1 * s2) c k = Done (s1' * s2).
Proof.
elim: k s1 s1' c => [|k IH] //= s1 s1'.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- by move=> sub _ [<-]; rewrite bound_assn_frame.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/bound_load_frame_ok.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/bound_store_frame_ok.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/bound_alloc_ok.
- move=> sub dis /result_of_optionD ?.
  by apply/result_of_optionD/bound_free_ok.
- by move=> _ _ [<-].
- rewrite fsubUset=> /andP [sub1 sub2] dis.
  case eval_c1: eval_com=> [s1''| |] //=.
  rewrite (IH _ _ _ sub1 dis eval_c1).
  have sub2': fsubset (vars_c c2) (vars_s s1'').
    by rewrite (bound_eval_com_vars sub1 eval_c1).
  apply/(IH _ _ _ sub2').
  by apply/(fdisjoint_trans _ dis)/(bound_eval_com_pub eval_c1).
- rewrite !fsubUset -andbA=> /and3P [sub_e sub1 sub2].
  rewrite bound_eval_cond_frame //.
  case: bound_eval_cond => [b|] //= dis.
  by apply: IH=> //; case: b.
rewrite !fsubUset=> /andP [sub_e sub].
rewrite bound_eval_cond_frame //.
case: bound_eval_cond => [b|] //= dis.
apply: IH=> //; case: b=> //; last by rewrite fsub0set.
by rewrite /= fsubUset fsubUset sub sub_e.
Qed.

Theorem frame_loop s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (pub s1) (pub s2) ->
  eval_com bound_sem s1 c k = NotYet ->
  eval_com bound_sem (s1 * s2) c k = NotYet.
Proof.
elim: k s1 c => [|k IH] //= s1.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- by case: bound_load.
- by case: bound_store.
- by case: bound_alloc.
- by case: bound_free.
- rewrite fsubUset=> /andP [sub1 sub2] dis.
  case eval_c1: eval_com=> [s''| |] //=.
    rewrite (frame_ok sub1 dis eval_c1).
    apply: IH.
      by rewrite (bound_eval_com_vars sub1 eval_c1).
    by apply/(fdisjoint_trans _ dis)/(bound_eval_com_pub eval_c1).
  by rewrite (IH _ _ sub1 dis eval_c1).
- rewrite !fsubUset -andbA=> /and3P [sub_e sub1 sub2].
  rewrite bound_eval_cond_frame //.
  case: bound_eval_cond => [b|] //= dis.
  by apply: IH=> //; case: b.
rewrite !fsubUset=> /andP [sub_e sub].
rewrite bound_eval_cond_frame //.
case: bound_eval_cond => [b|] //= dis.
apply: IH=> //; case: b=> //; last by rewrite fsub0set.
by rewrite /= fsubUset fsubUset sub sub_e.
Qed.

Theorem frame_error s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  eval_com bound_sem s1 c k = Error ->
  eval_com bound_sem (s1 * s2) c k = Error.
Proof.
elim: k s1 c => [|k IH] //= s1.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- move=> sub dis; case Pl: bound_load=> [s1'|] //= _.
  by rewrite (bound_load_frame_error sub dis Pl).
- move=> sub dis; case Ps: bound_store=> [s1'|] //= _.
  by rewrite (bound_store_frame_error sub dis Ps).
- move=> sub dis; case Pa: bound_alloc=> [s1'|] //= _.
  by rewrite (bound_alloc_error _ sub Pa).
- move=> sub dis; case Pa: bound_free=> [s1'|] //= _.
  by rewrite (bound_free_error sub dis Pa).
- rewrite fsubUset=> /andP [sub1 sub2] dis.
  case eval_c1: eval_com=> [s1''| |] //=.
    rewrite (frame_ok sub1 _ eval_c1).
      apply: IH=> //.
      by rewrite (bound_eval_com_vars sub1 eval_c1).
    apply/(fdisjoint_trans _ dis).
    rewrite -[names s1'']/(names (Done s1'')) -eval_c1.
    apply/(@equivariant_names _ _ (fun s => eval_com bound_sem s c1 k))=> /=.
    move=> ??; exact: renaming.
    by apply/(fdisjoint_trans _ dis)/pub_names.
  by rewrite (IH _ _ sub1 dis eval_c1).
- rewrite !fsubUset -andbA=> /and3P [sub_e sub1 sub2].
  rewrite bound_eval_cond_frame //.
  case: bound_eval_cond => [b|] //= dis.
  by apply: IH=> //; case: b.
rewrite !fsubUset=> /andP [sub_e sub].
rewrite bound_eval_cond_frame //.
case: bound_eval_cond => [b|] //= dis.
apply: IH=> //; case: b=> //; last by rewrite fsub0set.
by rewrite /= fsubUset fsubUset sub sub_e.
Qed.

Corollary noninterference s1 s21 s' s22 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (names s1) (pub s21) ->
  fdisjoint (pub s1) (pub s22) ->
  eval_com bound_sem (s1 * s21) c k = Done s' ->
  exists s1',
    [/\ eval_com bound_sem s1 c k = Done s1',
        s' = s1' * s21 &
        eval_com bound_sem (s1 * s22) c k = Done (s1' * s22)].
Proof.
move=> sub dis1 dis2 eval_c.
case eval_c': (eval_com bound_sem s1 c k) => [s1'| |] //=.
- exists s1'; split; eauto.
    move: eval_c; rewrite (frame_ok sub _ eval_c'); first congruence.
    by apply/(fdisjoint_trans _ dis1)/pub_names.
  by apply: frame_ok=> //.
- by rewrite (frame_error sub dis1 eval_c') in eval_c.
rewrite (frame_loop sub _ eval_c') // in eval_c.
by apply/(fdisjoint_trans _ dis1)/pub_names.
Qed.

End Structured.

Notation "s1 * s2" := (stateu s1 s2) : state_scope.
Notation "x ::= v" := (locval x v) (at level 20) : state_scope.
Notation "i :-> vs" := (blockat i vs) (at level 20) : state_scope.

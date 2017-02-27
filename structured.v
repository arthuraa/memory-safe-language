From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From CoqUtils Require Import ord fset partmap fperm nominal string.

Require Import basic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Structured.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Implicit Types (ls : locals) (h : heap) (x : string) (st : locals * heap).

Definition state := {restr locals * heap}.

(* XXX: The term below, while seemingly innocent, gets actually quite
   big when printed out fully. Maybe this suggests a refactoring in
   the basic definitions to make terms smaller? *)
Lemma stateu_key : unit. Proof. exact: tt. Qed.
Definition stateu_def : state -> state -> state :=
  mapr2 (fun s1 s2 => (unionm s1.1 s2.1, unionm s1.2 s2.2)).
Definition stateu := locked_with stateu_key stateu_def.

Notation "s1 * s2" := (stateu s1 s2) : state_scope.

Local Open Scope state_scope.

Lemma stateuE A1 ls1 h1 A2 ls2 h2 :
  mutfresh A1 (ls1, h1) A2 (ls2, h2) ->
  mask A1 (ls1, h1) * mask A2 (ls2, h2) =
  mask (A1 :|: A2) (unionm ls1 ls2, unionm h1 h2).
Proof.
move=> mf; rewrite [stateu]unlock /stateu_def /=.
rewrite mapr2E //= => {ls1 h1 ls2 h2 mf} /= pm [[ls1 h1] [ls2 h2]] /=.
by rewrite !renamepE !renamem_union.
Qed.

Lemma rename_stateu pm (s1 s2 : state) :
  rename pm (s1 * s2) = rename pm s1 * rename pm s2.
Proof.
rewrite [stateu]unlock /stateu_def rename_mapr2 //=.
move=> {pm s1 s2} pm /= [[ls1 h1] [ls2 h2]] /=.
by rewrite !renamepE !renamem_union.
Qed.

Definition emp : state := mask fset0 (emptym, emptym).

Lemma names_emp : names emp = fset0.
Proof. by rewrite /emp namesrE // fsetDUl /= !namesm_empty !fset0D fset0U. Qed.

Lemma stateu0s : left_id emp stateu.
Proof.
rewrite [stateu]unlock /stateu_def /=.
apply: restr_left_id=> /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls h] /=; rewrite !union0m.
Qed.

Lemma stateus0 : right_id emp stateu.
Proof.
rewrite [stateu]unlock; apply: restr_right_id=> /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls h] /=; rewrite !unionm0.
Qed.

Lemma stateuA : associative stateu.
Proof.
rewrite [stateu]unlock; apply: restr_associative => /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls1 h1] [ls2 h2] [ls3 h3] /=; rewrite !unionmA.
Qed.

Lemma new_stateul A (f : name -> state) s :
  finsupp A f ->
  new A f * s = new (A :|: names s) (fun a => f a * s).
Proof.
move=> fs_f; rewrite [stateu]unlock /stateu_def /= new_comp2l //=.
move=> /= {s} pm [[ls1 h1] [ls2 h2]] /=.
by rewrite renamepE /= !renamem_union.
Qed.

Lemma new_stateur s A (f : name -> state) :
  finsupp A f ->
  s * new A f = new (names s :|: A) (fun a => s * f a).
Proof.
move=> fs_f; rewrite [stateu]unlock /stateu_def /= new_comp2r //=.
move=> /= {s} pm [[ls1 h1] [ls2 h2]] /=.
by rewrite renamepE /= !renamem_union.
Qed.

Definition vars_s (s : state) : {fset string} :=
  expose (mapr (fun s => domm s.1) s).

Lemma vars_sE A ls h : vars_s (mask A (ls, h)) = domm ls.
Proof.
rewrite /vars_s /= maprE ?exposeE //.
by move=> pm /= {ls h} [ls h] /=; rewrite -renamem_dom.
Qed.

Lemma vars_s_stateu s1 s2 :
  vars_s (s1 * s2) = vars_s s1 :|: vars_s s2.
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
by rewrite stateuE // !vars_sE domm_union.
Qed.

Lemma vars_emp : vars_s emp = fset0.
Proof. by rewrite /emp vars_sE domm0. Qed.

Lemma vars_s_hide n s : vars_s (hide n s) = vars_s s.
Proof.
by case: s / (restrP fset0)=> [A [ls h] sub]; rewrite hideE !vars_sE.
Qed.

Definition pub (s : state) : {fset name} :=
  names (mapr (fun s => domm s.2) s).

Lemma pubE A ls h : pub (mask A (ls, h)) = names (domm h) :\: A.
Proof.
rewrite /pub /= maprE /= 1?maskE 1?namesrE ?fsubsetIr //.
by move=> pm {ls h} /= [ls h]; rewrite renamem_dom.
Qed.

Lemma pubU s1 s2 : pub (s1 * s2) = pub s1 :|: pub s2.
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf ? ?].
rewrite stateuE // !pubE domm_union namesfsU fsetDUl !fsetDUr.
have /fsetDidPl ->: fdisjoint (names (domm h1)) A2.
  case/andP: mf=> _; rewrite fdisjointC fdisjointUl /= => /andP [_].
  by rewrite namesmE fdisjointUl=> /andP [].
have /fsetDidPl ->: fdisjoint (names (domm h2)) A1.
  case/andP: mf; rewrite fdisjointC fdisjointUl /= => /andP [_].
  by rewrite namesmE fdisjointUl=> /andP [].
have /fsetIidPl ->: fsubset (names (domm h1) :\: A1) (names (domm h1)).
  by rewrite fsubDset fsubsetUr.
suff /fsetIidPr ->: fsubset (names (domm h2) :\: A2) (names (domm h2)) by [].
by rewrite fsubDset fsubsetUr.
Qed.

Lemma pub_names s : fsubset (pub s) (names s).
Proof.
case: s / (restrP fset0)=> /= [A [ls h] sub _].
rewrite namesrE // pubE; apply: fsetSD; apply: fsubsetU.
by apply/orP; right; rewrite namesmE; apply: fsubsetUl.
Qed.

Lemma pub_emp : pub emp = fset0.
Proof. by rewrite /emp pubE domm0 namesfs0 fset0D. Qed.

Lemma pub_hide n s : pub (hide n s) = pub s :\ n.
Proof.
case: s / (restrP fset0)=> [A [ls h] _ sub]; rewrite hideE !pubE.
by apply/eq_fset=> i; rewrite in_fsetD1 !in_fsetD !in_fsetU1 negb_or andbA.
Qed.

Lemma stateuC s1 s2 :
  fdisjoint (vars_s s1) (vars_s s2) ->
  fdisjoint (pub s1) (pub s2) ->
  s1 * s2 = s2 * s1.
Proof.
case: s1 s2 / restr2P=> [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite !vars_sE !pubE stateuE // stateuE 1?mutfresh_sym // fsetUC.
move=> disv dish; rewrite unionmC // [_ h1 _]unionmC //.
apply: fdisjoint_names_domm.
apply/fdisjointP=> i in_h1; apply/negP=> in_h2.
suff /fsetIP [in1 in2] :
  i \in (names (domm h1) :\: A1) :&: (names (domm h2) :\: A2).
  by move/fdisjointP/(_ i): dish=> /(_ in1)/negP; apply.
rewrite in_fsetI 2!in_fsetD in_h1 in_h2 !andbT.
case/andP: mf.
rewrite fdisjointUr /= => /andP [_].
rewrite fdisjointUr /= fdisjointC => /andP [/fdisjointP/(_ _ in_h2) -> _].
rewrite fdisjointUr /= => /andP [_].
by rewrite fdisjointUr /= fdisjointC => /andP [/fdisjointP/(_ _ in_h1) -> _].
Qed.

Definition locval (x : string) (v : value) : state :=
  mask fset0 (setm emptym x v, emptym).

Notation "x ::= v" := (locval x v) (at level 20) : state_scope.

Local Open Scope state_scope.

Lemma vars_s_locval x v : vars_s (x ::= v) = fset1 x.
Proof.
by rewrite /locval vars_sE domm_set domm0 fsetU0.
Qed.

Lemma names_locval x v : names (x ::= v) = names v.
Proof.
rewrite /locval namesrE // fsetD0 namespE /= namesm_empty fsetU0.
apply/eqP; rewrite eqEfsubset; apply/andP; split.
  apply/(fsubset_trans (namesm_set _ _ _)).
  by rewrite namesm_empty namesT !fset0U fsubsetxx.
apply/fsubsetP=> i i_in; apply/namesmP.
have get_x: setm emptym x v x = Some v by rewrite setmE eqxx.
exact: PMFreeNamesVal get_x i_in.
Qed.

Lemma pub_locval x v : pub (x ::= v) = fset0.
Proof.
by apply/eqP; rewrite -fsubset0 /locval pubE domm0 namesfs0 fsetD0 fsubsetxx.
Qed.

Lemma rename_locval s x v :
  rename s (x ::= v) = x ::= rename s v.
Proof.
rewrite /locval renamerE renamefs0 renamepE /= renamem_set.
by rewrite !renamem_empty renameT.
Qed.

Notation "i :-> vs" :=
  (mask fset0 (emptym, mkblock i vs) : state) (at level 20) : state_scope.

Lemma vars_s_blockat i vs : vars_s (i :-> vs) = fset0.
Proof. by rewrite vars_sE domm0. Qed.

Lemma pub_blockat i vs :
  pub (i :-> vs) = if vs is [::] then fset0 else fset1 i.
Proof.
by rewrite pubE fsetD0 names_domm_mkblock; case: vs.
Qed.

Lemma names_blockat i vs :
  names (i :-> vs) =
  if nilp vs then fset0 else i |: names vs.
Proof.
by rewrite namesrE fsetD0 namespE /= namesm_empty fset0U names_mkblock.
Qed.

Lemma rename_blockat s i vs :
  rename s (i :-> vs) = s i :-> rename s vs.
Proof.
rewrite renamerE renamefs0; congr mask.
by rewrite renamepE /= renamem_empty rename_mkblock.
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
elim: e=> [x|b|n|b e1 IH1 e2 IH2|e IH| |e IH] //=.
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
case: s1 s2 / restr2P=> [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite !vars_sE !pubE stateuE // => dis1 dis2.
rewrite ![in RHS]namesrE // namesrE //.
have mf': mutfresh A1 (domm h1) A2 (domm h2).
  by apply/(mutfreshS mf); apply/fsubsetU/orP; right; apply/fsubsetUl.
have dis2': fdisjoint (domm h1) (domm h2).
  apply/fdisjoint_names_domm.
  rewrite /fdisjoint -fsubset0; apply/fsubsetP=> i /fsetIP [Pi1 Pi2].
  case/andP: mf'=> []; rewrite fdisjointC=> /fdisjointP dish1.
  rewrite fdisjointC=> /fdisjointP dish2.
  move/fdisjointP/(_ i): dis2; rewrite in_fsetD (dish1 _ Pi2) /= => /(_ Pi1).
  by rewrite in_fsetD Pi2 andbT (dish2 _ Pi1).
rewrite namespE /= !namesm_union_disjoint //.
rewrite -fsetUA [names ls2 :|: _]fsetUC -(fsetUA (names h1)).
rewrite (fsetUC (names h2)) fsetUA -(namespE (ls1, h1)) -(namespE (ls2, h2)).
rewrite fsetDUl 2!fsetDUr; case/andP: mf; rewrite fdisjointC=> /fsetDidPl ->.
rewrite fdisjointC=> /fsetDidPl=> ->; congr fsetU.
  by apply/fsetIidPl; rewrite fsubDset fsubsetUr.
by apply/fsetIidPr; rewrite fsubDset fsubsetUr.
Qed.

Lemma mutfresh_eval_expr A1 ls1 h1 A2 ls2 h2 e p :
  mutfresh A1 (ls1, h1) A2 (ls2, h2) ->
  eval_expr true ls1 e = VPtr p ->
  fdisjoint (names (ls1, h1) :\: A1) (names (domm h2) :\: A2) ->
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
case/andP: mf=> [/fdisjointP/(_ p.1)/contraTN/(_ inNs2) dis1].
move=> /fdisjointP/(_ p.1)/contraTN/(_ inNs1) dis2.
move/fdisjointP/(_ p.1): dis.
by rewrite !in_fsetD dis1 inNh2 dis2=> /(_ inNs1).
Qed.

(* Assn *)

Definition restr_assn (x : string) (e : expr) : state -> state :=
  mapr (assn (basic_sem true) x e).

Lemma rename_assn x e : equivariant (assn (basic_sem true) x e).
Proof.
move=> pm /= [ls h] /=.
by rewrite renamepE /= renamem_set rename_eval_expr.
Qed.

Lemma restr_assnE x e A s :
  restr_assn x e (mask A s) = mask A (assn (basic_sem true) x e s).
Proof. by rewrite /restr_assn maprE //; apply/rename_assn. Qed.

Lemma rename_restr_assn x e : equivariant (restr_assn x e).
Proof. by rewrite /restr_assn; apply/rename_mapr/rename_assn. Qed.

Lemma restr_assn_frame x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  restr_assn x e s1 * s2 = restr_assn x e (s1 * s2).
Proof.
case: s1 s2 / (restr2P s1 s2) => /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE restr_assnE.
have sub1': fsubset (names (setm ls1 x (eval_expr true ls1 e))) (names ls1).
  apply/(fsubset_trans (namesm_set _ _ _)).
  by rewrite fsetU0 fsubUset fsubsetxx /= eval_expr_names.
rewrite stateuE //=; first last.
  apply/(mutfreshEl (rename_assn _ _) mf).
rewrite fsubU1set=> /andP [inD inV]; rewrite stateuE //.
by rewrite restr_assnE //= setm_union eval_expr_unionm.
Qed.

(* Load *)

Definition restr_load x e : state -> option state :=
  @orestr _ \o mapr (load (basic_sem true) x e).

Lemma rename_load x e : equivariant (load (basic_sem true) x e).
Proof.
move=> /= pm [ls1 h1] /=.
rewrite -rename_eval_expr; case: eval_expr=> [| |p|] //=.
rewrite renamemE renameK; case: (h1 p)=> [v|] //=.
by rewrite renameoE /= renamepE /= renamem_set.
Qed.

Lemma restr_loadE x e A s :
  restr_load x e (mask A s) = omap (mask A) (load (basic_sem true) x e s).
Proof.
rewrite /restr_load /= maprE; last exact: rename_load.
by rewrite orestrE.
Qed.

Lemma rename_restr_load x e : equivariant (restr_load x e).
Proof.
apply/equivariant_comp.
  by apply/rename_orestr.
by apply/rename_mapr/rename_load.
Qed.

Lemma restr_load_frame_ok x e s1 s1' s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  restr_load x e s1 = Some s1' ->
  restr_load x e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set=> /andP [x_in vars].
rewrite !restr_loadE /=; move: (mutfreshEl (rename_load x e) mf)=> /=.
rewrite stateuE // restr_loadE /= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite unionmE.
case get_p: (h1 p)=> [v|] //= mf'.
by move => - [<-]; rewrite stateuE // ?setm_union.
Qed.

Lemma restr_load_frame_error x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  restr_load x e s1 = None ->
  restr_load x e (s1 * s2) = None.
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set=> /andP [x_in vars].
rewrite namesrE // pubE=> dis; rewrite restr_loadE /=.
move: (mutfreshEl (rename_load x e) mf)=> /=.
rewrite stateuE // restr_loadE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite unionmE.
case get_p: (h1 p)=> [v|] //= mf' _ {get_p}.
by rewrite (mutfresh_eval_expr mf eval_e).
Qed.

(* Store *)

Definition restr_store e e' : state -> option state :=
  @orestr _ \o mapr (store (basic_sem true) e e').

Lemma rename_store e e' : equivariant (store (basic_sem true) e e').
Proof.
move=> /= pm [ls1 h1] /=.
rewrite -rename_eval_expr; case: eval_expr=> [| |p|] //=.
rewrite /updm renamemE renameK; case: (h1 p)=> [v|] //=.
by rewrite renameoE /= renamepE /= renamem_set rename_eval_expr.
Qed.

Lemma restr_storeE e e' A s :
  restr_store e e' (mask A s) = omap (mask A) (store (basic_sem true) e e' s).
Proof.
rewrite /restr_store /= maprE; last by apply: rename_store.
by rewrite orestrE.
Qed.

Lemma rename_restr_store e e' : equivariant (restr_store e e').
Proof.
apply/equivariant_comp; first by apply/rename_orestr.
by apply/rename_mapr/rename_store.
Qed.

Lemma restr_store_frame_ok e e' s1 s1' s2 :
  fsubset (vars_e e :|: vars_e e') (vars_s s1) ->
  restr_store e e' s1 = Some s1' ->
  restr_store e e' (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubUset=> /andP [vars vars'].
rewrite restr_storeE.
move: (mutfreshEl (rename_store e e') mf)=> /=.
rewrite stateuE // restr_storeE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite /updm unionmE.
case get_p: (h1 p)=> [v|] //= mf'.
by move => - [<-]; rewrite stateuE // ?setm_union eval_expr_unionm.
Qed.

Lemma restr_store_frame_error e e' s1 s2 :
  fsubset (vars_e e :|: vars_e e') (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  restr_store e e' s1 = None ->
  restr_store e e' (s1 * s2) = None.
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubUset=> /andP [vars vars'].
rewrite namesrE // pubE=> dis; rewrite restr_storeE /=.
move: (mutfreshEl (rename_store e e') mf)=> /=.
rewrite stateuE // restr_storeE //= eval_expr_unionm //.
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
  case: (restrP fset0 (newblock_def _ _ _))=> [A [??] ?].
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

Definition restr_eval_nat e : state -> option nat :=
  locked (@expose _ \o mapr (eval_nat e)).

Lemma restr_eval_natE e A s : restr_eval_nat e (mask A s) = eval_nat e s.
Proof.
rewrite /restr_eval_nat -lock /=.
rewrite maprE; last exact: rename_eval_nat.
by case: eval_nat=> [n|] //; rewrite exposeE.
Qed.

Lemma rename_restr_eval_nat e : equivariant (restr_eval_nat e).
Proof.
rewrite /restr_eval_nat -lock; apply/equivariant_comp.
  apply/rename_expose.
by apply/rename_mapr/rename_eval_nat.
Qed.

Definition restr_alloc x e (s : state) : option state :=
  if restr_eval_nat e s is Some n then Some (newblock x n * s)
  else None.

Lemma rename_restr_alloc x e : equivariant (restr_alloc x e).
Proof.
move=> pm /= s; rewrite /restr_alloc -rename_restr_eval_nat.
case: restr_eval_nat=> [n|] //=.
rewrite renameoE /= rename_stateu renameT.
rewrite [_ _ (newblock x n)](_ : _ = newblock x n) //.
by apply/names0P/eqP/names_newblock.
Qed.

Lemma restr_allocE x e A st i :
  i \notin names st ->
  restr_alloc x e (mask A st) =
  if eval_expr true st.1 e is VNum (Posz n) then
    Some (mask (i |: A) (setm st.1 x (VPtr (i, Posz 0)),
                         unionm (mkblock i (nseq n (VNum 0))) st.2))
  else None.
Proof.
rewrite /restr_alloc restr_eval_natE /eval_nat.
case: eval_expr=> [ |[n|]| | ] i_fresh //=.
have eA : i |: A = i |: A :\ i.
  apply/eq_fset=> i'; rewrite 2!in_fsetU1 in_fsetD1.
  by have [->|] //= := altP eqP.
have -> : mask A st = mask (A :\ i) st.
  rewrite -[LHS](@hideD _ i) ?namesrE ?in_fsetD ?(negbTE i_fresh) ?andbF //.
  rewrite -[RHS](@hideD _ i) ?namesrE ?in_fsetD ?(negbTE i_fresh) ?andbF //.
  by rewrite !hideE eA.
rewrite eA.
have i_fresh' : i \notin A :\ i by rewrite in_fsetD1 eqxx.
move: (A :\ i) i_fresh' => {A eA} A i_fresh'.
rewrite /newblock new_stateul; last first.
  by move=> ???; rewrite rename_newblock_def.
have {i_fresh} i_fresh : i \notin names (mask A st).
  by apply: contra i_fresh; rewrite namesrE => /fsetDP [->].
case: st i_fresh => /= [ls h] i_fresh.
rewrite fset0U (newE i_fresh).
  rewrite /newblock_def /locval /= stateuE /mutfresh ?fdisjoint0 //.
  rewrite unionm0 union0m fset0U stateuE ?fset0U ?hideE //.
  rewrite /mutfresh fdisjoint0 /= fdisjointC.
  rewrite -fdisjoints1 fdisjointC in i_fresh'.
  apply: fdisjoint_trans; try eassumption.
  rewrite namespE /= names_mkblock names_nseq if_same fsetU0.
  rewrite fsubUset; apply/andP; split.
    apply: fsubset_trans; first apply: namesm_set.
    by rewrite namesm_empty fsetU0 fset0U namesvE fsubsetxx.
  by case: ifP; rewrite ?fsub0set ?fsubsetxx.
move=> /= pm dis i'; rewrite rename_stateu rename_newblock_def.
by congr stateu; rewrite names_disjointE.
Qed.

Lemma restr_alloc_ok x e s1 s1' s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  restr_alloc x e s1 = Some s1' ->
  restr_alloc x e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set => /andP [x_in vars].
rewrite /restr_alloc {1}stateuE // 2!restr_eval_natE /eval_nat /=.
rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] // [<-].
by rewrite stateuA.
Qed.

Lemma restr_alloc_error x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  restr_alloc x e s1 = None ->
  restr_alloc x e (s1 * s2) = None.
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set => /andP [x_in vars].
rewrite /restr_alloc {1}stateuE // 2!restr_eval_natE /eval_nat /=.
by rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] // [<-].
Qed.

(* Free *)

Definition restr_free e :=
  locked (@orestr _ \o mapr (free (basic_sem true) e)).

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

Lemma restr_freeE e A s :
  restr_free e (mask A s) = omap (mask A) (free (basic_sem true) e s).
Proof.
rewrite /restr_free -lock /= maprE; last exact: rename_free.
by rewrite orestrE.
Qed.

Lemma rename_restr_free e : equivariant (restr_free e).
Proof.
move=> pm /= s; rewrite /restr_free -lock.
apply: equivariant_comp; first exact: rename_orestr.
by apply/rename_mapr/rename_free.
Qed.

Lemma restr_free_ok e s1 s1' s2 :
  fsubset (vars_e e) (vars_s s1) ->
  fdisjoint (pub s1) (pub s2) ->
  restr_free e s1 = Some s1' ->
  restr_free e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE !pubE => vars dis.
rewrite restr_freeE {1}stateuE // /= restr_freeE /= eval_expr_unionm //.
case eval_e: eval_expr=> [| |p|] //=.
case: ifP=> //= _; rewrite /free_fun -!lock.
rewrite (domm_curry (unionm _ _)) domm_union imfsetU in_fsetU.
rewrite -domm_curry; case: ifP=> //= inD [<-]; congr Some.
rewrite stateuE.
  congr mask; congr pair.
  have dis_h: fdisjoint (names (domm h1)) (names (domm h2)).
    rewrite /fdisjoint -fsubset0; apply/fsubsetP=> n /fsetIP [inD1 inD2].
    case/andP: mf => [/fdisjointP/(_ n) dis1 /fdisjointP/(_ n) dis2].
    move/contraTN: dis1; move/contraTN: dis2.
    rewrite in_fsetU /= [in X in _ || X]in_fsetU inD1 orbT /= => ninA2.
    rewrite in_fsetU /= [in X in _ || X]in_fsetU inD2 orbT /= => ninA1.
    move/fdisjointP/(_ n): dis; rewrite !in_fsetD ninA1 // ninA2 //= inD2.
    by move/(_ inD1).
  rewrite filterm_union //; last by apply/fdisjoint_names_domm.
  congr unionm; apply/eq_partmap=> p'; rewrite filtermE.
  case get_p': (h2 _) => [v|] //=.
  have [Pe|] //= := altP eqP.
  have: p.1 \in names (domm h1).
    move: inD; rewrite domm_curry=> /imfsetP [p'' inD ->].
    by apply/namesfsP; exists p''; last by apply/fsetUP; left; apply/namesnP.
  move=> /(fdisjointP _ _ dis_h _); rewrite -{}Pe (_ : p'.1 \in _ = true) //.
  apply/namesfsP; exists p'; last by apply/fsetUP; left; apply/namesnP.
  by apply/dommP; eauto.
apply/(mutfreshS mf); last exact: fsubsetxx.
by apply/fsetUS/namesm_filter.
Qed.

Lemma restr_free_error e s1 s2 :
  fsubset (vars_e e) (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  restr_free e s1 = None ->
  restr_free e (s1 * s2) = None.
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE namesrE // !pubE => vars dis.
rewrite restr_freeE /= {1}stateuE //= restr_freeE /= eval_expr_unionm //.
case eval_e: eval_expr=> [| |p|] //=.
case: ifP=> //= _; rewrite /free_fun -!lock.
rewrite (domm_curry (unionm _ _)) domm_union imfsetU in_fsetU.
rewrite -domm_curry; case: ifPn=> //= ninD _.
case: ifP=> //= /imfsetP [p' inD ep].
have /andP []: mutfresh A1 ls1 A2 h2.
  by apply/(mutfreshS mf); [apply/fsubsetUl|apply/fsubsetUr].
have inL: p.1 \in names ls1.
  move/fsubsetP: (eval_expr_names true ls1 e); apply.
  by rewrite eval_e in_fsetU; apply/orP; left; apply/namesnP.
have inH: p.1 \in names (domm h2).
  rewrite ep; apply/namesfsP; exists p'=> //.
  by apply/fsetUP; left; apply/namesnP.
rewrite fdisjointC fdisjointUl => /andP [/fdisjointP/(_ _ inH) ninA1 _].
rewrite fdisjointC=> /fdisjointP/(_ _ inL) ninA2.
move/fdisjointP/(_ p.1): dis; rewrite !in_fsetD ninA1 in_fsetU inL ninA2 inH.
by move=> /(_ erefl).
Qed.

Definition restr_eval_cond e :=
  locked (@expose _ \o mapr (eval_cond (basic_sem true) e)).

Lemma rename_eval_cond e : equivariant (eval_cond (basic_sem true) e).
Proof.
move=> pm [ls h]; rewrite /= -rename_eval_expr.
by case: eval_expr=> //.
Qed.

Lemma restr_eval_condE e A s :
  restr_eval_cond e (mask A s) =
  if eval_expr true s.1 e is VBool b then Some b
  else None.
Proof.
rewrite /restr_eval_cond -lock /= maprE; last exact: rename_eval_cond.
by rewrite exposeE.
Qed.

Lemma rename_restr_eval_cond e : equivariant (restr_eval_cond e).
Proof.
rewrite /restr_eval_cond -lock.
apply/equivariant_comp.
  by apply/rename_expose.
apply/rename_mapr/rename_eval_cond.
Qed.

Lemma restr_eval_cond_frame e s1 s2 :
  fsubset (vars_e e) (vars_s s1) ->
  restr_eval_cond e (s1 * s2) = restr_eval_cond e s1.
Proof.
case: s1 s2 / restr2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf ? ?].
rewrite vars_sE stateuE // !restr_eval_condE /= => ?.
by rewrite eval_expr_unionm.
Qed.

Definition restr_sem : sem state := {|
  assn := restr_assn;
  load := restr_load;
  store := restr_store;
  alloc := restr_alloc;
  free := restr_free;
  eval_cond := restr_eval_cond
|}.

Lemma rename_result_of_option (T : nominalType) :
  equivariant (@result_of_option T).
Proof. by move=> pm [v|]. Qed.

Lemma result_of_optionD (T : nominalType) o (x : T) :
  result_of_option o = Done x <->
  o = Some x.
Proof. case: o=> [?|] //=; split; congruence. Qed.

Lemma renaming pm s c k :
  rename pm (eval_com restr_sem s c k) =
  eval_com restr_sem (rename pm s) c k.
Proof.
elim: k s c=> [//=|k IH] s c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- by rewrite renameresE rename_restr_assn.
- by rewrite rename_result_of_option rename_restr_load.
- by rewrite rename_result_of_option rename_restr_store.
- by rewrite rename_result_of_option rename_restr_alloc.
- by rewrite rename_result_of_option rename_restr_free.
- by [].
- rewrite -IH; case: eval_com=> // s' /=.
  by rewrite IH.
- rewrite -rename_restr_eval_cond.
  by case: restr_eval_cond => [[|]|] //=.
- rewrite -rename_restr_eval_cond.
  by case: restr_eval_cond => [[|]|] //=.
Qed.

Lemma restr_eval_com_vars s s' c k :
  fsubset (vars_c c) (vars_s s) ->
  eval_com restr_sem s c k = Done s' ->
  vars_s s' = vars_s s.
Proof.
elim: k s s' c => [|k IH] /= s s'; first by [].
case: s / (restrP fset0) => /= [A [ls h] _ subs].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- rewrite fsubU1set !vars_sE=> /andP [Px Pe] [<-].
  rewrite restr_assnE /= !vars_sE domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- rewrite restr_loadE /=.
  case: eval_expr => // p; case: (h p)=> [v|] //=.
  rewrite fsubU1set !vars_sE=> /andP [Px Pe] [<-]; rewrite !vars_sE domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- rewrite restr_storeE !vars_sE /=.
  case: eval_expr => // p; rewrite /updm; case: (h p)=> [v|] //=.
  by rewrite fsubUset=> /andP [Pe Pe'] [<-]; rewrite vars_sE.
- rewrite /restr_alloc restr_eval_natE !vars_sE.
  case: eval_nat => [n|] //; rewrite fsubU1set=> /andP [Px Pe] [<-].
  rewrite vars_s_stateu vars_sE.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; last exact: fsubsetUr.
  by rewrite fsubUset fsubsetxx andbT vars_s_newblock fsub1set.
- rewrite restr_freeE vars_sE /=; case: eval_expr => // p.
  have [|]:= altP eqP=> // _; case: free_fun=> // h'' _ [<-].
  by rewrite vars_sE.
- congruence.
- move=> sub; rewrite vars_sE; case eval_c1: (eval_com _ _ _) => [s''| | ] //.
  move: sub; rewrite fsubUset=> /andP [vars_c1 vars_c2] eval_c2.
  move: (IH _ _ _ vars_c1 eval_c1); rewrite vars_sE=> e.
  rewrite vars_sE -e in vars_c2.
  by rewrite (IH _ _ _ vars_c2 eval_c2).
- rewrite restr_eval_condE; case: eval_expr=> // - b.
  by rewrite 2!fsubUset -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eauto.
rewrite restr_eval_condE; case: eval_expr=> // - [] P; apply: IH.
  by rewrite /= fsetUC -fsetUA fsetUid.
by rewrite fsub0set.
Qed.

Lemma restr_eval_com_pub s s' c k :
  eval_com restr_sem s c k = Done s' ->
  fsubset (pub s') (pub s).
Proof.
elim: k s s' c => [|k IH] /= s s'; first by [].
case: s / (restrP fset0)=> /= [A [ls h] _ subs].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- by move=> [<-]; rewrite restr_assnE /= !pubE fsubsetxx.
- rewrite restr_loadE /=; case: eval_expr=> // p.
  by case: (h p)=> // v /= [<-]; rewrite !pubE fsubsetxx.
- rewrite restr_storeE /=; case eval_e: eval_expr=> [| |p|] //=.
  rewrite /updm; case get_p: (h p)=> [v|] //= [<-]; rewrite !pubE.
  rewrite domm_set (_ : p |: domm h = domm h) ?fsubsetxx //.
  apply/eqP; rewrite eqEfsubset fsubsetUr fsubUset fsubsetxx !andbT.
  by apply/fsubsetP=> ? /fset1P ->; rewrite mem_domm get_p.
- rewrite /restr_alloc restr_eval_natE.
  case: eval_nat => [n|] //= [<-].
  by rewrite pubU pub_newblock fset0U fsubsetxx.
- rewrite restr_freeE pubE /=; case: eval_expr => // p.
  case: ifP=> //= _; rewrite /free_fun -lock.
  case: ifP=> //= _ [<-]; rewrite pubE; apply/fsetSD.
  by apply/namesfs_subset/domm_filter.
- move=> [<-]; apply/fsubsetxx.
- case eval_c1: eval_com=> [s''| |] //= eval_c2.
  by apply/(fsubset_trans (IH _ _ _ eval_c2)); eauto.
- by rewrite restr_eval_condE; case: eval_expr=> // - b; eauto.
by rewrite restr_eval_condE; case: eval_expr=> // - [] P; eauto.
Qed.

Lemma eval_com_hiden A s c k :
  eval_com restr_sem (hiden A s) c k =
  match eval_com restr_sem s c k with
  | Done s' => Done (hiden A s')
  | Error => Error
  | NotYet => NotYet
  end.
Proof.
elim: k s c => /= [|k IH] //= s.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- rewrite /restr_assn hiden_mapr //.
  exact: rename_assn.
- rewrite /restr_load /= -hiden_mapr; last exact: rename_load.
  by rewrite orestr_hiden result_of_option_omap.
- rewrite /restr_store /= -hiden_mapr; last exact: rename_store.
  by rewrite orestr_hiden result_of_option_omap.
- rewrite /restr_alloc /restr_eval_nat -lock /=.
  rewrite -hiden_mapr; last exact: rename_eval_nat.
  rewrite hidenT; case: (expose _)=> //= sz.
  rewrite [stateu]unlock /stateu_def /= hiden_mapr2r //=.
    by move=> s' [[ls1 h1] [ls2 h2]]; rewrite !renamepE /= !renamem_union.
  by rewrite names_newblock fdisjointC fdisjoint0.
- rewrite /restr_free -lock /= -hiden_mapr; last exact: rename_free.
  by rewrite orestr_hiden result_of_option_omap.
- by rewrite IH; case: eval_com.
- rewrite /restr_eval_cond -lock /= -hiden_mapr; last exact: rename_eval_cond.
  by rewrite hidenT; case: (expose _).
rewrite /restr_eval_cond -lock /= -hiden_mapr; last exact: rename_eval_cond.
by rewrite hidenT; case: (expose _).
Qed.

Lemma restriction_ok A (s s' : name -> state) c k :
  (eval_com restr_sem (s (fresh A)) c k = Done (s' (fresh A))) ->
  eval_com restr_sem (new A s) c k = Done (new A s').
Proof.
by move=> e; rewrite /new; rewrite eval_com_hiden e.
Qed.

Lemma restriction_error A (s : name -> state) c k :
  (eval_com restr_sem (s (fresh A)) c k = Error) ->
  eval_com restr_sem (new A s) c k = Error.
Proof.
move=> e; rewrite /new; by rewrite eval_com_hiden e.
Qed.

Lemma restriction_loop A (s : name -> state) c k :
  (eval_com restr_sem (s (fresh A)) c k = NotYet) ->
  eval_com restr_sem (new A s) c k = NotYet.
Proof.
move=> e; rewrite /new; by rewrite eval_com_hiden e.
Qed.

Lemma eval_basic_restr A s c k :
  exists A',
    eval_com restr_sem (mask A s) c k =
    match eval_com (basic_sem true) s c k with
    | Done s' => Done (mask A' s')
    | Error => Error
    | NotYet => NotYet
    end.
Proof.
elim: k A s c => /= [|k IH] A s c; first by exists fset0.
case: c => [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- by exists A; rewrite /restr_assn maprE /=; last exact: rename_assn.
- exists A; rewrite /restr_load /= maprE /= ?orestrE.
    by case: eval_expr=> //= p; case: getm.
  move=> pm s'. rewrite -rename_eval_expr.
  case: eval_expr=> //= p.
  rewrite renamemE renameK; case: getm=> //= v.
  by rewrite -renamem_set.
- exists A; rewrite /restr_store /= maprE ?orestrE.
    by case: eval_expr=> //= p; case: updm.
  move=> pm s'. rewrite -rename_eval_expr.
  case: eval_expr=> //= p.
  rewrite /updm renamemE renameK; case: getm=> //= v.
  by rewrite -rename_eval_expr -renamem_set.
- case: s=> [ls h]; rewrite (restr_allocE _ _ _ (freshP (names (ls, h)))) /=.
  case: eval_expr=> //; try by exists fset0.
  case=> [k'|] //=; rewrite /alloc_fun -lock.
  by move: (fresh _)=> i /=; exists (i |: A).
- exists A; rewrite restr_freeE /=.
  case: eval_expr=> //=; try by rewrite orestrE /=.
  by move=> p; case: ifP => // _; case: free_fun=> //=; eauto.
- by exists A.
- have [A' ->] := IH A s c1.
  case: eval_com; try by exists fset0.
  move=> s'; exact: IH.
- rewrite restr_eval_condE.
  case: eval_expr; try by exists fset0.
  by case; apply: IH.
rewrite restr_eval_condE.
case: eval_expr; try by exists fset0.
by case; apply: IH.
Qed.

Lemma mod_vars_cP s s' c x k :
  eval_com restr_sem s c k = Done s' ->
  x \notin mod_vars_c c ->
  mapr (fun st => st.1 x) s' = mapr (fun st => st.1 x) s.
Proof.
set f := fun st => st.1 x.
have eq_f : equivariant f.
  by move=> ? [??]; rewrite renamepE /= /f /= renamemE renameT.
elim: k s c s' => /= [|k IH] s c s' //.
case/(restrP fset0): s=> /= A [ls h] _ _.
case: c => [x' e|x' e|e e'|x' e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?in_fset1.
- move=> [<-].
  by rewrite restr_assnE !maprE // /f /= setmE => /negbTE ->.
- rewrite restr_loadE /=.
  case: eval_expr=> //= p.
  case: getm=> //= v [<-].
  by rewrite !maprE // /f /= setmE => /negbTE ->.
- rewrite restr_storeE /=.
  case: eval_expr=> //= p.
  case: updm=> //= h' [<-].
  by rewrite !maprE // /f /= setmE.
- rewrite (restr_allocE _ _ _ (freshP _)) /=.
  case: eval_expr=> [|[n|]| |] //= [<-].
  rewrite !maprE /f //= setmE => /negbTE ->.
  rewrite -hideE hideD // namesrE.
  case get: (ls x) => [v|] //=; last by rewrite fset0D in_fset0.
  apply: contra (freshP (names (ls, h))) => /fsetDP [i_in _].
  apply/fsetUP; left; apply/namesmP.
  by apply/@PMFreeNamesVal; eassumption.
- rewrite restr_freeE /=.
  case: eval_expr=> // p.
  case: ifP => // _.
  case: free_fun => //= h' [<-].
  by rewrite !maprE //.
- by move=> [<-] _.
- case ev1: eval_com=> [s''| |] //= ev2.
  rewrite in_fsetU => /norP [nin1 nin2].
  by rewrite -(IH _ _ _ ev1 nin1) -(IH _ _ _ ev2 nin2).
- rewrite restr_eval_condE /= in_fsetU.
  case: eval_expr=> // b ev /norP [nin1 nin2].
  by apply: IH; eauto; case: (b).
- rewrite restr_eval_condE /=.
  case: eval_expr=> // b ev nin.
  apply: IH; eauto.
  by case: (b); rewrite ?in_fset0 //= fsetUid.
Qed.

Theorem frame_ok s1 s1' s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (pub s1) (pub s2) ->
  eval_com restr_sem s1 c k = Done s1' ->
  eval_com restr_sem (s1 * s2) c k = Done (s1' * s2).
Proof.
elim: k s1 s1' c => [|k IH] //= s1 s1'.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- by move=> sub _ [<-]; rewrite restr_assn_frame.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/restr_load_frame_ok.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/restr_store_frame_ok.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/restr_alloc_ok.
- move=> sub dis /result_of_optionD ?.
  by apply/result_of_optionD/restr_free_ok.
- by move=> _ _ [<-].
- rewrite fsubUset=> /andP [sub1 sub2] dis.
  case eval_c1: eval_com=> [s1''| |] //=.
  rewrite (IH _ _ _ sub1 dis eval_c1).
  have sub2': fsubset (vars_c c2) (vars_s s1'').
    by rewrite (restr_eval_com_vars sub1 eval_c1).
  apply/(IH _ _ _ sub2').
  by apply/(fdisjoint_trans _ dis)/(restr_eval_com_pub eval_c1).
- rewrite !fsubUset -andbA=> /and3P [sub_e sub1 sub2].
  rewrite restr_eval_cond_frame //.
  case: restr_eval_cond => [b|] //= dis.
  by apply: IH=> //; case: b.
rewrite !fsubUset=> /andP [sub_e sub].
rewrite restr_eval_cond_frame //.
case: restr_eval_cond => [b|] //= dis.
apply: IH=> //; case: b=> //; last by rewrite fsub0set.
by rewrite /= fsubUset fsubUset sub sub_e.
Qed.

Theorem frame_loop s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (pub s1) (pub s2) ->
  eval_com restr_sem s1 c k = NotYet ->
  eval_com restr_sem (s1 * s2) c k = NotYet.
Proof.
elim: k s1 c => [|k IH] //= s1.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- by case: restr_load.
- by case: restr_store.
- by case: restr_alloc.
- by case: restr_free.
- rewrite fsubUset=> /andP [sub1 sub2] dis.
  case eval_c1: eval_com=> [s''| |] //=.
    rewrite (frame_ok sub1 dis eval_c1).
    apply: IH.
      by rewrite (restr_eval_com_vars sub1 eval_c1).
    by apply/(fdisjoint_trans _ dis)/(restr_eval_com_pub eval_c1).
  by rewrite (IH _ _ sub1 dis eval_c1).
- rewrite !fsubUset -andbA=> /and3P [sub_e sub1 sub2].
  rewrite restr_eval_cond_frame //.
  case: restr_eval_cond => [b|] //= dis.
  by apply: IH=> //; case: b.
rewrite !fsubUset=> /andP [sub_e sub].
rewrite restr_eval_cond_frame //.
case: restr_eval_cond => [b|] //= dis.
apply: IH=> //; case: b=> //; last by rewrite fsub0set.
by rewrite /= fsubUset fsubUset sub sub_e.
Qed.

Theorem frame_error s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (names s1) (pub s2) ->
  eval_com restr_sem s1 c k = Error ->
  eval_com restr_sem (s1 * s2) c k = Error.
Proof.
elim: k s1 c => [|k IH] //= s1.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- move=> sub dis; case Pl: restr_load=> [s1'|] //= _.
  by rewrite (restr_load_frame_error sub dis Pl).
- move=> sub dis; case Ps: restr_store=> [s1'|] //= _.
  by rewrite (restr_store_frame_error sub dis Ps).
- move=> sub dis; case Pa: restr_alloc=> [s1'|] //= _.
  by rewrite (restr_alloc_error _ sub Pa).
- move=> sub dis; case Pa: restr_free=> [s1'|] //= _.
  by rewrite (restr_free_error sub dis Pa).
- rewrite fsubUset=> /andP [sub1 sub2] dis.
  case eval_c1: eval_com=> [s1''| |] //=.
    rewrite (frame_ok sub1 _ eval_c1).
      apply: IH=> //.
      by rewrite (restr_eval_com_vars sub1 eval_c1).
    apply/(fdisjoint_trans _ dis).
    rewrite -[names s1'']/(names (Done s1'')) -eval_c1.
    apply/(@equivariant_names _ _ (fun s => eval_com restr_sem s c1 k))=> /=.
    move=> ??; exact: renaming.
    by apply/(fdisjoint_trans _ dis)/pub_names.
  by rewrite (IH _ _ sub1 dis eval_c1).
- rewrite !fsubUset -andbA=> /and3P [sub_e sub1 sub2].
  rewrite restr_eval_cond_frame //.
  case: restr_eval_cond => [b|] //= dis.
  by apply: IH=> //; case: b.
rewrite !fsubUset=> /andP [sub_e sub].
rewrite restr_eval_cond_frame //.
case: restr_eval_cond => [b|] //= dis.
apply: IH=> //; case: b=> //; last by rewrite fsub0set.
by rewrite /= fsubUset fsubUset sub sub_e.
Qed.

Corollary noninterference s1 s21 s' s22 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (names s1) (pub s21) ->
  fdisjoint (pub s1) (pub s22) ->
  eval_com restr_sem (s1 * s21) c k = Done s' ->
  exists s1',
    [/\ eval_com restr_sem s1 c k = Done s1',
        s' = s1' * s21 &
        eval_com restr_sem (s1 * s22) c k = Done (s1' * s22)].
Proof.
move=> sub dis1 dis2 eval_c.
case eval_c': (eval_com restr_sem s1 c k) => [s1'| |] //=.
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
Notation "i :-> vs" :=
  (mask fset0 (emptym, mkblock i vs) : state) (at level 20) : state_scope.
